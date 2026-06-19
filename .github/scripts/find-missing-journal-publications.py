#!/usr/bin/env python3
"""Find scientific articles / book chapters that mention Open Systems Pharmacology.

The script looks for publications that fulfil **all** of the following criteria:

* Published within a recent time window (the last two weeks by default).
* Mention one of the keywords ``"PK-Sim"`` or ``"Open Systems Pharmacology"``
  somewhere in an accessible part of the record (full text when available,
  otherwise title / abstract / references / other metadata).
* Are *not* already listed in ``journal-publications.md`` of this repository.
* Are *not* preprints (identified via API-level filters and URL / DOI heuristics).

Several openly accessible literature search APIs are queried (PubMed, PubMed
Central, Europe PMC, Crossref, OpenAlex, Semantic Scholar, DOAJ, CORE and
OpenAIRE). Every source is queried independently and wrapped in error handling
so that a single failing/unreachable service never aborts the whole run. The
remaining sources listed in the task (Google Scholar, Cochrane, TRIP, BASE,
Science.gov, Scilit, SciELO) do not expose a stable, key-less programmatic API
and are therefore covered indirectly: their indexed content is, to a large
extent, also discoverable through the aggregators above (OpenAlex, Europe PMC,
CORE, OpenAIRE, Crossref).

The matching publications are rendered as a markdown table with three columns
(``Year``, ``Title``, ``URL``) sorted by appearance date (newest first). The
URL favours the PubMed link when a PubMed identifier is known, otherwise it
falls back to a direct link to the article. The table is

* written to a file (used as a workflow artifact),
* published as a GitHub Actions annotation, and
* appended to the job summary

so that the surrounding workflow can additionally upload it as an artifact and
send it by e-mail.

The script only relies on the Python standard library so it can run on a plain
``actions/setup-python`` environment without extra dependencies.
"""

import argparse
import datetime as dt
import html
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

# Keywords that identify an Open Systems Pharmacology related publication.
KEYWORDS = ["PK-Sim", "Open Systems Pharmacology"]

USER_AGENT = (
    "OSP-find-missing-journal-publications/1.0 "
    "(+https://github.com/Open-Systems-Pharmacology/OSP-based-publications-and-content)"
)

# Matches a DOI such as 10.1208/s12248-026-01233-y
DOI_CORE = r"10\.\d{4,9}/[^\s\)\]\}<>\"]+"
PMID_URL_RE = re.compile(r"pubmed\.ncbi\.nlm\.nih\.gov/(\d+)")

# Preprint server URL / DOI patterns used to detect and discard preprints.
# DOI prefixes: 10.1101 = bioRxiv/medRxiv, 10.26434 = ChemRxiv,
# 10.20944 = Preprints.org, 10.21203 = Research Square,
# 10.22541 = Authorea, 10.31234 = PsyArXiv, 10.31219 = OSF Preprints.
_PREPRINT_URL_RE = re.compile(
    r"(arxiv\.org|biorxiv\.org|medrxiv\.org|ssrn\.com|"
    r"researchsquare\.com|chemrxiv\.org|preprints\.org|"
    r"authorea\.com|eartharxiv\.org|psyarxiv\.com|"
    r"osf\.io/preprints)",
    re.IGNORECASE,
)
_PREPRINT_DOI_RE = re.compile(
    r"^10\.(1101|26434|20944|21203|22541|31234|31219)/",
    re.IGNORECASE,
)
PMC_URL_RE = re.compile(r"pmc/articles/(PMC\d+)", re.IGNORECASE)


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------
def http_get(url, headers=None, retries=3, timeout=60):
    """Perform a GET request and return the decoded response body."""
    last_error = None
    for attempt in range(retries):
        request = urllib.request.Request(url)
        request.add_header("User-Agent", USER_AGENT)
        request.add_header("Accept", "application/json")
        for key, value in (headers or {}).items():
            request.add_header(key, value)
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.read().decode("utf-8", errors="replace")
        except (urllib.error.URLError, TimeoutError) as error:
            last_error = error
            # Back off briefly before retrying transient failures.
            time.sleep(1.5 * (attempt + 1))
    raise last_error if last_error else RuntimeError("request failed")


def http_get_json(url, headers=None, retries=3, timeout=60):
    """GET a URL and decode the response as JSON."""
    return json.loads(http_get(url, headers=headers, retries=retries, timeout=timeout))


def normalise_title(title):
    """Return a comparison key for a title (lowercase alphanumerics only)."""
    return re.sub(r"[^a-z0-9]+", "", clean_text(title).lower())


def normalise_doi(doi):
    """Return a normalised DOI (lowercase, no resolver prefix)."""
    if not doi:
        return ""
    doi = doi.strip()
    doi = re.sub(r"^https?://(dx\.)?doi\.org/", "", doi, flags=re.IGNORECASE)
    doi = re.sub(r"^doi\s*:?\s*", "", doi, flags=re.IGNORECASE)
    return doi.rstrip(".,;:)]}>").lower()


def keyword_in_text(text):
    """Return True if one of the keywords appears in the given text."""
    if not text:
        return False
    lowered = text.lower()
    return any(keyword.lower() in lowered for keyword in KEYWORDS)


def clean_text(text):
    """Remove simple HTML markup and normalise whitespace in source text."""
    text = html.unescape(text or "")
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"\s*-\s*", "-", text)
    return re.sub(r"\s+", " ", text).strip()


def reconstruct_abstract(inverted_index):
    """Rebuild an abstract string from an OpenAlex inverted index."""
    if not inverted_index:
        return ""
    positions = []
    for word, indices in inverted_index.items():
        for index in indices:
            positions.append((index, word))
    positions.sort()
    return " ".join(word for _, word in positions)


# Sources whose query already performs an exact keyword/phrase match (in title,
# abstract and, where available, full text). Their hits are trusted as-is.
# Hits from any other source are additionally verified against the keywords in
# the title/abstract to discard loose, tokenised matches.
TRUSTED_SOURCES = {"pubmed", "pmc", "europepmc"}


def is_keyword_verified(record):
    """Return True if the record reliably matches one of the keywords."""
    if record["source"] in TRUSTED_SOURCES:
        return True
    return keyword_in_text(record["title"] + " " + record.get("abstract", ""))


def is_preprint(record):
    """Return True if the record appears to be a preprint.

    Detection is based on three independent signals (any one is sufficient):
    * The URL points to a known preprint server.
    * The DOI prefix belongs to a preprint platform.
    * The title carries an explicit ``[Preprint]`` marker.
    """
    url = record.get("url", "") or ""
    if _PREPRINT_URL_RE.search(url):
        return True
    doi = record.get("doi", "") or ""
    if _PREPRINT_DOI_RE.match(doi):
        return True
    title = record.get("title", "") or ""
    if re.search(r"\bpreprint\b", title, re.IGNORECASE):
        return True
    return False


# ---------------------------------------------------------------------------
# Existing publications (exclusion list)
# ---------------------------------------------------------------------------
def load_existing_publications(path):
    """Parse ``journal-publications.md`` into sets of known identifiers."""
    pmids, dois, titles = set(), set(), set()
    if not path or not os.path.exists(path):
        return pmids, dois, titles

    with open(path, "r", encoding="utf-8") as handle:
        content = handle.read()

    for match in PMID_URL_RE.finditer(content):
        pmids.add(match.group(1))
    for match in re.finditer(r"doi\.org/(" + DOI_CORE + r")", content, re.IGNORECASE):
        dois.add(normalise_doi(match.group(1)))

    # Titles live inside the first anchor of every table row (the GitHub issue
    # link). Capture the anchor text to compare against candidate titles.
    for match in re.finditer(r"issues/\d+\">(.*?)</a>", content, re.DOTALL):
        title = clean_text(match.group(1))
        if title:
            titles.add(normalise_title(title))

    return pmids, dois, titles


# ---------------------------------------------------------------------------
# Candidate record handling
# ---------------------------------------------------------------------------
def make_record(title, date, year, pmid="", doi="", url="", source="", abstract=""):
    """Build a normalised candidate record."""
    date_obj = parse_date(date)
    if not year and date_obj:
        year = str(date_obj.year)
    return {
        "title": clean_text(title),
        "date": date_obj,
        "year": str(year or "").strip(),
        "pmid": str(pmid or "").strip(),
        "doi": normalise_doi(doi),
        "url": (url or "").strip(),
        "source": source,
        "abstract": clean_text(abstract),
    }


def parse_date(value):
    """Parse a variety of date encodings into a ``date`` object (or None)."""
    if not value:
        return None
    if isinstance(value, dt.date):
        return value
    value = str(value).strip()
    # Normalise common separators to a single space first.
    candidates = [value, value.split("T")[0]]
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%Y %m %d", "%Y-%m", "%Y/%m", "%Y"):
        for candidate in candidates:
            try:
                return dt.datetime.strptime(candidate, fmt).date()
            except ValueError:
                continue
    # Fall back to a leading 4-digit year.
    match = re.match(r"(\d{4})", value)
    if match:
        try:
            return dt.date(int(match.group(1)), 1, 1)
        except ValueError:
            return None
    return None


def final_url(record):
    """Return the preferred URL, favouring the PubMed link."""
    if record["pmid"]:
        return f"https://pubmed.ncbi.nlm.nih.gov/{record['pmid']}/"
    if record["url"]:
        return record["url"]
    if record["doi"]:
        return f"https://doi.org/{record['doi']}"
    return ""


# ---------------------------------------------------------------------------
# Source: PubMed (and PubMed Central) via NCBI E-utilities
# ---------------------------------------------------------------------------
EUTILS = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils"


def _eutils_extra():
    """Optional NCBI tool/email parameters (improves rate limits)."""
    params = {"tool": "osp-find-missing-journal-publications"}
    email = os.environ.get("NCBI_EMAIL")
    if email:
        params["email"] = email
    api_key = os.environ.get("NCBI_API_KEY")
    if api_key:
        params["api_key"] = api_key
    return params


def search_pubmed(days, db="pubmed"):
    """Search PubMed / PMC for the keywords within the recent time window."""
    term = (
        "(" + " OR ".join(f'"{keyword}"' for keyword in KEYWORDS) + ")"
        + ' NOT "Preprint"[pt]'
    )
    params = {
        "db": db,
        "term": term,
        "retmax": "200",
        "retmode": "json",
        "datetype": "pdat",
        "reldate": str(days),
        "sort": "pub_date",
    }
    params.update(_eutils_extra())
    url = f"{EUTILS}/esearch.fcgi?" + urllib.parse.urlencode(params)
    data = http_get_json(url)
    idlist = data.get("esearchresult", {}).get("idlist", [])
    if not idlist:
        return []

    summary_params = {
        "db": db,
        "id": ",".join(idlist),
        "retmode": "json",
    }
    summary_params.update(_eutils_extra())
    summary_url = f"{EUTILS}/esummary.fcgi?" + urllib.parse.urlencode(summary_params)
    summary = http_get_json(summary_url)
    result = summary.get("result", {})

    records = []
    for uid in result.get("uids", []):
        item = result.get(uid, {})
        title = item.get("title", "")
        date = item.get("sortpubdate") or item.get("pubdate") or item.get("epubdate")
        doi = ""
        pmid = uid if db == "pubmed" else ""
        for article_id in item.get("articleids", []):
            id_type = article_id.get("idtype", "").lower()
            if id_type == "doi":
                doi = article_id.get("value", "")
            elif id_type == "pubmed" and not pmid:
                pmid = article_id.get("value", "")
        url = ""
        if db == "pmc":
            url = f"https://pmc.ncbi.nlm.nih.gov/articles/{uid}/"
        records.append(
            make_record(title, date, "", pmid=pmid, doi=doi, url=url, source=db)
        )
    return records


# ---------------------------------------------------------------------------
# Source: Europe PMC (covers full-text search across PMC content)
# ---------------------------------------------------------------------------
def search_europepmc(days):
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    keyword_query = " OR ".join(f'"{keyword}"' for keyword in KEYWORDS)
    query = (
        f"({keyword_query}) AND "
        f"(FIRST_PDATE:[{start.isoformat()} TO {today.isoformat()}])"
        f" NOT (SRC:PPR)"
    )
    params = {
        "query": query,
        "format": "json",
        "pageSize": "200",
        "resultType": "core",
        "sort": "FIRST_PDATE_D desc",
    }
    url = (
        "https://www.ebi.ac.uk/europepmc/webservices/rest/search?"
        + urllib.parse.urlencode(params)
    )
    data = http_get_json(url)
    records = []
    for item in data.get("resultList", {}).get("result", []):
        title = item.get("title", "")
        date = item.get("firstPublicationDate") or item.get("pubYear")
        pmid = item.get("pmid", "")
        doi = item.get("doi", "")
        url_direct = ""
        if item.get("fullTextUrlList"):
            urls = item["fullTextUrlList"].get("fullTextUrl", [])
            if urls:
                url_direct = urls[0].get("url", "")
        records.append(
            make_record(
                title, date, item.get("pubYear", ""),
                pmid=pmid, doi=doi, url=url_direct, source="europepmc",
            )
        )
    return records


# ---------------------------------------------------------------------------
# Source: Crossref
# ---------------------------------------------------------------------------
def search_crossref(days):
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    params = {
        "query": " ".join(KEYWORDS),
        "filter": f"from-pub-date:{start.isoformat()},until-pub-date:{today.isoformat()}",
        "rows": "100",
        "sort": "published",
        "order": "desc",
        "select": "title,DOI,type,issued,published,published-online,published-print",
    }
    mailto = os.environ.get("CROSSREF_MAILTO")
    if mailto:
        params["mailto"] = mailto
    url = "https://api.crossref.org/works?" + urllib.parse.urlencode(params)
    data = http_get_json(url)
    records = []
    for item in data.get("message", {}).get("items", []):
        # Crossref type "posted-content" covers preprints (bioRxiv, medRxiv, etc.).
        if item.get("type") == "posted-content":
            continue
        titles = item.get("title") or []
        title = titles[0] if titles else ""
        if not keyword_in_text(title):
            # Crossref does not index full text; keep only metadata matches so
            # that unrelated articles published in the window are excluded.
            continue
        doi = item.get("DOI", "")
        date_parts = None
        for key in ("published", "published-online", "published-print", "issued"):
            block = item.get(key) or {}
            if block.get("date-parts") and block["date-parts"][0]:
                date_parts = block["date-parts"][0]
                break
        date = "-".join(f"{part:02d}" if i else str(part)
                        for i, part in enumerate(date_parts)) if date_parts else ""
        records.append(make_record(title, date, "", doi=doi, source="crossref"))
    return records


# ---------------------------------------------------------------------------
# Source: OpenAlex (default search covers title, abstract and full text)
# ---------------------------------------------------------------------------
def search_openalex(days):
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    records = []
    for keyword in KEYWORDS:
        params = {
            "search": keyword,
            "filter": (
                f"from_publication_date:{start.isoformat()},"
                f"to_publication_date:{today.isoformat()},"
                f"type:!preprint"
            ),
            "per-page": "100",
            "select": "display_name,publication_date,publication_year,doi,ids,abstract_inverted_index",
            "sort": "publication_date:desc",
        }
        mailto = os.environ.get("OPENALEX_MAILTO")
        if mailto:
            params["mailto"] = mailto
        url = "https://api.openalex.org/works?" + urllib.parse.urlencode(params)
        try:
            data = http_get_json(url)
        except (urllib.error.URLError, ValueError):
            continue
        for item in data.get("results", []):
            title = item.get("display_name", "")
            date = item.get("publication_date") or item.get("publication_year")
            doi = item.get("doi", "")
            ids = item.get("ids", {}) or {}
            pmid = ""
            if ids.get("pmid"):
                match = re.search(r"(\d+)$", ids["pmid"])
                pmid = match.group(1) if match else ""
            abstract = reconstruct_abstract(item.get("abstract_inverted_index"))
            records.append(
                make_record(
                    title, date, item.get("publication_year", ""),
                    pmid=pmid, doi=doi, url=ids.get("openalex", ""),
                    source="openalex", abstract=abstract,
                )
            )
    return records


# ---------------------------------------------------------------------------
# Source: Semantic Scholar
# ---------------------------------------------------------------------------
def search_semanticscholar(days):
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    params = {
        "query": " ".join(KEYWORDS),
        "limit": "100",
        "fields": "title,year,publicationDate,publicationTypes,externalIds,abstract",
        "publicationDateOrYear": f"{start.isoformat()}:{today.isoformat()}",
    }
    url = (
        "https://api.semanticscholar.org/graph/v1/paper/search?"
        + urllib.parse.urlencode(params)
    )
    headers = {}
    api_key = os.environ.get("SEMANTIC_SCHOLAR_API_KEY")
    if api_key:
        headers["x-api-key"] = api_key
    data = http_get_json(url, headers=headers)
    records = []
    for item in data.get("data", []) or []:
        pub_types = [t.lower() for t in (item.get("publicationTypes") or [])]
        if "preprint" in pub_types:
            continue
        title = item.get("title", "")
        date = item.get("publicationDate") or item.get("year")
        external = item.get("externalIds", {}) or {}
        records.append(
            make_record(
                title, date, item.get("year", ""),
                pmid=str(external.get("PubMed", "") or ""),
                doi=external.get("DOI", ""),
                source="semanticscholar",
                abstract=item.get("abstract", "") or "",
            )
        )
    return records


# ---------------------------------------------------------------------------
# Source: Directory of Open Access Journals (DOAJ)
# ---------------------------------------------------------------------------
def search_doaj(days):
    records = []
    for keyword in KEYWORDS:
        query = urllib.parse.quote(f'"{keyword}"')
        url = (
            f"https://doaj.org/api/search/articles/{query}"
            "?pageSize=100&sort=created_date:desc"
        )
        try:
            data = http_get_json(url)
        except (urllib.error.URLError, ValueError):
            continue
        for item in data.get("results", []):
            bibjson = item.get("bibjson", {})
            title = bibjson.get("title", "")
            year = bibjson.get("year", "")
            month = bibjson.get("month", "")
            date = f"{year}-{int(month):02d}" if year and str(month).isdigit() else year
            doi, pmid, link = "", "", ""
            for identifier in bibjson.get("identifier", []):
                id_type = identifier.get("type", "").lower()
                if id_type == "doi":
                    doi = identifier.get("id", "")
                elif id_type == "pmid":
                    pmid = identifier.get("id", "")
            for link_item in bibjson.get("link", []):
                if link_item.get("url"):
                    link = link_item["url"]
                    break
            records.append(
                make_record(title, date, year, pmid=pmid, doi=doi, url=link,
                            source="doaj", abstract=bibjson.get("abstract", ""))
            )
    return records


# ---------------------------------------------------------------------------
# Source: CORE (requires an API key; skipped when not configured)
# ---------------------------------------------------------------------------
def search_core(days):
    api_key = os.environ.get("CORE_API_KEY")
    if not api_key:
        return []
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    keyword_query = " OR ".join(f'"{keyword}"' for keyword in KEYWORDS)
    query = (
        f"({keyword_query}) AND createdDate>={start.isoformat()}"
    )
    params = {"q": query, "limit": "100"}
    url = "https://api.core.ac.uk/v3/search/works?" + urllib.parse.urlencode(params)
    data = http_get_json(url, headers={"Authorization": "Bearer " + api_key})
    records = []
    for item in data.get("results", []):
        title = item.get("title", "")
        date = item.get("publishedDate") or item.get("createdDate") or item.get("yearPublished")
        doi = item.get("doi", "")
        link = ""
        if item.get("links"):
            for link_item in item["links"]:
                if link_item.get("type") == "display" and link_item.get("url"):
                    link = link_item["url"]
                    break
        records.append(
            make_record(title, date, item.get("yearPublished", ""),
                        doi=doi, url=link, source="core")
        )
    return records


# ---------------------------------------------------------------------------
# Source: OpenAIRE
# ---------------------------------------------------------------------------
def search_openaire(days):
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    records = []
    for keyword in KEYWORDS:
        params = {
            "keywords": keyword,
            "fromDateAccepted": start.isoformat(),
            "toDateAccepted": today.isoformat(),
            "size": "100",
            "format": "json",
        }
        url = "https://api.openaire.eu/search/publications?" + urllib.parse.urlencode(params)
        try:
            data = http_get_json(url)
        except (urllib.error.URLError, ValueError):
            continue
        response = data.get("response") or {}
        results_block = response.get("results") or {}
        results = results_block.get("result") or []
        if isinstance(results, dict):
            results = [results]
        for entry in results:
            try:
                metadata = entry["metadata"]["oaf:entity"]["oaf:result"]
            except (KeyError, TypeError):
                continue
            title = metadata.get("title")
            if isinstance(title, list):
                title = title[0]
            if isinstance(title, dict):
                title = title.get("content") or title.get("$", "")
            date = metadata.get("dateofacceptance")
            if isinstance(date, dict):
                date = date.get("$", "")
            doi = ""
            pids = metadata.get("pid", [])
            if isinstance(pids, dict):
                pids = [pids]
            for pid in pids:
                if isinstance(pid, dict) and pid.get("@classid") == "doi":
                    doi = pid.get("$", "")
            description = metadata.get("description", "")
            if isinstance(description, list):
                description = description[0] if description else ""
            if isinstance(description, dict):
                description = description.get("$", "")
            records.append(
                make_record(title, date, "", doi=doi, source="openaire",
                            abstract=description or "")
            )
    return records


SOURCES = [
    ("PubMed", lambda days: search_pubmed(days, db="pubmed")),
    ("PubMed Central", lambda days: search_pubmed(days, db="pmc")),
    ("Europe PMC", search_europepmc),
    ("Crossref", search_crossref),
    ("OpenAlex", search_openalex),
    ("Semantic Scholar", search_semanticscholar),
    ("DOAJ", search_doaj),
    ("CORE", search_core),
    ("OpenAIRE", search_openaire),
]


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------
def collect_candidates(days):
    """Query every source and return the combined list of records."""
    records = []
    for name, func in SOURCES:
        try:
            found = func(days)
            print(f"  {name}: {len(found)} record(s)")
            records.extend(found)
        except Exception as error:  # noqa: BLE001 - keep going on any failure
            print(f"  {name}: skipped ({error.__class__.__name__}: {error})")
    return records


def is_recent(record, days):
    """Keep records whose known date lies within the time window."""
    if record["date"] is None:
        # No precise date available: trust the source's own date filtering.
        return True
    today = dt.date.today()
    start = today - dt.timedelta(days=days)
    return start <= record["date"] <= today


def deduplicate(records):
    """Merge records that refer to the same publication.

    Two records are considered the same publication when they share *any* of
    their identifiers (PMID, DOI or normalised title). Records are processed in
    order and merged into the first matching group so that information coming
    from different sources is combined.
    """
    groups = []
    index = {}  # identifier key -> group dict

    def keys_for(record):
        keys = []
        if record["pmid"]:
            keys.append(("pmid", record["pmid"]))
        if record["doi"]:
            keys.append(("doi", record["doi"]))
        if record["title"]:
            keys.append(("title", normalise_title(record["title"])))
        return keys

    def merge_into(target, record):
        if not target["pmid"] and record["pmid"]:
            target["pmid"] = record["pmid"]
        if not target["doi"] and record["doi"]:
            target["doi"] = record["doi"]
        if not target["url"] and record["url"]:
            target["url"] = record["url"]
        if target["date"] is None and record["date"] is not None:
            target["date"] = record["date"]
        if not target["year"] and record["year"]:
            target["year"] = record["year"]

    for record in records:
        keys = keys_for(record)
        if not keys:
            continue
        existing = None
        for key in keys:
            if key in index:
                existing = index[key]
                break
        if existing is None:
            groups.append(record)
            for key in keys:
                index[key] = record
        else:
            merge_into(existing, record)
            # Register any newly learned identifiers for the merged record.
            for key in keys_for(existing):
                index.setdefault(key, existing)
    return groups


def is_known(record, pmids, dois, titles):
    """Return True if the record is already listed in journal-publications.md."""
    if record["pmid"] and record["pmid"] in pmids:
        return True
    if record["doi"] and record["doi"] in dois:
        return True
    if record["title"] and normalise_title(record["title"]) in titles:
        return True
    return False


def sort_key(record):
    """Sort by appearance date (newest first); undated records go last."""
    if record["date"] is not None:
        return (record["date"].toordinal(), record["year"] or "")
    year = int(record["year"]) if record["year"].isdigit() else 0
    return (dt.date(year, 1, 1).toordinal() if year else 0, record["year"])


# ---------------------------------------------------------------------------
# Output rendering
# ---------------------------------------------------------------------------
def md_escape(text):
    """Escape characters that would break a markdown table cell."""
    return (text or "").replace("|", "\\|").replace("\n", " ").strip()


def build_table(records):
    lines = ["| Year | Title | URL |", "| --- | --- | --- |"]
    for record in records:
        url = final_url(record)
        title = md_escape(record["title"]) or "(no title)"
        url_cell = f"[{url}]({url})" if url else ""
        year = md_escape(record["year"])
        lines.append(f"| {year} | {title} | {url_cell} |")
    return "\n".join(lines)


def publish_annotation(table, count):
    message = table.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    print(
        f"::notice title=Missing journal publications ({count})::{message}"
    )


def write_step_summary(table, count):
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if not summary_path:
        return
    with open(summary_path, "a", encoding="utf-8") as handle:
        handle.write(f"## Missing journal publications ({count})\n\n")
        handle.write(table)
        handle.write("\n")


def write_github_output(count):
    output_path = os.environ.get("GITHUB_OUTPUT")
    if not output_path:
        return
    with open(output_path, "a", encoding="utf-8") as handle:
        handle.write(f"count={count}\n")
        handle.write(f"has_results={'true' if count else 'false'}\n")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------
def parse_args(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default="find-missing-journal-publications.md",
        help="Path of the markdown file to write (used as workflow artifact).",
    )
    parser.add_argument(
        "--existing",
        default="journal-publications.md",
        help="Path to the markdown file listing already-known publications.",
    )
    parser.add_argument(
        "--days",
        type=int,
        default=14,
        help="Size of the look-back window in days (default: 14, i.e. 2 weeks).",
    )
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv if argv is not None else sys.argv[1:])

    pmids, dois, titles = load_existing_publications(args.existing)
    print(
        f"Loaded {len(pmids)} PMIDs, {len(dois)} DOIs and {len(titles)} titles "
        f"from {args.existing}."
    )

    print(f"Searching sources for the last {args.days} day(s)...")
    candidates = collect_candidates(args.days)

    candidates = [record for record in candidates if record["title"]]
    candidates = [record for record in candidates if is_keyword_verified(record)]
    candidates = [record for record in candidates if is_recent(record, args.days)]
    candidates = deduplicate(candidates)
    candidates = [record for record in candidates if not is_preprint(record)]
    candidates = [
        record for record in candidates if not is_known(record, pmids, dois, titles)
    ]
    candidates.sort(key=sort_key, reverse=True)

    table = build_table(candidates)
    count = len(candidates)

    with open(args.output, "w", encoding="utf-8") as handle:
        handle.write(f"# Missing journal publications ({count})\n\n")
        if count:
            handle.write(table)
        else:
            handle.write(
                "No new matching publications were found in the search window."
            )
        handle.write("\n")

    print(f"Found {count} missing publication(s); written to {args.output}.")
    publish_annotation(table, count)
    write_step_summary(table, count)
    write_github_output(count)


if __name__ == "__main__":
    main()
