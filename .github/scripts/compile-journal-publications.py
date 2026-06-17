#!/usr/bin/env python3
"""Compile all open GitHub issues labelled "Journal" into a markdown table.

For every open issue carrying the ``Journal`` label the script extracts:

* Year of publication (taken from a 4-digit year label, e.g. ``2026``)
* Title (the issue title)
* Link to the publication (first non-DOI URL found in the issue body)
* Journal information (the citation/"source" line of the issue body)
* DOI (if present)

The information is rendered as a markdown table sorted in descending order by
year of publication. The table is written to a file (used as a workflow
artifact), published as a GitHub Actions annotation and appended to the job
summary when running inside GitHub Actions.

The script only relies on the Python standard library so it can run on a plain
``actions/setup-python`` environment without extra dependencies.
"""

import argparse
import html
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

API_ROOT = "https://api.github.com"

# Matches a DOI such as 10.1208/s12248-026-01233-y
DOI_CORE = r"10\.\d{4,9}/[^\s\)\]\}<>\"]+"
URL_RE = re.compile(r'https?://[^\s\)\]\}<>"]+')


def gh_request(url, token):
    """Perform an authenticated GET request against the GitHub REST API."""
    request = urllib.request.Request(url)
    if token:
        request.add_header("Authorization", "Bearer " + token)
    request.add_header("Accept", "application/vnd.github+json")
    request.add_header("X-GitHub-Api-Version", "2022-11-28")
    request.add_header("User-Agent", "compile-journal-publications-script")
    with urllib.request.urlopen(request) as response:
        return json.loads(response.read().decode("utf-8"))


def fetch_journal_issues(owner, repo, token, label="Journal"):
    """Fetch *all* open issues carrying the given label (handles pagination)."""
    issues = []
    page = 1
    while True:
        params = urllib.parse.urlencode(
            {
                "labels": label,
                "state": "open",
                "per_page": 100,
                "page": page,
            }
        )
        url = f"{API_ROOT}/repos/{owner}/{repo}/issues?{params}"
        batch = gh_request(url, token)
        if not batch:
            break
        for item in batch:
            # The issues endpoint also returns pull requests; skip them.
            if "pull_request" in item:
                continue
            issues.append(item)
        if len(batch) < 100:
            break
        page += 1
    return issues


def extract_year(issue):
    """Return the publication year taken from a 4-digit year label."""
    years = [
        label["name"]
        for label in issue.get("labels", [])
        if re.fullmatch(r"\d{4}", label["name"].strip())
    ]
    if not years:
        return ""
    # In the rare case of several year labels, keep the most recent one.
    return max(years)


def clean_doi(value):
    """Normalise a raw DOI candidate by removing prefixes/trailing noise."""
    value = value.strip()
    value = re.sub(r"^(?:doi|DOI)\s*:?\s*", "", value).strip()
    # Cut at characters that cannot belong to the DOI itself.
    value = re.split(r"[\s<>\"]", value)[0]
    value = value.split("&")[0]
    value = value.rstrip(".,;:)]}>")
    return value


def extract_doi(body):
    """Extract a DOI from the issue body, preferring the most explicit form."""
    # 1) Markdown link whose text is the DOI: [10.x/y](...) or [doi: 10.x/y](...)
    match = re.search(r"\[\s*(?:doi|DOI)?\s*:?\s*(" + DOI_CORE + r")\s*\]\(", body)
    if match:
        return clean_doi(match.group(1))
    # 2) A doi.org link.
    match = re.search(r"doi\.org/(" + DOI_CORE + r")", body, re.IGNORECASE)
    if match:
        return clean_doi(match.group(1))
    # 3) An explicit "doi: 10.x/y" marker.
    match = re.search(r"(?:doi|DOI)\s*:?\s*(" + DOI_CORE + r")", body)
    if match:
        return clean_doi(match.group(1))
    # 4) Any bare DOI as a last resort.
    match = re.search(DOI_CORE, body)
    if match:
        return clean_doi(match.group(0))
    return ""


def extract_publication_url(body):
    """Return the first non-DOI URL found in the issue body."""
    fallback = ""
    for match in URL_RE.finditer(body):
        url = match.group(0).rstrip(".,);]")
        if not fallback:
            fallback = url
        if "doi.org" in url:
            continue
        return url
    return fallback


def header_lines(body):
    """Return the citation header lines (everything before the abstract)."""
    lines = []
    for raw in body.splitlines():
        line = raw.strip()
        if re.match(r"^#{1,6}\s", line) or line.lower().startswith("keywords"):
            break
        lines.append(line)
    return lines


def markdown_links_to_text(text):
    """Replace markdown links ``[label](url)`` with their label."""
    return re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)


def strip_doi_segment(text):
    """Remove a trailing DOI segment from a citation line."""
    text = re.split(r"\s*[\[\(]?\s*(?:doi|DOI)\s*:?", text)[0]
    text = re.sub(r"https?://doi\.org/\S+", "", text)
    return text.strip()


def extract_source(body, publication_url, year):
    """Best-effort extraction of the journal/citation ("source") line."""
    candidates = []
    for line in header_lines(body):
        if not line:
            continue
        # Skip lines that are essentially just the publication URL.
        without_urls = URL_RE.sub("", line).strip()
        if not without_urls:
            continue
        if publication_url and publication_url in line and len(without_urls) < 3:
            continue
        candidates.append(line)

    if not candidates:
        return ""

    def score(line):
        value = 0
        if year and year in line:
            value += 4
        # Citation-like patterns: volume(issue):page, ;number, (year), eNNN, dates.
        if re.search(r"\d+\s*\(\s*\d+\s*\)", line):
            value += 2
        if re.search(r";\s*\d+", line):
            value += 2
        if re.search(r":\s*e?\d+", line):
            value += 1
        if re.search(r"\(\s*\d{4}\s*\)", line):
            value += 2
        if re.search(
            r"\b(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\w*\b", line
        ):
            value += 1
        if "doi" in line.lower():
            value += 1
        return value

    best = max(candidates, key=score)
    source = strip_doi_segment(best)
    source = markdown_links_to_text(source)
    source = html.unescape(source)
    source = re.sub(r"\s{2,}", " ", source).strip()
    return source


def link_html(url, text):
    """Render an HTML anchor, escaping the visible text."""
    safe_url = html.escape(url, quote=True)
    safe_text = html.escape(text, quote=False)
    return f'<a href="{safe_url}">{safe_text}</a>'


def build_row(issue):
    body = issue.get("body") or ""
    year = extract_year(issue)
    title = issue.get("title", "").strip()
    issue_url = issue.get("html_url", "")
    publication_url = extract_publication_url(body)
    source = extract_source(body, publication_url, year)
    doi = extract_doi(body)

    title_cell = link_html(issue_url, title) if issue_url else html.escape(title)
    url_cell = link_html(publication_url, publication_url) if publication_url else ""
    source_cell = html.escape(source, quote=False)
    doi_cell = link_html(f"https://doi.org/{doi}", doi) if doi else ""

    return {
        "year": year,
        "year_sort": int(year) if year.isdigit() else -1,
        "title": title_cell,
        "url": url_cell,
        "source": source_cell,
        "doi": doi_cell,
    }


def build_table(issues):
    rows = [build_row(issue) for issue in issues]
    rows.sort(key=lambda r: r["year_sort"], reverse=True)

    lines = ["Year|Title|URL|Source|DOI", "-|-|-|-|-"]
    for row in rows:
        lines.append(
            "|".join(
                [row["year"], row["title"], row["url"], row["source"], row["doi"]]
            )
        )
    return "\n".join(lines)


def publish_annotation(table):
    """Emit the table as a GitHub Actions notice annotation."""
    message = (
        table.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    )
    print(f"::notice title=Journal publications table::{message}")


def write_step_summary(table):
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if not summary_path:
        return
    with open(summary_path, "a", encoding="utf-8") as handle:
        handle.write("## Journal publications\n\n")
        handle.write(table)
        handle.write("\n")


def parse_args(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default="journal-publications.md",
        help="Path of the markdown file to write (used as workflow artifact).",
    )
    parser.add_argument(
        "--repository",
        default=os.environ.get("GITHUB_REPOSITORY", ""),
        help="Repository in 'owner/repo' form (defaults to $GITHUB_REPOSITORY).",
    )
    parser.add_argument(
        "--label",
        default="Journal",
        help="Issue label to filter on (default: Journal).",
    )
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv if argv is not None else sys.argv[1:])

    if "/" not in args.repository:
        sys.exit(
            "Repository must be provided as 'owner/repo' via --repository or "
            "the GITHUB_REPOSITORY environment variable."
        )
    owner, repo = args.repository.split("/", 1)
    token = os.environ.get("GITHUB_TOKEN", "")

    try:
        issues = fetch_journal_issues(owner, repo, token, label=args.label)
    except urllib.error.HTTPError as error:
        sys.exit(f"Failed to fetch issues: {error}")

    table = build_table(issues)

    with open(args.output, "w", encoding="utf-8") as handle:
        handle.write(table)
        handle.write("\n")

    print(f"Compiled {len(issues)} '{args.label}' issues into {args.output}.")
    publish_annotation(table)
    write_step_summary(table)


if __name__ == "__main__":
    main()
