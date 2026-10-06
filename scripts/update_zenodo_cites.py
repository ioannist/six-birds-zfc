#!/usr/bin/env python3
"""Update a Zenodo deposition's Cites relations from a BibTeX file.

Dry-run is the default. To write to Zenodo, set an access token in the
environment and pass ``--apply``:

    ZENODO_ACCESS_TOKEN=... scripts/update_zenodo_cites.py \
      10.5281/zenodo.20713968 paper/closure/references.bib --apply

For already-published records, the script opens an edit session before
updating metadata. Pass ``--publish`` to publish that edited draft after
the metadata update.
"""

from __future__ import annotations

import argparse
import copy
import dataclasses
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


DOI_RE = re.compile(r"^10\.\S+/.+$", re.IGNORECASE)
DOI_URL_RE = re.compile(r"^https?://(?:dx\.)?doi\.org/", re.IGNORECASE)
ARXIV_URL_RE = re.compile(r"^https?://arxiv\.org/(?:abs|pdf)/", re.IGNORECASE)
URL_IN_TEXT_RE = re.compile(r"https?://[^\s{}<>]+")
ARXIV_ID_RE = re.compile(
    r"^(?:arxiv:)?(?:[a-z-]+(?:\.[A-Z]{2})?/\d{7}|\d{4}\.\d{4,5})(?:v\d+)?$",
    re.IGNORECASE,
)
URL_RE = re.compile(r"^https?://\S+$", re.IGNORECASE)
ISSN_RE = re.compile(r"^\d{4}-?\d{3}[\dX]$", re.IGNORECASE)
PMID_RE = re.compile(r"^\d+$")
PMCID_RE = re.compile(r"^(?:PMC)?\d+$", re.IGNORECASE)
ZENODO_DOI_RE = re.compile(r"^10\.5281/zenodo\.(?P<id>\d+)$", re.IGNORECASE)
ZENODO_RECORD_URL_RE = re.compile(
    r"^https?://(?:sandbox\.)?zenodo\.org/records?/(?P<id>\d+)(?:\D.*)?$",
    re.IGNORECASE,
)

RELATION_CITES = "cites"
ALLOWED_RELATIONS = {
    "isCitedBy",
    "cites",
    "isSupplementTo",
    "isSupplementedBy",
    "isContinuedBy",
    "continues",
    "isDescribedBy",
    "describes",
    "hasMetadata",
    "isMetadataFor",
    "isNewVersionOf",
    "isPreviousVersionOf",
    "isPartOf",
    "hasPart",
    "isReferencedBy",
    "references",
    "isDocumentedBy",
    "documents",
    "isCompiledBy",
    "compiles",
    "isVariantFormOf",
    "isOriginalFormof",
    "isIdenticalTo",
    "isAlternateIdentifier",
    "isReviewedBy",
    "reviews",
    "isDerivedFrom",
    "isSourceOf",
    "requires",
    "isRequiredBy",
    "isObsoletedBy",
    "obsoletes",
}

ENTRY_RESOURCE_TYPES = {
    "article": "publication-article",
    "book": "publication-book",
    "booklet": "publication-book",
    "inbook": "publication-section",
    "incollection": "publication-section",
    "inproceedings": "publication-conferencepaper",
    "conference": "publication-conferencepaper",
    "proceedings": "publication-conferencepaper",
    "mastersthesis": "publication-thesis",
    "phdthesis": "publication-thesis",
    "thesis": "publication-thesis",
    "techreport": "publication-report",
    "manual": "publication-technicalnote",
    "misc": "publication-preprint",
    "online": "publication-other",
    "unpublished": "publication-preprint",
}


class UserError(Exception):
    """A predictable, user-actionable problem."""


class ZenodoError(Exception):
    """HTTP-level Zenodo API failure."""

    def __init__(self, method: str, url: str, status: int, body: str) -> None:
        self.method = method
        self.url = url
        self.status = status
        self.body = body
        super().__init__(self.__str__())

    def __str__(self) -> str:
        body = self.body.strip()
        if len(body) > 1200:
            body = body[:1200] + "...<truncated>"
        return f"{self.method} {self.url} failed with HTTP {self.status}: {body}"


@dataclasses.dataclass(frozen=True)
class BibEntry:
    entry_type: str
    key: str
    fields: dict[str, str]


@dataclasses.dataclass(frozen=True)
class Citation:
    bib_key: str
    entry_type: str
    identifier: str
    identifier_source: str
    resource_type: str
    title: str

    def as_related_identifier(self) -> dict[str, str]:
        return {
            "identifier": self.identifier,
            "relation": RELATION_CITES,
            "resource_type": self.resource_type,
        }


@dataclasses.dataclass(frozen=True)
class SkippedEntry:
    bib_key: str
    reason: str


@dataclasses.dataclass(frozen=True)
class CandidateIdentifier:
    source: str
    identifier: str


@dataclasses.dataclass(frozen=True)
class CitationPlan:
    new_metadata: dict[str, Any]
    existing_related: list[dict[str, Any]]
    kept_related: list[dict[str, Any]]
    removed_cites: list[dict[str, Any]]
    unsupported_related: list[dict[str, Any]]
    added_cites: list[Citation]


class ZenodoClient:
    def __init__(self, base_url: str, token: str) -> None:
        self.base_url = base_url.rstrip("/")
        self.api_base_url = f"{self.base_url}/api"
        self.token = token

    def request(
        self,
        method: str,
        path_or_url: str,
        *,
        params: dict[str, str] | None = None,
        json_body: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        if path_or_url.startswith(("http://", "https://")):
            url = path_or_url
        else:
            url = f"{self.api_base_url}{path_or_url}"
        if params:
            url = f"{url}?{urllib.parse.urlencode(params)}"

        data = None
        headers = {
            "Accept": "application/json",
            "Authorization": f"Bearer {self.token}",
            "User-Agent": "six-birds-zenodo-cites/1.0",
        }
        if json_body is not None:
            data = json.dumps(json_body).encode("utf-8")
            headers["Content-Type"] = "application/json"

        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=60) as response:
                payload = response.read().decode("utf-8")
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", errors="replace")
            raise ZenodoError(method, url, exc.code, body) from exc
        except urllib.error.URLError as exc:
            raise UserError(f"{method} {url} failed: {exc}") from exc

        if not payload.strip():
            return {}
        try:
            parsed = json.loads(payload)
        except json.JSONDecodeError as exc:
            raise UserError(f"{method} {url} returned non-JSON response") from exc
        if not isinstance(parsed, dict):
            raise UserError(f"{method} {url} returned unexpected JSON type")
        return parsed

    def get_deposition(self, deposition_id: int) -> dict[str, Any]:
        return self.request("GET", f"/deposit/depositions/{deposition_id}")

    def get_record(self, record_id: int) -> dict[str, Any]:
        return self.request("GET", f"/records/{record_id}")

    def search_record_by_doi(self, doi: str) -> dict[str, Any] | None:
        result = self.request(
            "GET",
            "/records",
            params={"q": f'doi:"{doi}"', "size": "1", "all_versions": "true"},
        )
        hits = result.get("hits", {}).get("hits", [])
        if not hits:
            return None
        record = hits[0]
        if not isinstance(record, dict):
            return None
        return record

    def edit_deposition(self, deposition: dict[str, Any]) -> dict[str, Any]:
        deposition_id = require_int(deposition.get("id"), "deposition id")
        response = self.request("POST", f"/deposit/depositions/{deposition_id}/actions/edit")
        latest_draft_url = response.get("links", {}).get("latest_draft")
        if isinstance(latest_draft_url, str) and latest_draft_url:
            return self.request("GET", latest_draft_url)
        return self.get_deposition(deposition_id)

    def put_metadata(self, deposition_id: int, metadata: dict[str, Any]) -> dict[str, Any]:
        return self.request(
            "PUT",
            f"/deposit/depositions/{deposition_id}",
            json_body={"metadata": metadata},
        )

    def publish_deposition(self, deposition_id: int) -> dict[str, Any]:
        return self.request("POST", f"/deposit/depositions/{deposition_id}/actions/publish")


def require_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise UserError(f"Zenodo response did not include a usable {name}")
    return value


def normalize_doi(raw: str) -> str | None:
    doi = raw.strip().strip("<>").strip()
    doi = DOI_URL_RE.sub("", doi)
    doi = re.sub(r"^doi:\s*", "", doi, flags=re.IGNORECASE)
    doi = urllib.parse.unquote(doi)
    doi = doi.replace(r"\_", "_").replace(r"\/", "/")
    doi = re.sub(r"\s+", "", doi)
    doi = doi.strip(".,;")
    if not DOI_RE.match(doi):
        return None
    return doi


def strip_tex_identifier_markup(raw: str) -> str:
    value = collapse_space(raw)
    href_match = re.fullmatch(r"\\href\{([^{}]+)\}\{[^{}]*\}", value)
    if href_match:
        return href_match.group(1).strip()
    url_match = re.fullmatch(r"\\url\{([^{}]+)\}", value)
    if url_match:
        return url_match.group(1).strip()
    return value.strip().strip("{}").strip()


def split_identifier_values(raw: str) -> list[str]:
    value = strip_tex_identifier_markup(raw)
    return [part.strip() for part in re.split(r"\s*(?:;|,|\band\b)\s*", value) if part.strip()]


def normalize_arxiv(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw)
    value = ARXIV_URL_RE.sub("", value)
    value = value.removesuffix(".pdf")
    value = re.sub(r"^arxiv:\s*", "", value, flags=re.IGNORECASE)
    value = value.strip().strip(".,;")
    if not ARXIV_ID_RE.match(value):
        return None
    return f"arXiv:{value}"


def normalize_isbn(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).upper()
    value = re.sub(r"^ISBN(?:-1[03])?:\s*", "", value, flags=re.IGNORECASE)
    compact = re.sub(r"[^0-9X]", "", value)
    if len(compact) not in {10, 13}:
        return None
    return compact


def normalize_issn(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).upper()
    value = re.sub(r"^ISSN:\s*", "", value, flags=re.IGNORECASE)
    compact = re.sub(r"[^0-9X]", "", value)
    if len(compact) != 8:
        return None
    return f"{compact[:4]}-{compact[4:]}"


def normalize_pmid(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw)
    value = re.sub(r"^PMID:\s*", "", value, flags=re.IGNORECASE)
    value = value.strip().strip(".,;")
    if not PMID_RE.match(value):
        return None
    return f"PMID:{value}"


def normalize_pmcid(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw)
    value = re.sub(r"^PMCID:\s*", "", value, flags=re.IGNORECASE)
    value = value.strip().strip(".,;").upper()
    if not PMCID_RE.match(value):
        return None
    if not value.startswith("PMC"):
        value = f"PMC{value}"
    return value


def normalize_ads(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).strip().strip(".,;")
    value = re.sub(r"^ADS:\s*", "", value, flags=re.IGNORECASE)
    return value or None


def normalize_handle(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).strip().strip(".,;")
    as_url = normalize_url(value)
    if as_url and as_url.startswith("http"):
        return as_url
    value = re.sub(r"^(?:hdl|handle):\s*", "", value, flags=re.IGNORECASE)
    return f"hdl:{value}" if value else None


def normalize_ark(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).strip().strip(".,;")
    as_url = normalize_url(value)
    if as_url and as_url.startswith("http"):
        return as_url
    value = re.sub(r"^ark:\s*", "", value, flags=re.IGNORECASE)
    return f"ark:{value}" if value.startswith("/") else f"ark:/{value}" if value else None


def normalize_lsid(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).strip().strip(".,;")
    value = re.sub(r"^LSID:\s*", "", value, flags=re.IGNORECASE)
    if value.lower().startswith("urn:lsid:"):
        return value
    return f"urn:lsid:{value}" if value else None


def normalize_urn(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).strip().strip(".,;")
    if value.lower().startswith("urn:"):
        return value
    return f"urn:{value}" if value else None


def normalize_ean13(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw)
    compact = re.sub(r"[^0-9]", "", value)
    return compact if len(compact) == 13 else None


def normalize_istc(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).upper().strip().strip(".,;")
    return value or None


def normalize_url(raw: str) -> str | None:
    value = strip_tex_identifier_markup(raw).strip().strip(".,;")
    if not URL_RE.match(value):
        return None
    doi = normalize_doi(value)
    if doi is not None:
        return doi
    arxiv = normalize_arxiv(value)
    if arxiv is not None:
        return arxiv
    return value


def first_url_in_text(raw: str) -> str | None:
    match = URL_IN_TEXT_RE.search(raw)
    if not match:
        return None
    return normalize_url(match.group(0))


def candidate_identifiers(entry: BibEntry) -> list[CandidateIdentifier]:
    """Return supported Zenodo related identifiers in preference order.

    Zenodo auto-detects the identifier type from the identifier string; the API
    payload only carries ``identifier`` plus ``relation``.
    """
    candidates: list[CandidateIdentifier] = []

    doi = entry.fields.get("doi")
    if doi:
        normalized = normalize_doi(doi)
        if normalized:
            candidates.append(CandidateIdentifier("doi", normalized))

    eprint = entry.fields.get("eprint")
    archive = entry.fields.get("archiveprefix", entry.fields.get("eprinttype", ""))
    if eprint and (
        archive.lower() == "arxiv"
        or eprint.lower().startswith("arxiv:")
        or ARXIV_ID_RE.match(strip_tex_identifier_markup(eprint))
    ):
        normalized = normalize_arxiv(eprint)
        if normalized:
            candidates.append(CandidateIdentifier("arxiv", normalized))
    for field in ("arxiv", "arxivid"):
        if field in entry.fields:
            normalized = normalize_arxiv(entry.fields[field])
            if normalized:
                candidates.append(CandidateIdentifier("arxiv", normalized))

    for field, source, normalizer in (
        ("pmid", "pmid", normalize_pmid),
        ("pubmed", "pmid", normalize_pmid),
        ("pmcid", "pmcid", normalize_pmcid),
    ):
        value = entry.fields.get(field)
        if value:
            normalized = normalizer(value)
            if normalized:
                candidates.append(CandidateIdentifier(source, normalized))

    for field in ("isbn", "isbn13", "isbn10"):
        value = entry.fields.get(field)
        if value:
            for part in split_identifier_values(value):
                normalized = normalize_isbn(part)
                if normalized:
                    candidates.append(CandidateIdentifier("isbn", normalized))

    for field in ("issn", "eissn"):
        value = entry.fields.get(field)
        if value:
            for part in split_identifier_values(value):
                normalized = normalize_issn(part)
                if normalized:
                    candidates.append(CandidateIdentifier("issn", normalized))

    for field, source, normalizer in (
        ("adsbibcode", "ads", normalize_ads),
        ("bibcode", "ads", normalize_ads),
        ("handle", "handle", normalize_handle),
        ("ark", "ark", normalize_ark),
        ("purl", "purl", normalize_url),
        ("lsid", "lsid", normalize_lsid),
        ("urn", "urn", normalize_urn),
        ("ean", "ean13", normalize_ean13),
        ("ean13", "ean13", normalize_ean13),
        ("istc", "istc", normalize_istc),
    ):
        value = entry.fields.get(field)
        if value:
            normalized = normalizer(value)
            if normalized:
                candidates.append(CandidateIdentifier(source, normalized))

    for field in ("url", "howpublished", "note"):
        value = entry.fields.get(field)
        if not value:
            continue
        normalized = normalize_url(value) if field == "url" else first_url_in_text(value)
        if normalized:
            source = "doi-url" if normalize_doi(normalized) else "url"
            if normalized.startswith("arXiv:"):
                source = "arxiv-url"
            candidates.append(CandidateIdentifier(source, normalized))

    deduped: list[CandidateIdentifier] = []
    seen: set[str] = set()
    for candidate in candidates:
        canonical = canonical_identifier(candidate.identifier)
        if canonical not in seen:
            deduped.append(candidate)
            seen.add(canonical)
    return deduped


def normalize_zenodo_identifier(raw: str) -> tuple[str, int | None]:
    value = raw.strip()
    value = re.sub(r"^doi:\s*", "", value, flags=re.IGNORECASE)
    value = DOI_URL_RE.sub("", value)
    value = value.rstrip("/")
    record_url_match = ZENODO_RECORD_URL_RE.match(value)
    if record_url_match:
        record_id = int(record_url_match.group("id"))
        return f"10.5281/zenodo.{record_id}", record_id
    doi = normalize_doi(value)
    if doi is None:
        raise UserError(f"{raw!r} is not a DOI or Zenodo record URL")
    match = ZENODO_DOI_RE.match(doi)
    return doi, int(match.group("id")) if match else None


def canonical_identifier(raw: Any) -> str:
    if not isinstance(raw, str):
        return ""
    value = raw.strip()
    doi = normalize_doi(value)
    if doi is not None:
        return f"doi:{doi.lower()}"
    return re.sub(r"/+$", "", value).lower()


def relation_is_cites(value: Any) -> bool:
    return isinstance(value, str) and value.lower() == RELATION_CITES


def find_matching_delimiter(text: str, start: int, opener: str, closer: str) -> int:
    depth = 0
    in_quote = False
    escaped = False
    for index in range(start, len(text)):
        char = text[index]
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if in_quote:
            if char == '"':
                in_quote = False
            continue
        if char == '"':
            in_quote = True
            continue
        if char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
            if depth == 0:
                return index
    raise UserError("unterminated BibTeX entry")


def find_top_level_comma(text: str) -> int:
    depth = 0
    in_quote = False
    escaped = False
    for index, char in enumerate(text):
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if in_quote:
            if char == '"':
                in_quote = False
            continue
        if char == '"':
            in_quote = True
            continue
        if char in "{(":
            depth += 1
            continue
        if char in "})" and depth > 0:
            depth -= 1
            continue
        if char == "," and depth == 0:
            return index
    return -1


def read_braced_value(text: str, start: int) -> tuple[str, int]:
    depth = 1
    pieces: list[str] = []
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "{":
            depth += 1
            pieces.append(char)
        elif char == "}":
            depth -= 1
            if depth == 0:
                return "".join(pieces), index + 1
            pieces.append(char)
        else:
            pieces.append(char)
        index += 1
    raise UserError("unterminated braced BibTeX value")


def read_quoted_value(text: str, start: int) -> tuple[str, int]:
    pieces: list[str] = []
    escaped = False
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "\\" and not escaped:
            pieces.append(char)
            escaped = True
            index += 1
            continue
        if char == '"' and not escaped:
            return "".join(pieces), index + 1
        pieces.append(char)
        escaped = False
        index += 1
    raise UserError("unterminated quoted BibTeX value")


def read_bare_value(text: str, start: int) -> tuple[str, int]:
    index = start
    while index < len(text) and text[index] not in ",#":
        index += 1
    return text[start:index], index


def skip_space(text: str, index: int) -> int:
    while index < len(text) and text[index].isspace():
        index += 1
    return index


def read_value(text: str, start: int) -> tuple[str, int]:
    index = skip_space(text, start)
    if index >= len(text):
        return "", index
    if text[index] == "{":
        return read_braced_value(text, index)
    if text[index] == '"':
        return read_quoted_value(text, index)
    return read_bare_value(text, index)


def collapse_space(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def parse_fields(text: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    index = 0
    while index < len(text):
        while index < len(text) and (text[index].isspace() or text[index] == ","):
            index += 1
        if index >= len(text):
            break

        name_start = index
        while index < len(text) and text[index] != "=":
            if text[index] == ",":
                raise UserError("malformed BibTeX field before '='")
            index += 1
        if index >= len(text):
            break
        field_name = text[name_start:index].strip().lower()
        index += 1

        values: list[str] = []
        value, index = read_value(text, index)
        values.append(value)
        while True:
            index = skip_space(text, index)
            if index >= len(text) or text[index] != "#":
                break
            value, index = read_value(text, index + 1)
            values.append(value)
        fields[field_name] = collapse_space("".join(values))

        while index < len(text) and text[index] not in ",":
            if not text[index].isspace():
                break
            index += 1
    return fields


def parse_bibtex(text: str) -> list[BibEntry]:
    entries: list[BibEntry] = []
    index = 0
    while True:
        at = text.find("@", index)
        if at == -1:
            break
        type_start = at + 1
        type_end = type_start
        while type_end < len(text) and (text[type_end].isalnum() or text[type_end] in "_-"):
            type_end += 1
        entry_type = text[type_start:type_end].strip().lower()
        body_start = skip_space(text, type_end)
        if body_start >= len(text) or text[body_start] not in "{(":
            index = type_end
            continue
        opener = text[body_start]
        closer = "}" if opener == "{" else ")"
        body_end = find_matching_delimiter(text, body_start, opener, closer)
        body = text[body_start + 1 : body_end]
        index = body_end + 1

        if entry_type in {"comment", "preamble", "string"}:
            continue
        comma = find_top_level_comma(body)
        if comma == -1:
            raise UserError(f"BibTeX entry @{entry_type} has no field list")
        key = body[:comma].strip()
        if not key:
            raise UserError(f"BibTeX entry @{entry_type} has an empty key")
        fields = parse_fields(body[comma + 1 :])
        entries.append(BibEntry(entry_type=entry_type, key=key, fields=fields))
    return entries


def resource_type_for_entry(entry: BibEntry, override: str | None) -> str:
    if override:
        return override
    return ENTRY_RESOURCE_TYPES.get(entry.entry_type, "publication-other")


def extract_citations(
    entries: list[BibEntry],
    *,
    resource_type_override: str | None,
    include_secondary_identifiers: bool,
) -> tuple[list[Citation], list[SkippedEntry]]:
    citations: list[Citation] = []
    skipped: list[SkippedEntry] = []
    seen: set[str] = set()

    for entry in entries:
        identifiers = candidate_identifiers(entry)
        if not identifiers:
            skipped.append(SkippedEntry(entry.key, "no supported identifier field"))
            continue

        if not include_secondary_identifiers:
            identifiers = identifiers[:1]

        for candidate in identifiers:
            canonical = canonical_identifier(candidate.identifier)
            if canonical in seen:
                skipped.append(
                    SkippedEntry(
                        entry.key,
                        f"duplicate {candidate.source} identifier: {candidate.identifier}",
                    )
                )
                continue
            seen.add(canonical)

            citations.append(
                Citation(
                    bib_key=entry.key,
                    entry_type=entry.entry_type,
                    identifier=candidate.identifier,
                    identifier_source=candidate.source,
                    resource_type=resource_type_for_entry(entry, resource_type_override),
                    title=collapse_space(entry.fields.get("title", "")),
                )
            )

    return citations, skipped


def build_plan(
    deposition: dict[str, Any],
    citations: list[Citation],
    *,
    preserve_existing_cites: bool,
    drop_unsupported_related_identifiers: bool,
) -> CitationPlan:
    metadata = copy.deepcopy(deposition.get("metadata", {}))
    if not isinstance(metadata, dict):
        raise UserError("Zenodo response has no usable metadata object")

    raw_related = metadata.get("related_identifiers", [])
    if raw_related is None:
        raw_related = []
    if not isinstance(raw_related, list):
        raise UserError("metadata.related_identifiers is not a list")

    existing_related: list[dict[str, Any]] = []
    for item in raw_related:
        if not isinstance(item, dict):
            raise UserError("metadata.related_identifiers contains a non-object item")
        existing_related.append(copy.deepcopy(item))

    kept_related: list[dict[str, Any]] = []
    removed_cites: list[dict[str, Any]] = []
    unsupported_related: list[dict[str, Any]] = []
    allowed_relation_lowers = {relation.lower() for relation in ALLOWED_RELATIONS}

    for item in existing_related:
        relation = item.get("relation")
        relation_lower = relation.lower() if isinstance(relation, str) else ""
        if relation_lower and relation_lower not in allowed_relation_lowers:
            unsupported_related.append(item)
            if drop_unsupported_related_identifiers:
                continue

        if relation_is_cites(relation):
            if preserve_existing_cites:
                kept_related.append(item)
            else:
                removed_cites.append(item)
        else:
            kept_related.append(item)

    seen_related = {
        (str(item.get("relation", "")).lower(), canonical_identifier(item.get("identifier", "")))
        for item in kept_related
    }
    for citation in citations:
        key = (RELATION_CITES, canonical_identifier(citation.identifier))
        if key not in seen_related:
            kept_related.append(citation.as_related_identifier())
            seen_related.add(key)

    metadata["related_identifiers"] = kept_related
    return CitationPlan(
        new_metadata=metadata,
        existing_related=existing_related,
        kept_related=kept_related,
        removed_cites=removed_cites,
        unsupported_related=unsupported_related,
        added_cites=citations,
    )


def resolve_deposition(
    client: ZenodoClient,
    doi: str,
    parsed_id: int | None,
    deposition_id_override: int | None,
) -> dict[str, Any]:
    if deposition_id_override is not None:
        return client.get_deposition(deposition_id_override)

    if parsed_id is not None:
        try:
            return client.get_deposition(parsed_id)
        except ZenodoError as exc:
            if exc.status != 404:
                raise
            record = client.get_record(parsed_id)
            record_id = require_int(record.get("id"), "record id")
            return client.get_deposition(record_id)

    record = client.search_record_by_doi(doi)
    if record is None:
        raise UserError(f"could not find a Zenodo record for DOI {doi!r}")
    record_id = require_int(record.get("id"), "record id")
    return client.get_deposition(record_id)


def ensure_editable(client: ZenodoClient, deposition: dict[str, Any]) -> dict[str, Any]:
    state = deposition.get("state")
    if state == "inprogress":
        return deposition
    if deposition.get("submitted") or state == "done":
        return client.edit_deposition(deposition)
    return deposition


def read_token(token_env: str) -> str | None:
    token = os.environ.get(token_env)
    if token:
        return token
    if token_env != "ZENODO_ACCESS_TOKEN":
        return None
    return os.environ.get("ZENODO_TOKEN")


def format_related_identifier(item: dict[str, Any]) -> str:
    relation = item.get("relation", "<no relation>")
    identifier = item.get("identifier", "<no identifier>")
    resource_type = item.get("resource_type")
    suffix = f" [{resource_type}]" if resource_type else ""
    return f"{relation}: {identifier}{suffix}"


def print_citation_list(citations: list[Citation], skipped: list[SkippedEntry]) -> None:
    print(f"BibTeX citation identifiers: {len(citations)}")
    for citation in citations:
        title = f" - {citation.title}" if citation.title else ""
        print(
            f"  {citation.bib_key}: {citation.identifier} ({citation.identifier_source}) "
            f"[{citation.resource_type}]{title}"
        )
    if skipped:
        print(f"\nSkipped BibTeX entries: {len(skipped)}")
        for entry in skipped:
            print(f"  {entry.bib_key}: {entry.reason}")


def print_plan(
    deposition: dict[str, Any],
    doi: str,
    plan: CitationPlan,
    skipped: list[SkippedEntry],
    *,
    preserve_existing_cites: bool,
) -> None:
    deposition_id = deposition.get("id", "<unknown>")
    title = deposition.get("title") or deposition.get("metadata", {}).get("title", "")
    print(f"Zenodo DOI: {doi}")
    print(f"Deposition id: {deposition_id}")
    if title:
        print(f"Title: {title}")
    print(f"State: {deposition.get('state', '<unknown>')}")
    print()
    print(f"Existing related identifiers: {len(plan.existing_related)}")
    print(f"Existing non-Cites preserved: {len([r for r in plan.kept_related if not relation_is_cites(r.get('relation'))])}")
    if preserve_existing_cites:
        print("Existing Cites behavior: preserve and add missing BibTeX identifiers")
    else:
        print(f"Existing Cites to replace: {len(plan.removed_cites)}")
    print(f"BibTeX Cites to set/add: {len(plan.added_cites)}")
    print(f"Final related identifiers: {len(plan.kept_related)}")

    if plan.unsupported_related:
        print("\nUnsupported existing related identifiers:")
        for item in plan.unsupported_related:
            print(f"  {format_related_identifier(item)}")

    if plan.removed_cites:
        print("\nRemoved existing Cites:")
        for item in plan.removed_cites:
            print(f"  {format_related_identifier(item)}")

    print("\nBibTeX Cites:")
    for citation in plan.added_cites:
        title = f" - {citation.title}" if citation.title else ""
        print(
            f"  {citation.bib_key}: {citation.identifier} ({citation.identifier_source}) "
            f"[{citation.resource_type}]{title}"
        )

    if skipped:
        print(f"\nSkipped BibTeX entries: {len(skipped)}")
        for entry in skipped:
            print(f"  {entry.bib_key}: {entry.reason}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Update Zenodo related_identifiers relation=cites from a BibTeX file."
    )
    parser.add_argument("zenodo_doi", help="Zenodo DOI, DOI URL, or Zenodo record URL")
    parser.add_argument("bib_file", type=Path, help="BibTeX file to read")
    parser.add_argument(
        "--apply",
        action="store_true",
        help="write the metadata update to Zenodo; default is dry-run",
    )
    parser.add_argument(
        "--publish",
        action="store_true",
        help="publish the edited deposition after a successful update",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="only parse and print supported BibTeX citation identifiers; do not contact Zenodo",
    )
    parser.add_argument(
        "--base-url",
        default="https://zenodo.org",
        help="Zenodo base URL; use https://sandbox.zenodo.org for testing",
    )
    parser.add_argument(
        "--token-env",
        default="ZENODO_ACCESS_TOKEN",
        help="environment variable containing the Zenodo access token",
    )
    parser.add_argument(
        "--deposition-id",
        type=int,
        help="override DOI-to-deposition resolution with an explicit deposition id",
    )
    parser.add_argument(
        "--preserve-existing-cites",
        action="store_true",
        help="keep existing Cites and add missing BibTeX identifier Cites instead of replacing them",
    )
    parser.add_argument(
        "--include-secondary-identifiers",
        action="store_true",
        help="add every supported identifier found per BibTeX entry instead of only the preferred one",
    )
    parser.add_argument(
        "--resource-type",
        help="force this Zenodo resource_type for every added citation",
    )
    parser.add_argument(
        "--drop-unsupported-related-identifiers",
        action="store_true",
        help="drop existing related_identifiers whose relation is outside Zenodo's documented vocabulary",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.publish and not args.apply:
        raise UserError("--publish requires --apply")

    if not args.bib_file.exists():
        raise UserError(f"missing BibTeX file: {args.bib_file}")

    entries = parse_bibtex(args.bib_file.read_text(encoding="utf-8"))
    citations, skipped = extract_citations(
        entries,
        resource_type_override=args.resource_type,
        include_secondary_identifiers=args.include_secondary_identifiers,
    )
    if not citations:
        raise UserError("no supported BibTeX citation identifiers found")

    if args.offline:
        print_citation_list(citations, skipped)
        return 0

    doi, parsed_id = normalize_zenodo_identifier(args.zenodo_doi)
    token = read_token(args.token_env)
    if not token:
        raise UserError(
            f"set {args.token_env} with a Zenodo access token "
            "(ZENODO_TOKEN is also accepted for the default token env)"
        )

    client = ZenodoClient(args.base_url, token)
    deposition = resolve_deposition(client, doi, parsed_id, args.deposition_id)
    if args.apply:
        deposition = ensure_editable(client, deposition)

    plan = build_plan(
        deposition,
        citations,
        preserve_existing_cites=args.preserve_existing_cites,
        drop_unsupported_related_identifiers=args.drop_unsupported_related_identifiers,
    )
    print_plan(
        deposition,
        doi,
        plan,
        skipped,
        preserve_existing_cites=args.preserve_existing_cites,
    )

    if plan.unsupported_related and not args.drop_unsupported_related_identifiers:
        raise UserError(
            "existing related_identifiers include unsupported relation values; "
            "review them or rerun with --drop-unsupported-related-identifiers"
        )

    if not args.apply:
        print("\nDry run only. Rerun with --apply to update Zenodo metadata.")
        return 0

    deposition_id = require_int(deposition.get("id"), "deposition id")
    updated = client.put_metadata(deposition_id, plan.new_metadata)
    print(f"\nUpdated Zenodo metadata for deposition {updated.get('id', deposition_id)}.")

    if args.publish:
        client.publish_deposition(deposition_id)
        print(f"Published edited deposition {deposition_id}.")
    else:
        print("Edit session left unpublished. Rerun with --publish during apply to publish it.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except (UserError, ZenodoError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
