from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json


def _canonical_json(value) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


@dataclass(frozen=True)
class HistoricalClue:
    concept_id: str
    term: str
    source_family: str
    source_version: str | None
    source_path: str
    source_commit: str | None
    line_number: int | None
    excerpt: str
    authority: str
    requires_revalidation: bool = True

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass(frozen=True)
class RetroSearchReceipt:
    concept_id: str
    terms: tuple[str, ...]
    mode: str
    as_of_ref: str | None
    search_scope: str
    search_complete: bool
    searched_sources: tuple[str, ...]
    search_paths: tuple[str, ...]
    hits: tuple[HistoricalClue, ...]

    @property
    def receipt_id(self) -> str:
        # The id hashes the canonical JSON of the whole receipt. An exhaustive
        # all-ref search can hold millions of hits, and one JSON string of all
        # of them (plus its UTF-8 copy) exhausts a CI runner, so the same
        # bytes are fed to the hash one hit at a time.
        payload = {
            "concept_id": self.concept_id,
            "terms": self.terms,
            "mode": self.mode,
            "as_of_ref": self.as_of_ref,
            "search_scope": self.search_scope,
            "search_complete": self.search_complete,
            "searched_sources": self.searched_sources,
            "search_paths": self.search_paths,
            "hits": [],
        }
        # Inside a JSON string every quote is escaped, so the only unescaped
        # '"hits":[]' is the key itself.
        head, _, tail = _canonical_json(payload).partition('"hits":[]')
        digest = hashlib.sha256((head + '"hits":[').encode("utf-8"))
        for i, hit in enumerate(self.hits):
            if i:
                digest.update(b",")
            digest.update(_canonical_json(hit.to_dict()).encode("utf-8"))
        digest.update(("]" + tail).encode("utf-8"))
        return "RETRO-" + digest.hexdigest()[:20]

    def to_dict(self) -> dict:
        return {
            "receipt_id": self.receipt_id,
            "concept_id": self.concept_id,
            "terms": list(self.terms),
            "mode": self.mode,
            "as_of_ref": self.as_of_ref,
            "search_scope": self.search_scope,
            "search_complete": self.search_complete,
            "searched_sources": list(self.searched_sources),
            "search_paths": list(self.search_paths),
            "hits": [h.to_dict() for h in self.hits],
        }
