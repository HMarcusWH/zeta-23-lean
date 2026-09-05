from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json


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
    searched_sources: tuple[str, ...]
    hits: tuple[HistoricalClue, ...]

    @property
    def receipt_id(self) -> str:
        payload = {
            "concept_id": self.concept_id,
            "terms": self.terms,
            "mode": self.mode,
            "as_of_ref": self.as_of_ref,
            "searched_sources": self.searched_sources,
            "hits": [h.to_dict() for h in self.hits],
        }
        raw = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        return "RETRO-" + hashlib.sha256(raw).hexdigest()[:20]

    def to_dict(self) -> dict:
        return {
            "receipt_id": self.receipt_id,
            "concept_id": self.concept_id,
            "terms": list(self.terms),
            "mode": self.mode,
            "as_of_ref": self.as_of_ref,
            "searched_sources": list(self.searched_sources),
            "hits": [h.to_dict() for h in self.hits],
        }
