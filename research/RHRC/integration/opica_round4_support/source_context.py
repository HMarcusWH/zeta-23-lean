"""Strict source-context comparison; matching metadata is NOT a Lean proof."""
from __future__ import annotations
from dataclasses import asdict, dataclass, fields
import hashlib
import json
import re

HEX40 = re.compile(r"[0-9a-f]{40}\Z", re.ASCII)
PARITIES = frozenset({"even", "odd", "both", "none"})

@dataclass(frozen=True)
class SourceContext:
    commit: str
    source_blob: str
    source_object: str
    carrier: str
    parity: str
    normalization: str
    witness_kind: str
    aperture: str
    cutoff: str
    spectral_domain: str
    quantifiers: tuple[str, ...]

    def __post_init__(self) -> None:
        for name in ("commit", "source_blob"):
            raw = getattr(self, name)
            if type(raw) is not str or HEX40.fullmatch(raw) is None:
                raise ValueError(f"{name} must be an exact lowercase Git SHA1")
        for field in fields(self):
            if field.name in {"commit", "source_blob", "quantifiers"}:
                continue
            raw = getattr(self, field.name)
            if type(raw) is not str or not raw or raw != raw.strip():
                raise ValueError(f"invalid nonempty normalized metadata: {field.name}")
            if any(ord(char) < 32 for char in raw):
                raise ValueError(f"control character in {field.name}")
        if self.parity not in PARITIES:
            raise ValueError("invalid parity")
        if type(self.quantifiers) is not tuple or not self.quantifiers:
            raise ValueError("quantifiers must be an ordered, nonempty tuple")
        if any(type(q) is not str or not q or q != q.strip() for q in self.quantifiers):
            raise ValueError("invalid quantifier")

    def fingerprint(self) -> str:
        text = json.dumps(asdict(self), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        return hashlib.sha256(text.encode("utf-8")).hexdigest()

def context_differences(left: SourceContext, right: SourceContext) -> tuple[str, ...]:
    if not isinstance(left, SourceContext) or not isinstance(right, SourceContext):
        raise TypeError("expected SourceContext objects")
    return tuple(field.name for field in fields(left)
                 if getattr(left, field.name) != getattr(right, field.name))


def require_identical_context(left: SourceContext, right: SourceContext) -> None:
    """Conservative consistency guard, not a proof that the bound values coincide."""
    differences = context_differences(left, right)
    if differences:
        raise ValueError(f"context mismatch needs a proved adapter: {differences!r}")
