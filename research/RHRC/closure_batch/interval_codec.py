from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
import json
import math
from typing import Any


class IntervalCodecError(ValueError):
    pass


def _frac(value: str | int | Fraction | Decimal) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, Decimal):
        return Fraction(value)
    if isinstance(value, int):
        return Fraction(value, 1)
    try:
        return Fraction(str(value))
    except (ValueError, ZeroDivisionError) as exc:
        raise IntervalCodecError(f"invalid rational/decimal value: {value!r}") from exc


@dataclass(frozen=True)
class DyadicInterval:
    lo_num: int
    hi_num: int
    exp2: int

    def __post_init__(self) -> None:
        if self.exp2 < 0:
            raise IntervalCodecError("exp2 must be nonnegative")
        if self.lo_num > self.hi_num:
            raise IntervalCodecError("lower endpoint exceeds upper endpoint")

    @property
    def denominator(self) -> int:
        return 1 << self.exp2

    @property
    def lo(self) -> Fraction:
        return Fraction(self.lo_num, self.denominator)

    @property
    def hi(self) -> Fraction:
        return Fraction(self.hi_num, self.denominator)

    def contains(self, x: str | int | Fraction | Decimal) -> bool:
        q = _frac(x)
        return self.lo <= q <= self.hi

    def sign(self) -> str:
        if self.lo > 0:
            return "POSITIVE"
        if self.hi < 0:
            return "NEGATIVE"
        if self.lo == 0 and self.hi == 0:
            return "ZERO_ONLY"
        return "CONTAINS_ZERO"

    def to_json(self) -> dict[str, int]:
        return {"lo_num": self.lo_num, "hi_num": self.hi_num, "exp2": self.exp2}

    @classmethod
    def from_json(cls, obj: dict[str, Any]) -> "DyadicInterval":
        if set(obj) != {"lo_num", "hi_num", "exp2"}:
            raise IntervalCodecError("unexpected interval fields")
        return cls(int(obj["lo_num"]), int(obj["hi_num"]), int(obj["exp2"]))

    @classmethod
    def from_decimal_bounds(
        cls, lo: str | Decimal, hi: str | Decimal, *, bits: int = 192
    ) -> "DyadicInterval":
        if bits <= 0:
            raise IntervalCodecError("bits must be positive")
        qlo, qhi = _frac(lo), _frac(hi)
        if qlo > qhi:
            raise IntervalCodecError("lower endpoint exceeds upper endpoint")
        scale = 1 << bits
        lo_num = math.floor(qlo * scale)
        hi_num = math.ceil(qhi * scale)
        out = cls(lo_num, hi_num, bits)
        if not out.contains(qlo) or not out.contains(qhi):
            raise IntervalCodecError("outward rounding failed")
        return out

    @classmethod
    def from_mid_rad(
        cls, mid: str | Decimal, rad: str | Decimal, *, bits: int = 192
    ) -> "DyadicInterval":
        m, r = _frac(mid), _frac(rad)
        if r < 0:
            raise IntervalCodecError("radius must be nonnegative")
        return cls.from_decimal_bounds(m - r, m + r, bits=bits)


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"))
