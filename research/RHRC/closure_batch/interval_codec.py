from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
import json
import math
from typing import Any


class IntervalCodecError(ValueError):
    pass


MAX_EXP2 = 1_000_000


def _strict_int(value: Any, label: str) -> int:
    if isinstance(value, bool):
        raise IntervalCodecError(f"{label} must be an integer, not bool")
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        s = value.strip()
        if not s or (s[0] in "+-" and not s[1:].isdigit()) or (
            s[0] not in "+-" and not s.isdigit()
        ):
            raise IntervalCodecError(f"{label} is not a canonical integer")
        return int(s)
    raise IntervalCodecError(f"{label} must be an integer")


def _frac(value: str | int | Fraction | Decimal) -> Fraction:
    if isinstance(value, bool):
        raise IntervalCodecError("boolean is not a rational value")
    if isinstance(value, Fraction):
        return value
    if isinstance(value, Decimal):
        if not value.is_finite():
            raise IntervalCodecError("nonfinite decimal")
        return Fraction(value)
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, str):
        s = value.strip()
        if s.lower() in {"nan", "+nan", "-nan", "inf", "+inf", "-inf",
                         "infinity", "+infinity", "-infinity"}:
            raise IntervalCodecError("nonfinite rational/decimal value")
        try:
            return Fraction(s)
        except (ValueError, ZeroDivisionError) as exc:
            raise IntervalCodecError(f"invalid rational/decimal value: {value!r}") from exc
    raise IntervalCodecError(f"unsupported rational value: {type(value).__name__}")


def _is_power_of_two(n: int) -> bool:
    return n > 0 and n & (n - 1) == 0


def _fraction_from_man_exp(value: Any) -> Fraction:
    """Decode a finite python-flint exact endpoint without decimal rounding."""
    try:
        man, exp = value.man_exp()
    except Exception as exc:  # python-flint raises domain/value errors by version
        raise IntervalCodecError("Arb endpoint does not expose a finite man_exp") from exc
    m = int(man)
    e = int(exp)
    if e >= 0:
        return Fraction(m * (1 << e), 1)
    return Fraction(m, 1 << (-e))


@dataclass(frozen=True)
class DyadicInterval:
    lo_num: int
    hi_num: int
    exp2: int

    def __post_init__(self) -> None:
        if isinstance(self.lo_num, bool) or isinstance(self.hi_num, bool) or isinstance(self.exp2, bool):
            raise IntervalCodecError("boolean interval field")
        if not all(isinstance(x, int) for x in (self.lo_num, self.hi_num, self.exp2)):
            raise IntervalCodecError("interval fields must be integers")
        if self.exp2 < 0 or self.exp2 > MAX_EXP2:
            raise IntervalCodecError("exp2 outside resource-safe range")
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

    def contains_interval(self, other: "DyadicInterval") -> bool:
        return self.lo <= other.lo and other.hi <= self.hi

    def sign(self) -> str:
        if self.lo > 0:
            return "POSITIVE"
        if self.hi < 0:
            return "NEGATIVE"
        if self.lo == 0 and self.hi == 0:
            return "ZERO_ONLY"
        return "CONTAINS_ZERO"

    def width(self) -> Fraction:
        return self.hi - self.lo

    def to_json(self) -> dict[str, int]:
        return {"lo_num": self.lo_num, "hi_num": self.hi_num, "exp2": self.exp2}

    @classmethod
    def from_json(cls, obj: dict[str, Any]) -> "DyadicInterval":
        if not isinstance(obj, dict) or set(obj) != {"lo_num", "hi_num", "exp2"}:
            raise IntervalCodecError("unexpected interval fields")
        return cls(
            _strict_int(obj["lo_num"], "lo_num"),
            _strict_int(obj["hi_num"], "hi_num"),
            _strict_int(obj["exp2"], "exp2"),
        )

    @classmethod
    def from_fraction_bounds(cls, lo: Fraction, hi: Fraction) -> "DyadicInterval":
        if lo > hi:
            raise IntervalCodecError("lower endpoint exceeds upper endpoint")
        if not _is_power_of_two(lo.denominator) or not _is_power_of_two(hi.denominator):
            raise IntervalCodecError("exact endpoints are not dyadic")
        elo = lo.denominator.bit_length() - 1
        ehi = hi.denominator.bit_length() - 1
        exp2 = max(elo, ehi)
        if exp2 > MAX_EXP2:
            raise IntervalCodecError("endpoint exponent outside resource-safe range")
        scale = 1 << exp2
        lo_num = lo.numerator * (scale // lo.denominator)
        hi_num = hi.numerator * (scale // hi.denominator)
        return cls(lo_num, hi_num, exp2)

    @classmethod
    def from_decimal_bounds(
        cls, lo: str | Decimal, hi: str | Decimal, *, bits: int = 192
    ) -> "DyadicInterval":
        if isinstance(bits, bool) or not isinstance(bits, int) or bits <= 0 or bits > MAX_EXP2:
            raise IntervalCodecError("bits must be a positive resource-safe integer")
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

    @classmethod
    def from_arb(cls, ball: Any) -> "DyadicInterval":
        """Encode a finite Arb ball from directed exact endpoints."""
        try:
            lo = ball.lower()
            hi = ball.upper()
        except Exception as exc:
            raise IntervalCodecError("value does not provide Arb lower/upper endpoints") from exc
        qlo = _fraction_from_man_exp(lo)
        qhi = _fraction_from_man_exp(hi)
        out = cls.from_fraction_bounds(qlo, qhi)
        if out.lo > qlo or out.hi < qhi:
            raise IntervalCodecError("Arb endpoint encoding failed to enclose source ball")
        return out


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"))
