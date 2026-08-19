from __future__ import annotations

from dataclasses import dataclass
from math import exp

@dataclass(frozen=True)
class World:
    name: str
    tightmult_visible: tuple[float, ...]
    multiscale_probe: tuple[float, ...] | None
    truth: str


def build_worlds() -> dict[str, World]:
    # G03 and G04 deliberately share the same TightMult-visible vector.
    same = (4.0, 4.0, 1.0)
    return {
        "G00": World("pure-null", (0.0, 0.0, 0.0), (0.0, 0.0, 0.0), "NULL"),
        "G03": World("online-double", same, (1.0, 1.0, 1.0), "ONLINE_DOUBLE"),
        "G04": World("tight-offline-pair", same, None, "OFFLINE_PAIR"),
        "G05": World("tight-offline-pair-no-extra-channel", same, None, "INSUFFICIENT_INFORMATION"),
        "G06": World("tight-offline-pair-with-scale-channel", same,
                     tuple(exp(0.08 * a) for a in (10.0, 20.0, 30.0)), "OFFLINE_PAIR"),
    }


def distinguish_from_tightmult_only(a: World, b: World) -> str:
    if a.tightmult_visible == b.tightmult_visible:
        return "INSUFFICIENT_INFORMATION"
    return "DISTINGUISHABLE"


def positive_log_slope(values: tuple[float, ...]) -> bool:
    if len(values) < 2 or any(v <= 0 for v in values):
        return False
    return values[-1] > values[0]
