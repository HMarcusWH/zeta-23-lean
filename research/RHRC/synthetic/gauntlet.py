from __future__ import annotations

from dataclasses import dataclass
from math import cos, exp

@dataclass(frozen=True)
class World:
    name: str
    tightmult_visible: tuple[float, ...]
    multiscale_probe: tuple[float, ...] | None
    truth: str
    note: str = ""


def build_worlds() -> dict[str, World]:
    same = (4.0, 4.0, 1.0)
    return {
        "G00": World("pure-null", (0.0,0.0,0.0), (0.0,0.0,0.0), "NULL"),
        "G01": World("planted-global-source", (1.0,1.0,0.0), (1.0,1.4,2.0), "SOURCE"),
        "G02": World("single-offline-pair", (2.0,2.0,1.0), tuple(exp(0.04*a) for a in (10.,20.,30.)), "OFFLINE_PAIR"),
        "G03": World("online-double", same, (1.0,1.0,1.0), "ONLINE_DOUBLE"),
        "G04": World("tight-offline-pair", same, None, "OFFLINE_PAIR"),
        "G05": World("tight-pair-no-extra-channel", same, None, "INSUFFICIENT_INFORMATION", "must fail closed"),
        "G06": World("tight-pair-with-scale-channel", same, tuple(exp(0.08*a) for a in (10.,20.,30.)), "OFFLINE_PAIR"),
        "G07": World("adversarial-phase-cancellation", (2.0,2.0,2.0), tuple(exp(0.05*a)*abs(cos(a)) for a in (10.,20.,30.)), "ADVERSARIAL"),
        "G08": World("clustered-near-degenerate-pairs", (4.0,4.0,2.0), (1.0,1.01,1.03), "CLUSTER"),
        "G09": World("matched-window-artifact", (1.0,1.0,0.0), (1.0,1.02,1.01), "ARTIFACT"),
        "G10": World("local-evolving-source", (1.0,1.0,0.0), (0.2,0.8,1.6), "EVOLVING_SOURCE"),
        "G11": World("high-gamma-tiny-delta", (2.0,2.0,1.0), tuple(exp(0.002*a) for a in (10.,20.,30.)), "HARD_OFFLINE_PAIR"),
    }


def distinguish_from_tightmult_only(a: World, b: World) -> str:
    if a.tightmult_visible == b.tightmult_visible:
        return "INSUFFICIENT_INFORMATION"
    return "DISTINGUISHABLE"


def positive_log_slope(values: tuple[float, ...]) -> bool:
    if len(values) < 2 or any(v <= 0 for v in values):
        return False
    return values[-1] > values[0]
