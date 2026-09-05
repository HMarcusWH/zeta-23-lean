from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from enum import Enum


class ResearchRegime(str, Enum):
    NO_HISTORY = "NO_HISTORY"
    CONVERGENT = "CONVERGENT"
    BOUNDED_EXPLORATION = "BOUNDED_EXPLORATION"
    OSCILLATION = "OSCILLATION"
    EVALUATOR_MONOCULTURE = "EVALUATOR_MONOCULTURE"
    BENCHMARK_LOCK_IN = "BENCHMARK_LOCK_IN"
    CAPABILITY_RATCHET = "CAPABILITY_RATCHET"


@dataclass(frozen=True)
class RouteHistoryRecord:
    action_id: str
    evaluator_id: str
    benchmark_id: str | None
    complexity: int
    outcome: str


@dataclass(frozen=True)
class RegimeAssessment:
    regime: ResearchRegime
    reasons: tuple[str, ...]
    authorization: bool = False


def assess_regime(history: tuple[RouteHistoryRecord, ...], *, window: int = 8) -> RegimeAssessment:
    """Read-only PIRE-style monitor of the research controller itself.

    It detects obvious controller pathologies. It never authorizes a theorem,
    route promotion or action; `authorization` is permanently false.
    """
    if not history:
        return RegimeAssessment(ResearchRegime.NO_HISTORY, ("no route history available",))
    recent = history[-window:]

    if len(recent) >= 4:
        actions = [x.action_id for x in recent]
        if len(set(actions[-4:])) == 2 and actions[-4] == actions[-2] and actions[-3] == actions[-1]:
            return RegimeAssessment(
                ResearchRegime.OSCILLATION,
                ("alternating A/B/A/B route pattern detected",),
            )

    evaluator_counts = Counter(x.evaluator_id for x in recent)
    evaluator, count = evaluator_counts.most_common(1)[0]
    if len(recent) >= 5 and count / len(recent) >= 0.9:
        return RegimeAssessment(
            ResearchRegime.EVALUATOR_MONOCULTURE,
            (f"evaluator {evaluator!r} owns {count}/{len(recent)} recent evaluations",),
        )

    benchmarks = [x.benchmark_id for x in recent if x.benchmark_id]
    if len(benchmarks) >= 5:
        b_counts = Counter(benchmarks)
        benchmark, b_count = b_counts.most_common(1)[0]
        if b_count / len(benchmarks) >= 0.9:
            return RegimeAssessment(
                ResearchRegime.BENCHMARK_LOCK_IN,
                (f"benchmark {benchmark!r} dominates {b_count}/{len(benchmarks)} recent benchmarked runs",),
            )

    if len(recent) >= 4:
        complexities = [x.complexity for x in recent]
        if all(b > a for a, b in zip(complexities, complexities[1:])) and not any(
            x.outcome in {"KILLED", "PRUNED", "SIMPLIFIED"} for x in recent
        ):
            return RegimeAssessment(
                ResearchRegime.CAPABILITY_RATCHET,
                ("complexity strictly increased without a kill/prune/simplification event",),
            )

    if recent[-1].outcome in {"CLOSED", "PRUNED", "KILLED"}:
        return RegimeAssessment(
            ResearchRegime.CONVERGENT,
            (f"latest route outcome is {recent[-1].outcome}",),
        )

    return RegimeAssessment(
        ResearchRegime.BOUNDED_EXPLORATION,
        ("no configured long-run pathology detected",),
    )
