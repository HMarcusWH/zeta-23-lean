from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from enum import Enum
from typing import Iterable

from ffbbp.v16_commutation import DecisionCommutationResult
from ffbbp.v16_horizon import HorizonCertificate


class TailBudgetStatus(str, Enum):
    CERTIFIED = "CERTIFIED"
    BOUND_UNAVAILABLE = "BOUND_UNAVAILABLE"
    OUTSIDE_TRUST_REGION = "OUTSIDE_TRUST_REGION"


class BudgetDecision(str, Enum):
    PRUNE = "PRUNE"
    UNRESOLVED = "UNRESOLVED"


def D(value: Decimal | int | float | str) -> Decimal:
    if isinstance(value, Decimal):
        return value
    if isinstance(value, float):
        return Decimal(str(value))
    return Decimal(value)


def _finite_nonnegative(value: Decimal, *, name: str) -> None:
    if not value.is_finite() or value < 0:
        raise ValueError(f"{name} must be finite and nonnegative")


def diagnostic_two_by_two_drop(mu: Decimal | int | float | str,
                               q: Decimal | int | float | str,
                               beta: Decimal | int | float | str) -> Decimal:
    """Exact scalar 2x2 comparison formula in Decimal arithmetic.

    This is a diagnostic formula. The certified route consumes explicit
    lower/upper input bounds and separate assurance certificates instead of
    treating point estimates as theorem data.
    """
    mu_d, q_d, beta_d = D(mu), D(q), abs(D(beta))
    if not mu_d.is_finite() or not q_d.is_finite() or not beta_d.is_finite():
        raise ValueError("diagnostic inputs must be finite")
    gap = q_d - mu_d
    with localcontext() as ctx:
        ctx.prec = 60
        disc = gap * gap + D(4) * beta_d * beta_d
        root = disc.sqrt()
        out = (root - gap) / D(2)
    return max(D(0), out)


def certified_step_upper(*, beta_upper: Decimal | int | float | str,
                          gap_lower: Decimal | int | float | str) -> Decimal | None:
    """Return beta_upper^2 / gap_lower when a positive gap is certified."""
    beta = abs(D(beta_upper))
    gap = D(gap_lower)
    if not beta.is_finite() or not gap.is_finite():
        raise ValueError("step-bound inputs must be finite")
    if gap <= 0:
        return None
    return beta * beta / gap


@dataclass(frozen=True)
class StepUpperBound:
    """One certified finite-prefix step, with its exact N index and provenance."""

    n: int
    upper: Decimal
    provenance: tuple[str, ...] = ()

    @staticmethod
    def make(n: int, upper: Decimal | int | float | str,
             provenance: tuple[str, ...] = ()) -> "StepUpperBound":
        if n < 0:
            raise ValueError("step index must be nonnegative")
        value = D(upper)
        _finite_nonnegative(value, name="step upper bound")
        return StepUpperBound(n=n, upper=value, provenance=provenance)


@dataclass(frozen=True)
class TailBudgetCertificate:
    start_n: int
    prefix_end_n: int
    prefix_steps: tuple[StepUpperBound, ...]
    prefix_upper: Decimal
    tail_upper: Decimal | None
    status: TailBudgetStatus
    method: str
    provenance: tuple[str, ...]
    horizon_certificate: HorizonCertificate | None
    assurance_reason: str

    @property
    def total_upper(self) -> Decimal | None:
        if self.status is not TailBudgetStatus.CERTIFIED or self.tail_upper is None:
            return None
        return self.prefix_upper + self.tail_upper


@dataclass(frozen=True)
class BudgetDecisionCertificate:
    decision: BudgetDecision
    headroom: Decimal | None
    horizon_passed: bool
    decision_commutation_required: bool
    decision_commutation_passed: bool | None
    reason: str


def _validate_prefix_steps(*, start_n: int, prefix_end_n: int,
                           steps: tuple[StepUpperBound, ...]) -> None:
    expected = tuple(range(start_n, prefix_end_n))
    actual = tuple(step.n for step in steps)
    if actual != expected:
        raise ValueError(
            "prefix steps must cover every N exactly once in sorted contiguous order: "
            f"expected={expected}, actual={actual}"
        )


def _horizon_covers_remaining_budget(horizon: HorizonCertificate | None,
                                     tail_upper: Decimal) -> tuple[bool, str]:
    if horizon is None:
        return False, "HORIZON_CERTIFICATE_MISSING"
    if not horizon.passed:
        return False, f"HORIZON_CERTIFICATE_NOT_PASSED:{horizon.status.value}"
    if horizon.contract.target_metric != "remaining_deformation_budget":
        return False, "HORIZON_TARGET_METRIC_MISMATCH"
    if horizon.propagated_upper is None:
        return False, "HORIZON_PROPAGATED_BOUND_MISSING"
    propagated = D(horizon.propagated_upper)
    if not propagated.is_finite() or propagated < 0:
        return False, "HORIZON_PROPAGATED_BOUND_INVALID"
    if propagated > tail_upper:
        return False, "TAIL_UPPER_TIGHTER_THAN_HORIZON_BOUND"
    return True, "HORIZON_CERTIFIED_FOR_REMAINING_DEFORMATION_BUDGET"


def make_tail_budget_certificate(*, start_n: int,
                                 prefix_bounds: Iterable[StepUpperBound],
                                 prefix_end_n: int,
                                 tail_upper: Decimal | int | float | str | None,
                                 in_trust_region: bool,
                                 method: str,
                                 provenance: tuple[str, ...],
                                 horizon_certificate: HorizonCertificate | None = None) -> TailBudgetCertificate:
    """Build a fail-closed complete-budget certificate.

    `prefix_end_n` is exclusive: prefix steps must be exactly
    `start_n, ..., prefix_end_n - 1`. A numeric tail is not certified unless a
    passed FFBBP v1.6 horizon certificate explicitly targets
    `remaining_deformation_budget` and carries a propagated bound no larger
    than the recorded tail upper bound.
    """
    if start_n < 0 or prefix_end_n < start_n:
        raise ValueError("invalid N interval")
    if not method:
        raise ValueError("tail method is required")

    steps = tuple(prefix_bounds)
    _validate_prefix_steps(start_n=start_n, prefix_end_n=prefix_end_n, steps=steps)
    prefix = sum((step.upper for step in steps), D(0))
    _finite_nonnegative(prefix, name="prefix upper bound")

    if not in_trust_region:
        return TailBudgetCertificate(
            start_n, prefix_end_n, steps, prefix, None,
            TailBudgetStatus.OUTSIDE_TRUST_REGION, method, provenance,
            horizon_certificate, "OUTSIDE_DECLARED_TRUST_REGION",
        )

    if tail_upper is None:
        return TailBudgetCertificate(
            start_n, prefix_end_n, steps, prefix, None,
            TailBudgetStatus.BOUND_UNAVAILABLE, method, provenance,
            horizon_certificate, "INFINITE_TAIL_BOUND_UNAVAILABLE",
        )

    tail = D(tail_upper)
    _finite_nonnegative(tail, name="tail upper bound")
    horizon_ok, horizon_reason = _horizon_covers_remaining_budget(horizon_certificate, tail)
    if not horizon_ok:
        return TailBudgetCertificate(
            start_n, prefix_end_n, steps, prefix, None,
            TailBudgetStatus.BOUND_UNAVAILABLE, method, provenance,
            horizon_certificate, horizon_reason,
        )

    return TailBudgetCertificate(
        start_n, prefix_end_n, steps, prefix, tail,
        TailBudgetStatus.CERTIFIED, method, provenance,
        horizon_certificate, horizon_reason,
    )


def certified_headroom(mu_lower: Decimal | int | float | str,
                       budget: TailBudgetCertificate) -> Decimal | None:
    total = budget.total_upper
    if total is None:
        return None
    mu = D(mu_lower)
    if not mu.is_finite():
        raise ValueError("mu lower bound must be finite")
    return mu - total


def certify_prune_decision(
    mu_lower: Decimal | int | float | str,
    budget: TailBudgetCertificate,
    *,
    decision_commutation_required: bool = False,
    decision_commutation: DecisionCommutationResult[BudgetDecision] | None = None,
) -> BudgetDecisionCertificate:
    """Combined fail-closed gate for a deformation-budget PRUNE decision."""
    headroom = certified_headroom(mu_lower, budget)
    horizon_passed = (
        budget.status is TailBudgetStatus.CERTIFIED
        and budget.horizon_certificate is not None
        and budget.horizon_certificate.passed
    )

    if headroom is None or not horizon_passed:
        return BudgetDecisionCertificate(
            BudgetDecision.UNRESOLVED, headroom, horizon_passed,
            decision_commutation_required,
            None if decision_commutation is None else decision_commutation.passed,
            "COMPLETE_CERTIFIED_HORIZON_BUDGET_REQUIRED",
        )

    if decision_commutation_required:
        if decision_commutation is None:
            return BudgetDecisionCertificate(
                BudgetDecision.UNRESOLVED, headroom, horizon_passed, True, None,
                "DECISION_COMMUTATION_CERTIFICATE_MISSING",
            )
        if not decision_commutation.passed:
            return BudgetDecisionCertificate(
                BudgetDecision.UNRESOLVED, headroom, horizon_passed, True, False,
                "DECISION_COMMUTATION_FAILED",
            )

    if headroom > 0:
        return BudgetDecisionCertificate(
            BudgetDecision.PRUNE, headroom, horizon_passed,
            decision_commutation_required,
            None if decision_commutation is None else decision_commutation.passed,
            "POSITIVE_CERTIFIED_HEADROOM_AFTER_COMPLETE_ASSURED_TAIL",
        )

    return BudgetDecisionCertificate(
        BudgetDecision.UNRESOLVED, headroom, horizon_passed,
        decision_commutation_required,
        None if decision_commutation is None else decision_commutation.passed,
        "CERTIFIED_HEADROOM_NOT_POSITIVE",
    )


def prune_decision(
    mu_lower: Decimal | int | float | str,
    budget: TailBudgetCertificate,
    *,
    decision_commutation_required: bool = False,
    decision_commutation: DecisionCommutationResult[BudgetDecision] | None = None,
) -> BudgetDecision:
    return certify_prune_decision(
        mu_lower,
        budget,
        decision_commutation_required=decision_commutation_required,
        decision_commutation=decision_commutation,
    ).decision


def first_unexcluded_crossing_index(mu_lower: Decimal | int | float | str,
                                    bounds: Iterable[tuple[int, Decimal | int | float | str]]) -> int | None:
    """First index not excluded by contiguous supplied finite cumulative bounds.

    This is not evidence that a crossing actually occurs at that index.
    """
    target = D(mu_lower)
    if not target.is_finite():
        raise ValueError("mu lower bound must be finite")
    cumulative = D(0)
    previous_n: int | None = None
    for n, bound in bounds:
        if n < 0:
            raise ValueError("step index must be nonnegative")
        if previous_n is not None and n != previous_n + 1:
            raise ValueError("crossing bounds must be sorted and contiguous")
        previous_n = n
        b = D(bound)
        _finite_nonnegative(b, name="step upper bound")
        cumulative += b
        if cumulative >= target:
            return n + 1
    return None
