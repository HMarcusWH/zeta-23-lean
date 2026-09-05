from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext
from enum import Enum
from typing import Iterable


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


def diagnostic_two_by_two_drop(mu: Decimal | int | float | str,
                               q: Decimal | int | float | str,
                               beta: Decimal | int | float | str) -> Decimal:
    """Exact scalar 2x2 comparison formula in Decimal arithmetic.

    This is a diagnostic formula.  The certified route should consume explicit
    lower/upper input bounds instead of treating point estimates as theorem data.
    """
    mu_d, q_d, beta_d = D(mu), D(q), abs(D(beta))
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
    if gap <= 0:
        return None
    return beta * beta / gap


@dataclass(frozen=True)
class TailBudgetCertificate:
    start_n: int
    prefix_end_n: int
    prefix_upper: Decimal
    tail_upper: Decimal | None
    status: TailBudgetStatus
    method: str
    provenance: tuple[str, ...]

    @property
    def total_upper(self) -> Decimal | None:
        if self.status is not TailBudgetStatus.CERTIFIED or self.tail_upper is None:
            return None
        return self.prefix_upper + self.tail_upper


def make_tail_budget_certificate(*, start_n: int, prefix_bounds: Iterable[Decimal | int | float | str],
                                 prefix_end_n: int, tail_upper: Decimal | int | float | str | None,
                                 in_trust_region: bool, method: str,
                                 provenance: tuple[str, ...]) -> TailBudgetCertificate:
    if start_n < 0 or prefix_end_n < start_n:
        raise ValueError("invalid N interval")
    prefix = sum((D(x) for x in prefix_bounds), D(0))
    if prefix < 0:
        raise ValueError("prefix upper bound cannot be negative")
    if not in_trust_region:
        return TailBudgetCertificate(start_n, prefix_end_n, prefix, None,
                                     TailBudgetStatus.OUTSIDE_TRUST_REGION, method, provenance)
    if tail_upper is None:
        return TailBudgetCertificate(start_n, prefix_end_n, prefix, None,
                                     TailBudgetStatus.BOUND_UNAVAILABLE, method, provenance)
    tail = D(tail_upper)
    if tail < 0:
        raise ValueError("tail upper bound cannot be negative")
    return TailBudgetCertificate(start_n, prefix_end_n, prefix, tail,
                                 TailBudgetStatus.CERTIFIED, method, provenance)


def certified_headroom(mu_lower: Decimal | int | float | str,
                       budget: TailBudgetCertificate) -> Decimal | None:
    total = budget.total_upper
    if total is None:
        return None
    return D(mu_lower) - total


def prune_decision(mu_lower: Decimal | int | float | str,
                   budget: TailBudgetCertificate) -> BudgetDecision:
    headroom = certified_headroom(mu_lower, budget)
    if headroom is not None and headroom > 0:
        return BudgetDecision.PRUNE
    return BudgetDecision.UNRESOLVED


def first_unexcluded_crossing_index(mu_lower: Decimal | int | float | str,
                                    bounds: Iterable[tuple[int, Decimal | int | float | str]]) -> int | None:
    """First index not excluded by the supplied finite cumulative upper bounds.

    This is not evidence that a crossing actually occurs at that index.
    """
    target = D(mu_lower)
    cumulative = D(0)
    for n, bound in bounds:
        b = D(bound)
        if b < 0:
            raise ValueError("step upper bounds must be nonnegative")
        cumulative += b
        if cumulative >= target:
            return n + 1
    return None
