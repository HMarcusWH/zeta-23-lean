"""Deterministic bounded research priority, not likelihood of mathematical truth."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction


def natural(value: int, name: str, *, nonzero: bool = False) -> None:
    if type(value) is not int or value < (1 if nonzero else 0):
        raise ValueError(f"invalid {name}: expected {'positive' if nonzero else 'nonnegative'} integer")

@dataclass(frozen=True)
class Candidate:
    identifier: str
    dependencies: tuple[str, ...]
    information_gain: int
    cost: int

    def __post_init__(self) -> None:
        if type(self.identifier) is not str or not self.identifier.strip():
            raise ValueError("candidate must have a nonempty identifier")
        if type(self.dependencies) is not tuple or len(set(self.dependencies)) != len(self.dependencies):
            raise ValueError("dependencies must be a unique tuple")
        if any(type(x) is not str or not x.strip() for x in self.dependencies):
            raise ValueError("invalid dependency")
        if self.identifier in self.dependencies:
            raise ValueError("self dependency")
        natural(self.information_gain, "information_gain")
        natural(self.cost, "cost", nonzero=True)

@dataclass(frozen=True)
class Decision:
    tag: str
    candidate_id: str | None
    reason: str

    def __post_init__(self) -> None:
        if self.tag not in {"SELECT", "STOP"}:
            raise ValueError("unknown decision tag")
        if type(self.reason) is not str or not self.reason.strip():
            raise ValueError("decision reason is mandatory")
        if self.tag == "STOP" and self.candidate_id is not None:
            raise ValueError("STOP cannot select a candidate")
        if self.tag == "SELECT" and (type(self.candidate_id) is not str or not self.candidate_id):
            raise ValueError("SELECT must name a candidate")


def choose(candidates: tuple[Candidate, ...], completed: frozenset[str], budget: int) -> Decision:
    natural(budget, "budget")
    if type(candidates) is not tuple or any(type(c) is not Candidate for c in candidates):
        raise TypeError("candidates must be a tuple of Candidates")
    if type(completed) is not frozenset or any(type(s) is not str or not s for s in completed):
        raise TypeError("completed must be a frozenset of completed identifiers")
    ids = [c.identifier for c in candidates]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate candidate identifier")
    valid = [c for c in candidates if c.identifier not in completed
             and all(d in completed for d in c.dependencies) and c.cost <= budget]
    if not valid:
        return Decision("STOP", None, "No dependency-ready affordable candidate")
    chosen = min(valid, key=lambda c: (-Fraction(c.information_gain, c.cost), c.identifier))
    return Decision("SELECT", chosen.identifier, "Exact priority ratio and stable tie break")
