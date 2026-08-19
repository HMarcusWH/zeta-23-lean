# HMWH Zeta23 fork: research boundary

This fork preserves the inherited Anthropic Zeta23 formalization as a trusted baseline and adds an explicitly separated research program for exceptional-zero detection.

## Boundary

Baseline main commit: `cec57f919ccf34e5fa5372b4ba332f7c848bbb6e`.

Everything under `research/RHRC/` is discovery, falsification, provenance, or experiment infrastructure. It is **not** a theorem dependency and cannot promote a mathematical claim by itself.

Everything under `Zeta23/ExceptionalZero/` is intended to remain ordinary Lean mathematics. Files in that subtree must contain no `sorry` and no project-declared axioms. Open research obligations live in `research/RHRC/CLAIM_REGISTRY.json`, not as Lean axioms.

## Permanent rules

1. Research machinery does not become a theorem dependency.
2. Synthetic zeta-like worlds calibrate the solver; they are never counterexamples to zeta unless realizability is independently proved.
3. A candidate does not escape `Zeta23.ZeroSide.TightMult` merely by computing another scalar function of the same compression data. It must state the additional information channel it uses.
4. Conditional, numerical, heuristic, and synthetic ancestry is transitive. It cannot be laundered into `PROVED_UNCONDITIONAL` by composition.
5. The fork may search aggressively and must promote conservatively.
