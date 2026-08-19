# HMWH Zeta23 fork: research boundary

This fork preserves the inherited Anthropic Zeta23 formalization as a trusted baseline and adds an explicitly separated research program for exceptional-zero detection.

## Boundary

Baseline main commit: `cec57f919ccf34e5fa5372b4ba332f7c848bbb6e`.

Everything under `research/RHRC/` is discovery, falsification, provenance, or experiment infrastructure. It is **not** a theorem dependency and cannot promote a mathematical claim by itself.

Everything under `Zeta23/ExceptionalZero/` is intended to remain ordinary Lean mathematics. Files in that subtree must contain no `sorry` and no project-declared axioms. Open research obligations live in `research/RHRC/CLAIM_REGISTRY.json`, not as Lean axioms.

## FFBBP solver boundary

RHRC now targets **FFBBP Reference Solver Architecture v1.5 (2026-08-19)**, which supersedes v1.4.2. The supplied v1.5 PDF is attested in `research/RHRC/ffbbp/FFBBP_REFERENCE.json` with SHA-256 `fed1d92e1c881a5be5a93261b29b813055c629679da3ddc8a2ed3502a09175ac`.

The named RUN42B A0 implementation profile is finite-synthetic qualified for unknown-field **diagnostic-only** interrogation after two-sided known-truth qualification. RHRC therefore treats V06N known-null immunity, V06P known-positive recovery, and relevant V06X artifact rejection as admission prerequisites. RUN38 remains a regression/pathology reference, not sufficient admission evidence by itself.

RUN42B profile values are reproducibility data, not universal constants. Material solver-profile changes require requalification, and the RH domain adapter must be frozen before a real zeta run.

## Permanent rules

1. Research machinery does not become a theorem dependency.
2. Synthetic zeta-like worlds calibrate the solver; they are never counterexamples to zeta unless realizability is independently proved.
3. A candidate does not escape `Zeta23.ZeroSide.TightMult` merely by computing another scalar function of the same compression data. It must state the additional information channel it uses.
4. Conditional, numerical, heuristic, and synthetic ancestry is transitive. It cannot be laundered into `PROVED_UNCONDITIONAL` by composition.
5. FFBBP unknown-field admission is diagnostic only. No FFBBP posterior, qualification result, field recovery, or collapse decision is RH evidence or a theorem.
6. The fork may search aggressively and must promote conservatively.
