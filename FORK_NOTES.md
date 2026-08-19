# HMWH Zeta23 fork: research boundary

This fork preserves the inherited Anthropic Zeta23 formalization as a trusted baseline and adds an explicitly separated research program for exceptional-zero detection.

## Boundary

Baseline main commit: `cec57f919ccf34e5fa5372b4ba332f7c848bbb6e`.

Everything under `research/RHRC/` is discovery, falsification, provenance, or experiment infrastructure. It is **not** a theorem dependency and cannot promote a mathematical claim by itself.

Everything under `Zeta23/ExceptionalZero/` is intended to remain ordinary Lean mathematics. Files in that subtree must contain no `sorry` and no project-declared axioms. Open research obligations live in `research/RHRC/CLAIM_REGISTRY.json`, not as Lean axioms.

## FFBBP solver boundary

RHRC targets **FFBBP Reference Solver Architecture v1.5 (2026-08-19)**, which supersedes v1.4.2. The supplied v1.5 PDF is attested in `research/RHRC/ffbbp/FFBBP_REFERENCE.json` with SHA-256 `fed1d92e1c881a5be5a93261b29b813055c629679da3ddc8a2ed3502a09175ac`.

The named RUN42B A0 implementation profile is finite-synthetic qualified for unknown-field **diagnostic-only** interrogation after two-sided known-truth qualification. RHRC therefore treats V06N known-null immunity, V06P known-positive recovery, and relevant V06X artifact rejection as admission prerequisites. RUN38 remains a regression/pathology reference, not sufficient admission evidence by itself.

RUN42B profile values are reproducibility data, not universal constants. Material solver-profile changes require requalification, and the RH domain adapter must be frozen before a real zeta run.

## OoL-MVS route-closure boundary

RHRC now targets **OoL-MVS Kernel v2.7.6 (2026-08-19)** for operational route-closure semantics. The supplied release archive is attested in `research/RHRC/ool/OOL_REFERENCE.json` with SHA-256 `35eef74477b97cfa0f0c5367b51747022ba78c4df16e54869c41614d99e184f2`.

Only the domain-neutral governance layer is transplanted. The 24 origin-of-life physical claims are not RH premises. The imported contract is:

- complete formal worlds use `TRUE/FALSE`; partial experimental/research evidence uses strong-Kleene `PASS/FAIL/NA`;
- missing or unresolved evidence is `NA`, not silent `FAIL`;
- claim outcome is separate from certificate integrity, so `FAIL + VALID` is legal;
- claim-bearing evidence must bind to raw evidence, exact support receipts, witness identity and frozen registry/route/boundary identity;
- unknown provenance is not unconditional provenance; explicit conditional/conjectural ancestry blocks unconditional route closure;
- absence/clean-ancestry claims require a complete declared search domain;
- discovery may adapt, but confirmatory execution requires frozen route/boundary digests;
- claim-bearing changes after result/lockbox exposure require a new route digest and fresh confirmatory execution;
- route-specific protocols instantiate but may not weaken the governing semantics.

The supplied v2.7.6 package was independently executed in the authoring environment: all six packaged suites passed, **530/530 checks**. This verifies the package's software/formal/numerical consistency only; it is not RH evidence.

## Permanent rules

1. Research machinery does not become a theorem dependency.
2. Synthetic zeta-like worlds calibrate the solver; they are never counterexamples to zeta unless realizability is independently proved.
3. A candidate does not escape `Zeta23.ZeroSide.TightMult` merely by computing another scalar function of the same compression data. It must state the additional information channel it uses.
4. Conditional, numerical, heuristic, and synthetic ancestry is transitive. It cannot be laundered into `PROVED_UNCONDITIONAL` by composition.
5. FFBBP unknown-field admission is diagnostic only. No FFBBP posterior, qualification result, field recovery, or collapse decision is RH evidence or a theorem.
6. OoL evidence/certificate semantics govern research-route integrity but do not replace Lean/comparator as the authority for mathematical theoremhood.
7. Current R001/R002/R003 remain `DISCOVERY`; confirmatory digests are issued only after their claim-bearing mathematical objects and protocols are actually frozen.
8. The fork may search aggressively and must promote conservatively.
