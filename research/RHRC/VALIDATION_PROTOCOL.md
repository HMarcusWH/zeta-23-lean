# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, merged theorem-bearing commit/tree and relevant compiler/toolchain evidence. Compiler validity attaches only to the exact checked object.

For research-only PRs, record the exact research head/merge and CI evidence separately. A green research PR validates that its executable checks ran as specified; it does not convert symbolic/numerical/Arb research output into Lean theorem authority.

## Authority classes

### Theorem authority

```text
latest theorem-bearing PR = #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS
```

### Latest research-evidence anchor

```text
merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS
```

### Control authority

```text
control-plane anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

Theorem, research and control anchors are deliberately separate.

## Authoritative repository gates

Current theorem/claim gates include:

```text
python research/RHRC/tools/run_suite.py
R003 normalization audit / dictionary guards / source-normalization firewall
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
```

A skipped downstream step is not a passed gate. Control-v2 regression tests guard routing semantics only; they do not grant theorem authority.

## Exact #182 theorem evidence

PR #182 validated the exact head

```text
0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
```

with theorem tree

```text
e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
```

and was merged as

```text
a69160d37a84049711aaff6c3d5db804583a7306.
```

The module `Zeta23/CCM/SchurEnvelopeDerivative.lean` is imported by `Zeta23/CCM.lean`, so the successful aggregate CCM build compiler-validates its declarations. The same workflow also built `Zeta23.ExceptionalZero` and ran the forbidden-placeholder scan over the promoted CCM/ExceptionalZero subtrees. Permansson #855 independently completed successfully.

Validated declarations include:

```text
schurDet2x2_eq_mul_pivot
schurDet2x2Derivative_eq_factorized
schurPivot2x2Derivative_eq_detQuotientDerivative
hasDerivAt_schurPivot2x2
hasDerivAt_schurDet2x2
schurDet2x2Derivative_eq_mul_pivotDerivative_of_contact
schurDet2x2Derivative_neg_iff_pivotDerivative_neg_of_contact
schurDet2x2Derivative_pos_iff_pivotDerivative_pos_of_contact
```

Operational interpretation:

```text
PROVED / #182
  generic real 2x2 determinant-pivot factorization
  exact correlation-preserving pivot derivative
  exact quotient/envelope derivative equivalence
  actual scalar HasDerivAt theorems
  at contact P=0: Delta_2'=aP'
  under H1 a>0: determinant and pivot derivative orientations agree

NOT PROVED / #182
  contact existence or uniqueness
  production arithmetic sign for P' or Delta_2'
  finite-width H1 on the Q14 boxes
  production/Hermitian Schur-envelope bridge
  global Schur monotonicity
  first-bad exclusion
  negative-root exclusion
  RH
```

## Post-#163 research checks remain research evidence

The R003 workflow continues to run the post-#163 research chain through #180: endpoint-scalar audit; shifted-state scout/replay; Q16 interval audit; threshold-jet/Q17 microscope; theorem-aligned Schur visibility; threshold-to-threshold barrier audit; q13 scalar barrier; fixed-unit enclosure benchmark; complete derivative discrimination; and the post-#179 exact-center/Schur-scope audit.

Interpretation law:

```text
research gate green
  -> executable research check is validated on the exact head
  -/-> Lean theorem
  -/-> global sign theorem
  -/-> whole-cell theorem
  -/-> universal arithmetic-entry sign
  -/-> RH.
```

In particular:

- exact SymPy/algebraic identities are **EXACT EXECUTABLE**, not Lean theorem authority;
- floating discovery is **EXPERIMENTAL SIGNAL**;
- deterministic numerical checks are implementation evidence only;
- Arb pointwise replay is **RIGOROUS FINITE CERTIFICATION** only;
- Arb interval output is a rigorous enclosure only for the exact encoded interval expression;
- Arb central finite differences are finite-difference enclosures, not derivative theorems;
- `UNRESOLVED` is neither positive nor negative evidence;
- absence of a finite negative candidate is not a positivity theorem.

## Exact #180 research evidence

The inherited #178 schedule is reused exactly. At all six frozen primary Q14 exact centers, rigorous Arb point balls give

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
```

The Schur point graph agrees on the same H1-usable points. This supports a derived stationary-existence statement if continuity is invoked, but `uniqueness_claim = false`.

For the nonzero-width primary boxes:

```text
SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0
sign_recovery_labels = []
strict_width_gain_labels = []
material_2x_gain_labels = []
```

So #180 does not establish a finite-box Schur width gain or sign recovery.

## Current FB-05 validation target

The next finite research target is:

```text
1. centered H1 recovery from point a(L0)>0 plus rigorous a'(I)
2. inside recovered H1, retry the Schur derivative box using theorem-backed #182 calculus
3. if still unresolved, add Delta_2'' and centered derivative propagation
4. only after signed neighborhoods, attempt interval Newton/Krawczyk.
```

The parallel theorem target is an invariant/Hermitian production Schur-envelope bridge that attaches to the already-proved fixed-cell `-log(L)I + remainder` decomposition and exposes the exact universal `-||u||^2/L` drift plus a scalar production remainder derivative.

## Production normalization firewall after #182

The finite q13 research code uses exact integer `W,c` coordinates. Its shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified at the same magnitude. Formal production lives in a complex Hermitian carrier, while #182 is generic real 2x2 calculus.

Therefore:

```text
research W/c coordinates
  -/-> formal canonical shell coordinates by definitional equality
real b^2/a Schur correction
  -/-> complex Hermitian |b|^2/a without a specialization theorem.
```

Prefer invariant statements or separately prove the bridge.

## Axiom inspection

The accepted production foundation remains the compiler-reported Mathlib foundations; no production theorem may depend on `sorryAx` or a promoted project axiom. The authoritative workflow rejects `sorry` and top-level `axiom` declarations in the promoted CCM/ExceptionalZero subtrees.

Research Python/SymPy/Arb tooling has no authority to alter this axiom surface.

## What remains outside theorem authority

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine the seventh jet at zero
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
production/Hermitian Schur-envelope derivative bridge
source-specific production remainder/contact-orientation bound
centered finite-width H1 on frozen Q14 boxes
q13/N2/K3/even whole-cell strict positivity / nonvanishing / contact classification
simultaneous even/odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing complete arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate. A declaration becomes compiler-validated theorem authority only when its module lies in an exact successful authoritative build closure or is explicitly built by such a gate.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, theorem names must agree across

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

PR #182 adds theorem authority but does not alter those machine claim-promotion surfaces.

## Vocabulary

- **source present** — file exists;
- **module compiles** — Lean elaborated that module;
- **umbrella build green** — named target and transitive imports compiled;
- **PR green** — all required gates for the exact PR object succeeded;
- **PROVED** — exact statement compiler-validated with acceptable axiom surface;
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface;
- **DERIVED** — mathematical consequence not separately theorem-locked;
- **LOCAL LEAN CHECK** — standalone/local compilation outside merged theorem authority;
- **EXACT EXECUTABLE** — symbolic/executable identity locked by research tooling, not Lean theorem authority;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **RIGOROUS FINITE CERTIFICATION** — Arb/interval statement in the exact finite scope only;
- **LEAD / HYPOTHESIS** — motivated research route;
- **OPEN** — not established.

## Claim firewall

Green #182 Schur/contact calculus is not a zeta arithmetic sign theorem. Green #180 research evidence is not theorem promotion. A contradiction still requires a genuinely independent canonical arithmetic restriction on the exact retained state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN.**
