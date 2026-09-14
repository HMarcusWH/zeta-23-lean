# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, merged theorem-bearing commit/tree and relevant compiler/toolchain evidence. Compiler validity attaches only to the exact checked object.

For research-only PRs, record the exact research head/merge and CI evidence separately. A green research PR validates that its executable checks ran as specified; it does not convert symbolic/numerical/Arb research output into Lean theorem authority.

## Authority classes

### Theorem authority

```text
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
```

### Latest research-evidence anchor

```text
merged research PR = #178
validated research head = 28df43faed0db8c0f12a25525df6c28467ce5b07
merged research commit = fb2a181ce0d95d90396ead7730e7bf365616a153
research tree = 96ab14953e9e8bff5245953082db8a6471648614
RHRC #1074 = SUCCESS
Permansson #847 = SUCCESS
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

## Current R003 research audit stack

The R003 workflow also runs executable research checks that are **not theorem promotion surfaces**:

```text
post-#150 selected-residual certification plumbing / scout / replay
post-#163 endpoint-scalar audit                       [research PR #165]
post-#165 shifted-state plumbing / scout / replay    [research PR #166]
post-#166 Q16 scalar-barrier scout / interval audit  [research PR #167]
post-#167 threshold-jet algebra / Q17 scout / replay [research PR #168]
post-#169 theorem-aligned Schur visibility algebra   [research PR #170]
post-#169 threshold Schur/background scout           [research PR #170]
post-#169 Arb Schur-visibility replay                 [research PR #170]
post-#171 threshold-barrier accounting check         [research PR #172]
post-#171 multi-cell threshold-barrier scout         [research PR #172]
post-#171 Arb finite-point barrier replay            [research PR #172]
post-#173 q13 scalar-barrier plumbing                [research PR #174]
post-#173 q13 2x2 scalar scout                       [research PR #174]
post-#173 q13 adaptive Arb scalar audit              [research PR #174]
post-#175 fixed-unit q13 enclosure plumbing          [research PR #176]
post-#175 fixed-unit q13 benchmark                   [research PR #176]
post-#175 fixed-unit agreement/width certification  [research PR #176]
post-#177 fixed-unit derivative plumbing             [research PR #178]
post-#177 Q14 derivative schedule/probe              [research PR #178]
post-#177 derivative discrimination certification   [research PR #178]
```

Interpretation law:

```text
research gate green
  -> executable research check is validated on the exact head
  -/-> Lean theorem
  -/-> global sign theorem
  -/-> whole-cell theorem
  -/-> universal arithmetic-entry sign
  -/-> RH evidence beyond its exact finite/symbolic scope
```

In particular:

- exact SymPy/algebraic identities are **EXACT EXECUTABLE**, not Lean theorem authority;
- floating discovery is **EXPERIMENTAL SIGNAL**;
- deterministic Gauss-Legendre integration smoke tests are **DETERMINISTIC NUMERICAL VALIDATION**, not exact integral identities;
- Arb pointwise replay is **RIGOROUS FINITE CERTIFICATION** only;
- Arb interval output is a rigorous enclosure only for the exact encoded interval expression;
- Arb central finite differences are **RIGOROUS FINITE-DIFFERENCE ENCLOSURES**, not derivative theorems;
- production envelope quadrature is a numerical diagnostic unless separately interval-certified;
- `UNRESOLVED` interval output is neither positive nor negative evidence;
- absence of a finite negative candidate is not a positivity theorem.

## Exact #163 theorem evidence

At validated theorem head `b418ff034428f92594bab0e5b8276181a086ee4b`, RHRC #1039 and Permansson #812 completed successfully. The theorem-bearing closure includes aggregate CCM and ExceptionalZero builds, R003 normalization/source checks, Control-v2/regression tests and the forbidden-placeholder/project-axiom gate.

Validated declarations include:

```text
iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
```

These establish theorem authority through #163. Research PRs #165-#178 do not alter this declaration set.

## What the post-#163 research checks validate operationally

### #165

Exact executable Riesz-8 endpoint-scalar normalization, prime-power handling, stable pole expression and finite Arb replay are internally cross-checked. No global sign theorem is created.

### #166

Discovery is aligned with the generalized shifted system `H-lambda G`; source-channel reconstruction and Arb safe-shift plumbing are checked. No actual first-bad state is assumed to exist in the finite scan.

### #167

The Q16 near-critical cell is searched. The direct whole-cell Arb representation returns 256/256 unresolved depth-8 leaves. That validates a methodological limitation, not a sign.

### #168

Boundary-flat threshold-jet algebra is checked exactly in the executable layer for `K=2..8`; the Q16/Q17 threshold and finite two-sided microscope are replayed with Arb.

### #170

The deterministic checker validates theorem-aligned `[W|c]` one-step geometry, unit-shell agreement with the selected residual, exact finite-dimensional rank-one Schur update, exact directional Schur derivative, and transformed threshold moment law. Arb replay finite-certifies the checked q17 visibility/background behavior.

### #172

The threshold-to-threshold layer validates the finite-dimensional accounting and finite Arb replay across several arithmetic intervals. Current-q entry lift is sign-indefinite in the tested finite states and the q13/N2/K3/even state becomes the strongest near-critical target.

### #174

The deterministic checker validates the exact q13/N2/K3/even 1D->2D theorem-aligned scalar geometry, exact research-basis norms, physical-cell seam handling, and the reduction

```text
H1 <-> a_even(L) > 0
Delta_even(L) = a_even(L)d_even(L)-b_even(L)^2
sign pivot = sign Delta_even in H1.
```

The 384-bit direct scalar interval audit reports

```text
Q=13: 100% UNRESOLVED
Q=14: 100% UNRESOLVED
Q=15: 100% UNRESOLVED
```

with zero positive, bad, or H1-loss width certified. No zero/contact theorem follows from a zero-containing enclosure.

Operational interpretation:

```text
direct scalar interval UNRESOLVED
  -/-> determinant zero
  -/-> determinant negative
  -/-> determinant positive
  -> current direct scalar enclosure representation is insufficient
```

### #176

The fixed-unit research path rewrites the archimedean integrals on a fixed unit interval while keeping the direct evaluator as an independent comparator. The exact PR pipeline validates primitive, full-matrix, theorem-aligned scalar, odd-ancestry, seam and zero-weight agreement.

Its frozen fixture defines six primary Q14 boxes at three radii around the separately sampled determinant and Schur-pivot minima, with predeclared `material_width_gain_factor = 2.0`.

The exact RHRC #1072 certifier reports

```text
status = PASS
method_classification = FIXED_UNIT_METHOD_ACCEPTED
```

and all six primary boxes satisfy the strict-narrower/material-gain criterion.

Operational interpretation:

```text
FIXED_UNIT_METHOD_ACCEPTED
  -> frozen direct/fixed-unit agreement checks passed
  -> predeclared factor-2 determinant-width method gate passed
  -> fixed-unit value-level research investment is justified

  -/-> determinant sign
  -/-> stationary-point theorem
  -/-> whole-cell q13 positivity
  -/-> arbitrary first-bad restriction
  -/-> FB-05 closure
  -/-> Lean theorem promotion
```

### #178

The derivative research path differentiates the complete fixed-Q canonical source

```text
M'(L)=pole'(L)-arch'(L)-prime'(L)
```

and restricts it through the theorem-aligned `[W|c]` basis to `a',b',d'` and

```text
Delta_2' = a'd + ad' - 2bb'.
```

The checker compares analytic primitive derivatives, every upper-triangular entry of the complete 7x7 derivative matrix, theorem-aligned scalar derivatives and odd-N2 predecessor derivative against centered differences of the already-green value evaluators. Derivative continuation is required only at zero-von-Mangoldt seams 14 and 15.

The exact RHRC #1074 certifier reports

```text
status = PASS
derivative disposition = DERIVATIVE_UNRESOLVED
orientation = NO_CERTIFIED_PRIMARY_DERIVATIVE_SIGN
left_negative_labels  = []
left_positive_labels  = []
right_negative_labels = []
right_positive_labels = []
derived_stationary_existence_if_continuity_used = false
uniqueness_claim = false
```

and separately

```text
value event = NO_BAD_OR_H1_LOSS_INTERVAL_CERTIFIED
bad_labels = []
h1_loss_labels = []
```

Operational interpretation:

```text
DERIVATIVE_UNRESOLVED
  -> the complete derivative implementation/checking stack is valid on the exact head
  -> all six primary raw Delta_2' interval boxes contain no certified sign

  -/-> Delta_2' = 0
  -/-> stationary existence
  -/-> stationary uniqueness
  -/-> contact
  -/-> bad successor
  -/-> H1 loss
  -/-> failure of every derivative representation
```

#178 also closes the #176 standalone replay-hardening debt: the certifier reconstructs the frozen schedule from the fixture, and adversarial schedule mutations are rejected.

## Current FB-05 research target

The q13 scalar geometry, fixed-unit value representation, and complete derivative implementation are now consumed research infrastructure.

The next target is correlation-preserving derivative enclosure:

```text
1. rigorous point Delta_2' signs at frozen centers
2. compare exact raw and H1 Schur-factorized derivative representations
3. if point orientation is visible, add Delta_2'' and centered mean-value/Taylor bounds
4. only after a two-sided derivative bracket, attempt interval Newton/Krawczyk.
```

Do not repeat the same raw assembled derivative boxes with only more precision/depth and call it a new route.

## Axiom inspection

The #163 mixed-source headline declarations carry module-local `#print axioms` checks. The successful aggregate build plus the no-placeholder/project-axiom gate makes them compiler-validated theorem authority. The accepted production foundation remains `[propext, Classical.choice, Quot.sound]`; no production theorem may depend on `sorryAx` or a promoted project axiom.

Research Python/SymPy/Arb tooling has no authority to alter this axiom surface.

## What remains outside theorem authority

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine the seventh jet at zero
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
boundary-flat threshold-entry law as a separately Lean-theoremized aperture theorem
Schur-envelope derivative as a project Lean theorem
q13/N2/K3/even whole-cell strict positivity / nonvanishing
universal arithmetic threshold-entry sign
simultaneous even/odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing complete arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate. A declaration becomes compiler-validated project theorem authority only when its module lies in an exact successful authoritative build closure or is explicitly built by such a gate.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, theorem names must agree across

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

The post-#178 docs/routing synchronization leaves those promotion surfaces unchanged.

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
- **DETERMINISTIC NUMERICAL VALIDATION** — deterministic floating numerical acceptance test with an explicit tolerance;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **RIGOROUS FINITE CERTIFICATION** — Arb/interval statement in the exact finite scope only;
- **RIGOROUS FINITE-DIFFERENCE ENCLOSURE** — certified finite quotient/enclosure, not a derivative theorem;
- **LEAD / HYPOTHESIS** — motivated research route;
- **OPEN** — not established.

## Claim firewall

Green #163 mixed-source/Riesz theorems are not RH. Green #165-#178 research tooling is not theorem authority. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**