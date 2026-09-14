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
merged research PR = #176
validated research head = c6f53131b91b18aff2a50a6db2ddaa2761e7e5aa
PR integration commit tested by Actions = ad6c904cf38c64d61c7990b3b6e87eec27ad0064
merged research commit = 96cccf715c02ed2bd4ae58f8362180020ae90854
research tree = 28bd302c17a6128e538a3510917dafb670f6dce8
RHRC #1072 = SUCCESS
Permansson #845 = SUCCESS
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

These establish theorem authority through #163. Research PRs #165-#176 do not alter this declaration set.

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

The floating scout refines the dangerous Q14 basin and remains sampled-positive.

The 384-bit direct scalar interval audit reports

```text
Q=13: 100% UNRESOLVED
Q=14: 100% UNRESOLVED
Q=15: 100% UNRESOLVED
```

with zero positive, bad, or H1-loss width certified. No zero/contact theorem follows from a zero-containing enclosure, no strict-positive whole-cell theorem is created, and no shifted-state handoff is emitted.

Operational interpretation:

```text
direct scalar interval UNRESOLVED
  -/-> determinant zero
  -/-> determinant negative
  -/-> determinant positive
  -> current direct scalar enclosure representation is insufficient
```

Because #167 already falsified brute subdivision of the full matrix and #174 now shows the same pathology after exact scalarization, the next certification attempt must change the representation or add analytic control rather than merely increase depth/precision.

### #176

The fixed-unit research path rewrites the archimedean integrals on a fixed unit interval while keeping the direct evaluator as an independent comparator. The exact PR pipeline validates primitive, full-matrix, theorem-aligned scalar, odd-ancestry, seam and zero-weight agreement.

Its frozen fixture defines six primary Q14 boxes at three radii around the separately sampled determinant and Schur-pivot minima, with predeclared `material_width_gain_factor = 2.0`.

The exact RHRC #1072 certifier reports

```text
status = PASS
method_classification = FIXED_UNIT_METHOD_ACCEPTED
```

and all six primary boxes report

```text
delta_strictly_narrower = true
delta_material_gain = true
```

Operational interpretation:

```text
FIXED_UNIT_METHOD_ACCEPTED
  -> frozen direct/fixed-unit agreement checks passed in the exact CI pipeline
  -> predeclared factor-2 q13/Q14 determinant-width method gate passed
  -> investing in fixed-unit derivative research is justified

  -/-> determinant sign
  -/-> stationary-point theorem
  -/-> whole-cell q13 positivity
  -/-> arbitrary first-bad restriction
  -/-> FB-05 closure
  -/-> Lean theorem promotion
```

### #176 replay-hardening caveat

The exact GitHub Actions pipeline generated the benchmark from the frozen fixture immediately before the certifier. A review identified that the standalone certifier itself does not independently verify every schedule-defining field of an externally supplied `PASS` benchmark against the fixture.

Therefore the exact in-pipeline #176 classification remains valid in its finite scope, while standalone/replayed certification should eventually be hardened to reject stale or hand-modified schedules explicitly. Do not silently upgrade this software-validation debt into mathematical evidence in either direction.

## Current FB-05 research target

The q13 scalar geometry and the first representation-selection gate are now consumed research infrastructure. The next target is fixed-unit derivative/stationary discrimination on the same observables:

```text
a(L)
Delta_2(L)=a(L)d(L)-b(L)^2
odd N=2 predecessor ancestry
```

Primary derivative chain:

```text
fixed-unit alpha', beta', gamma'
  -> a', b', d'
  -> Delta_2' = a'd + ad' - 2bb'.
```

The first acceptance gate is:

```text
analytic derivative evaluator agrees with independent
high-precision centered finite differences at frozen points
AND
rigorous derivative intervals are narrow enough to discriminate
outer Q14 monotone regions from the local stationary basin.
```

Only then should local Taylor models, interval Newton/Krawczyk, or certified minimum/contact isolation be treated as justified research investment.

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

The post-#176 docs/routing synchronization leaves those promotion surfaces unchanged.

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

Green #163 mixed-source/Riesz theorems are not RH. Green #165-#176 research tooling is not theorem authority. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
