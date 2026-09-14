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
merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS
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
post-#169 Arb Schur-visibility replay                [research PR #170]
post-#171 threshold-barrier accounting check         [research PR #172]
post-#171 multi-cell threshold-barrier scout         [research PR #172]
post-#171 Arb finite-point barrier replay            [research PR #172]
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

These establish theorem authority through #163. Research PRs #165-#172 do not alter this declaration set.

## What the post-#163 research checks validate operationally

### #165

The exact executable Riesz-8 endpoint-scalar normalization, prime-power handling, stable pole expression and finite Arb replay are internally cross-checked. No global sign theorem is created.

### #166

The discovery state is aligned with the generalized shifted system `H-lambda G`; source-channel reconstruction and Arb safe-shift plumbing are checked. No actual first-bad state is assumed to exist in the finite scan.

### #167

The Q16 near-critical scalar barrier is searched. The direct whole-cell Arb representation returns 256/256 unresolved depth-8 leaves. That validates a methodological limitation, not a sign.

### #168

The boundary-flat threshold-jet algebra is checked exactly in the executable layer for `K=2..8`; the Q16/Q17 threshold and finite two-sided microscope are replayed with Arb. The full Q17 discovery state remains positive in the sampled scope while continuing downward.

### #170

The deterministic checker validates theorem-aligned `[W|c]` one-step geometry, unit-shell agreement with the post-#150 selected residual, exact finite-dimensional rank-one Schur update, exact directional Schur derivative, and transformed threshold moment law.

The Arb replay finite-certifies q17 predecessor positivity, nonzero Schur visibility, positive q17 entering-q pivot effect at checked offsets, and negative q-removed background central finite differences.

### #172

The deterministic accounting checker validates exact finite-dimensional Schur/envelope algebra, genuine nonzero von-Mangoldt seam identification, production budget reconstruction, and threshold-entry vanishing at the seam. Its synthetic integral closure test is numerical: it uses 32-node floating Gauss-Legendre quadrature with a finite acceptance tolerance and therefore validates the integration implementation as a deterministic numerical smoke test, not as an exact executable integral identity.

The floating production scout tests several arithmetic intervals and reports no sampled bad successor. Its most dangerous target is `q13 -> 16, N2, K3, even`, with a sampled unit-shell pivot near `5.8e-12`.

The finite Arb replay certifies selected threshold and near-minimum points. In particular it certifies at the q13/even quantized candidate:

```text
H1 predecessor positive
full unit-shell pivot      ~= +5.8401616e-12
q-removed background       ~= +1.2217611e-11
q13 entry lift             ~= -6.3774491e-12
```

It also certifies negative current-q entry lift at q9/even and positive lift at q16/odd. Therefore no universal favorable arithmetic-entry sign may be inferred.

The q17 replay preserves another scope distinction: full physical H1 can hold while the q-removed background is not H1-certified. Algebraic `full-background` differences are not automatically first-bad comparative statements.

The large cancellation ratios observed by the production diagnostic are research evidence about conditioning, not formal derivative identities.

## Current q13 scalar-certification target

For the next research PR, the exact executable `N=2 -> K*=3` geometry should be checked again and the complete successor written as

```text
H(L) = [[a(L),b(L)],[b(L),d(L)]].
```

On H1 scope,

```text
a(L) > 0
P(L) = Delta_2(L)/a(L)
Delta_2(L)=a(L)d(L)-b(L)^2.
```

The whole-interval task must distinguish four outcomes:

```text
A. a(L) <= 0 somewhere: H1 scope loss.
B. a(L) > 0 and Delta_2(L) < 0 somewhere: strict bad successor.
C. a(L) > 0 and Delta_2(L) = 0 somewhere: barrier contact / singular successor.
D. a(L) > 0 and Delta_2(L) > 0 everywhere: strict positive-cell certificate.
```

Thus a nonnegative determinant certificate still requires a separate nonvanishing argument before it can be called a strict barrier.

A rigorous whole-interval claim over `log13 <= L <= log16` must respect physical integer cutoff cells Q=13,14,15 unless exact zero-weight seam inertness is separately certified. A pointwise Arb replay is insufficient for a whole-cell claim.

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

The post-#172 docs/routing synchronization leaves those promotion surfaces unchanged.

## Control-v2 validation law

Control v2 has no theorem/claim/terminal-answer authority. Its CI gates enforce separate theorem/control anchors, deterministic routing, fail-closed retro/first-break contracts, dead-route revival requirements and hard-coded current theorem/frontier/action smoke assertions.

The post-#172 synchronization must:

- keep theorem anchor at #163;
- keep control semantic anchor at #117;
- keep frontier and selected action unchanged;
- keep `E4A4-SCHUR-FB-05` as the sole selected first break;
- refresh surviving objections through #172;
- record the q13/N2/K3/even 2x2 scalar determinant barrier as the current highest-information research slice;
- record that finite current-q entry lift is sign-indefinite;
- preserve the physical-H1 versus background-H1 distinction;
- preserve endpoint-scalar/sourceMoment/parity/odd-selected firewalls;
- preserve DR-024/global monotonicity quarantines and the #167 representation warning;
- keep terminal claim `RH_OPEN`.

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
- **DETERMINISTIC NUMERICAL VALIDATION** — deterministic floating numerical acceptance test with an explicit tolerance; not an exact identity or theorem;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **RIGOROUS FINITE CERTIFICATION** — Arb/interval statement in the exact finite scope only;
- **RIGOROUS FINITE-DIFFERENCE ENCLOSURE** — certified finite quotient/enclosure, not a derivative theorem;
- **LEAD / HYPOTHESIS** — motivated research route;
- **OPEN** — not established.

## Claim firewall

Green #163 mixed-source/Riesz theorems are not RH. Green #165-#172 research tooling is not theorem authority. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
