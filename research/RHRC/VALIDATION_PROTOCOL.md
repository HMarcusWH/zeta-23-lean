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
merged research PR = #168
validated research head = 9657dad6f1e262b1fa7e08e6944aaa935feeaf33
merged research commit = 4e2c111a836f3fc95f8209485f726dc886c918e7
research tree = 881e1f05302041f56ae4b6a14f14e45d7bbc096b
RHRC #1055 = SUCCESS
Permansson #828 = SUCCESS
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
```

Interpretation law:

```text
research gate green
  -> executable research check is validated on the exact head
  -/-> Lean theorem
  -/-> global sign theorem
  -/-> whole-cell theorem
  -/-> RH evidence beyond its exact finite/symbolic scope
```

In particular:

- exact SymPy identities are **EXACT EXECUTABLE**, not Lean theorem authority;
- floating discovery is **EXPERIMENTAL SIGNAL**;
- Arb pointwise replay is **RIGOROUS FINITE CERTIFICATION** only;
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

These establish theorem authority through #163. Research PRs #165-#168 do not alter this declaration set.

## What the post-#163 research checks validate operationally

### #165

The exact executable Riesz-8 endpoint-scalar normalization, prime-power handling, stable pole expression and finite Arb replay are internally cross-checked. No global sign theorem is created.

### #166

The discovery state is aligned with the generalized shifted system `H-lambda G`; source-channel reconstruction and Arb safe-shift plumbing are checked. No actual first-bad state is assumed to exist in the finite scan.

### #167

The Q16 near-critical scalar barrier is searched. The direct whole-cell Arb representation returns 256/256 unresolved depth-8 leaves. That validates a methodological limitation, not a sign.

### #168

The boundary-flat threshold-jet algebra is checked exactly in the executable layer for `K=2..8`; the Q16/Q17 threshold and finite two-sided microscope are replayed with Arb. The full Q17 discovery state remains positive in the sampled scope while continuing downward.

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
boundary-flat threshold-jet law as a separately Lean-theoremized aperture-entry theorem
full scalar pivot/background inequality
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

The post-#168 docs/routing synchronization leaves those promotion surfaces unchanged.

## Control-v2 validation law

Control v2 has no theorem/claim/terminal-answer authority. Its CI gates enforce separate theorem/control anchors, deterministic routing, fail-closed retro/first-break contracts, dead-route revival requirements and hard-coded current theorem/frontier/action smoke assertions.

The post-#168 synchronization must:

- keep theorem anchor at #163;
- keep control semantic anchor at #117;
- keep frontier and selected action unchanged;
- keep `E4A4-SCHUR-FB-05` as the sole selected first break;
- refresh surviving objections through #165-#168;
- record the full scalar pivot/background decomposition as the current highest-information research slice;
- preserve endpoint-scalar/sourceMoment/parity/odd-selected firewalls;
- preserve DR-024 and global monotonicity quarantines;
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
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **RIGOROUS FINITE CERTIFICATION** — Arb/interval statement in the exact finite scope only;
- **LEAD / HYPOTHESIS** — motivated research route;
- **OPEN** — not established.

## Claim firewall

Green #163 mixed-source/Riesz theorems are not RH. Green #165-#168 research tooling is not theorem authority. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**