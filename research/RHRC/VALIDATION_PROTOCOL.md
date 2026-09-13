# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, merged-main commit/tree and relevant compiler/toolchain evidence. Compiler validity attaches only to the exact checked object. A docs/control-only green does not create theorem authority.

## Authoritative repository gates

Current theorem/claim gates include:

```text
python research/RHRC/tools/run_suite.py
R003 normalization audit / dictionary guards / source-normalization firewall
post-#150 selected-residual certification plumbing / scout / certificate replay
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
```

A skipped downstream step is not a passed gate. Control-v2 regression tests guard routing semantics only; they do not grant theorem authority.

## Current theorem/control validation anchors

```text
latest theorem-bearing PR = #163
merged theorem-bearing main = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #163 validated PR head and merged main are different commit objects but share theorem tree `c397b3a0...`. PR #117 remains the Control-v2 semantic authority because #163 changes mathematical state, not controller capability/authority semantics.

## Exact #163 gate evidence

At validated theorem head `b418ff034428f92594bab0e5b8276181a086ee4b`, RHRC workflow run #1039 completed successfully. Its `python-rhrc`, `r003-normalization-audit`, and `lean` jobs all succeeded. The Lean job completed the aggregate CCM build, ExceptionalZero build and forbidden-placeholder/project-axiom scan. Permansson workflow run #812 also completed successfully.

The new modules are imported through `Zeta23.CCM` and therefore lie in the authoritative aggregate build closure.

## What #163 validates

### Generic mixed-source calculus

Validated declarations include:

```text
iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
```

These establish the exact normalized mixed quadratic-normal source observable, its seventh jet proportional to `M4`, the corresponding norm-square identity, the fact that the finite-prime contribution to `explicitCanonicalSourceMoment` samples the same observable, and the exact Riesz-8/Riesz-9 boundary rewrite through the squared seventh jet.

### Retained first-bad specialization

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedMixedSourceSeventhJet_eq_momentFour
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNine_eq_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_mixedJetBoundary
RegularCellMinimalNegativeEnergyCertificate.crossParityGamma_ne_zero_of_even_of_not_oddBad
```

The strict Riesz-9 upper bound on the retained even-selected shifted trial is obtained without a sign assumption on `canonicalPolePrimeRieszEndpointScalar`. The selected-parity condition remains explicit where used.

## Axiom inspection

The #163 mixed-source headline declarations carry module-local `#print axioms` checks. The successful aggregate build plus the no-placeholder/project-axiom gate makes them compiler-validated theorem authority. The accepted production foundation remains `[propext, Classical.choice, Quot.sound]`; no production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without becoming machine-promoted claims. #163 advances compiler theorem authority beyond the current machine-promoted claim-ID surface.

## What remains outside theorem authority after #163

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine the seventh jet at zero
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
simultaneous even/odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing complete arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

A shared analytic observable in the finite-prime sum and in the local jet is an exact interface, not yet a sampling/interpolation rigidity theorem.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate. A declaration becomes compiler-validated project theorem authority only when its module lies in an exact successful authoritative build closure or is explicitly built by such a gate.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, theorem names must agree across

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

This docs/control sync leaves those promotion surfaces unchanged.

## Control-v2 validation law

Control v2 has no theorem/claim/terminal-answer authority. Its CI gates enforce separate theorem/control anchors, deterministic routing, fail-closed retro/first-break contracts, dead-route revival requirements and hard-coded current theorem/frontier/action smoke assertions.

The post-#163 sync must:

- advance theorem anchor to #163 / merge `bd3fa1aa...` / tree `c397b3a0...`;
- stop labeling the mixed quadratic-normal seventh-jet/Riesz coupling as open;
- remove consumed `E4A4-SCHUR-FB-04` from the selected action's live first breaks;
- make existing `E4A4-SCHUR-FB-05` the selected first break;
- preserve the firewall that nonzero explicit source moment does not imply nonzero `M4`;
- preserve the firewall that exact finite-prime sampling does not itself determine a local derivative;
- preserve the absence of an endpoint-scalar sign/nonvanishing theorem;
- keep DR-024 as a negative-control objection without a dead-route revival blocker;
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
- **LEAD / HYPOTHESIS** — motivated research route;
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only;
- **OPEN** — not established.

## Claim firewall

Green #163 mixed-source/Riesz theorems are not RH. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
