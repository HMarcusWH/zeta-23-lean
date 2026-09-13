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
latest theorem-bearing PR = #161
merged theorem-bearing main = ef29b45de683962122c1e898ed31bf9417757125
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #161 validated PR head and merged main are different commit objects but share theorem tree `b080572e...`. PR #117 remains the Control-v2 semantic authority because #161 changes mathematical state, not controller capability/authority semantics.

## Exact #161 gate evidence

At validated theorem head `188407fb02a37de2e380ede3b60e140953b01441`, RHRC workflow run #1026 completed successfully. Permansson workflow run #799 also completed successfully.

The authoritative closure includes `python-rhrc`, Control-v2 smoke, R003 normalization audit, aggregate CCM/ExceptionalZero Lean builds, forbidden-placeholder/project-axiom scan and Permansson.

## What #161 validates

The new modules are imported through `Zeta23.CCM` and therefore lie in the authoritative aggregate build closure.

### Spectral / first-bad interfaces

Validated declarations include:

```text
parityBad_of_negative_eigenmode
RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
```

### Shifted secular-root energy / Riesz layer

Validated declarations include:

```text
parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
cubicSecularScalar_ne_zero_of_not_parityBad
```

No sign of the Riesz endpoint scalar is validated. The R8/R9 statements are even-sector statements on the genuine shifted secular-root trial.

### Retained same-state composition

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial
RegularCellMinimalNegativeEnergyCertificate.evenSecularRoot_of_even
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNeg
RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_momentFourBoundary
RegularCellMinimalNegativeEnergyCertificate.oddSecularScalar_eq_gamma_mul_explicitSource_of_even
RegularCellMinimalNegativeEnergyCertificate.explicitSourceMoment_ne_zero_of_even_of_not_oddBad
RegularCellMinimalNegativeEnergyCertificate.oddBad_or_explicitSourceMoment_ne_zero_of_even
```

The proof does not identify the retained zero-shift trial with the shifted secular trial. It reconstructs the retained explicit root as a genuine even secular root through an eigenmode proposition and then composes theorem-backed interfaces on the same shifted state.

## What remains outside theorem authority after #161

```text
mixed quadratic-normal source-pairing seventh jet = constant * M4
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
simultaneous even/odd bad exclusion
odd-selected first-bad branch reduction/closure
independent contradiction-producing complete arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The derived odd-good consequence `Gamma != 0 AND explicitCanonicalSourceMoment != 0` is straightforward from validated #161 theorems but is not separately theorem-locked unless added later.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate. A declaration becomes compiler-validated project theorem authority only when its module lies in an exact successful authoritative build closure or is explicitly built by such a gate.

## Axiom inspection

Production-promoted R003 bindings require exact `#check` and `#print axioms` alignment across claim surfaces. The accepted production foundation is `[propext, Classical.choice, Quot.sound]`; no production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without becoming machine-promoted claims. #161 advances compiler theorem authority beyond the current machine-promoted claim-ID surface.

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

The post-#161 sync must:

- advance theorem anchor to #161 / merge `ef29b45d...` / tree `b080572e...`;
- stop labeling same-state shifted Riesz x cross-parity source composition as open;
- keep FB-04 and FB-05 as the selected action's live first breaks;
- retarget FB-04 toward mixed quadratic-normal source / M4 theoremization and falsification;
- retain the new firewall that nonzero explicit source moment does not imply nonzero `M4`;
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

Green #161 same-state Riesz/source theorems are not RH. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
