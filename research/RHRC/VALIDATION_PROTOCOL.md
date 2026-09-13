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
latest theorem-bearing PR = #159
merged theorem-bearing main = 63862cd80501754c6c6599ffea09b874a327dae4
validated theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #159 validated PR head and merged main are different commit objects but share theorem tree `cb7a81d3...`. PR #117 remains the Control-v2 semantic authority because #159 changes mathematical state, not controller capability/authority semantics.

## Exact #159 gate evidence

At validated theorem head `b2a064ad5d1f0acbd93309a9257c5661cfa3ec28`, RHRC workflow run #1021 (`34736245287`) completed successfully. Permansson workflow run #794 (`34736245311`) also completed successfully.

The authoritative closure includes `python-rhrc`, R003 normalization audit, aggregate CCM/ExceptionalZero Lean builds, forbidden-placeholder/project-axiom scan and Permansson.

## What #159 validates

The new modules are imported through `Zeta23.CCM` and therefore lie in the authoritative aggregate build closure.

### Production moment-prefix jets

Validated declarations include:

```text
iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
```

Thus the exact seventh and even ninth self-energy leading-moment formulas are theorem authority. They are no longer DERIVED/OPEN.

### Signed Riesz boundary recurrence

Validated declarations include:

```text
canonicalPolePrimeRieszEndpointScalar
canonicalPolePrimeRieszBoundaryTerm
canonicalPolePrimeRiesz_integral_step_with_boundary
canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
canonicalPolePrimeRieszBoundaryTerm_six_eq_moment_three
canonicalPolePrimeRieszBoundaryTerm_eight_eq_moment_four_of_even
canonicalRieszSourceChannelEnergy_six_eq_seven_sub_moment_three
canonicalRieszSourceChannelEnergy_eight_eq_nine_add_moment_four
```

No sign of the endpoint scalar is validated. The complete-channel recurrence retains the archimedean and scalar terms exactly.

### Retained first-bad boundary state

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate.rieszSix_eq_rieszSeven_sub_momentThree
RegularCellMinimalNegativeEnergyCertificate.rieszSeven_lt_momentThreeBoundary
RegularCellMinimalNegativeEnergyCertificate.rieszEight_eq_rieszNine_add_momentFour_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszNine_lt_neg_momentFourBoundary_of_even
```

R8/R9 remains conditional on even first-bad parity.

## What remains outside theorem authority after #159

```text
same-state composition of shifted negative secular trial with #159 Riesz boundary and cross-parity source transfer
negative eigenmode -> ParityBad converse wrapper as a named theorem
first-bad arbitrary-parity predecessor-nonnegativity convenience method
opposite-parity-bad OR explicit-source-moment-nonzero retained obstruction
mixed quadratic-normal source-pairing seventh jet = constant * M4
independent contradiction-producing complete arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The existing component theorems for cross-parity source transfer and explicit source-moment decomposition remain valid, but their post-#159 same-state composition is not automatically theorem authority until separately packaged and compiled.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate. A declaration becomes compiler-validated project theorem authority only when its module lies in an exact successful authoritative build closure or is explicitly built by such a gate.

## Axiom inspection

Production-promoted R003 bindings require exact `#check` and `#print axioms` alignment across claim surfaces. The accepted production foundation is `[propext, Classical.choice, Quot.sound]`; no production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without becoming machine-promoted claims. #159 advances compiler theorem authority beyond the current machine-promoted claim-ID surface.

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

The post-#159 sync must:

- advance theorem anchor to #159 / merge `63862cd...` / tree `cb7a81d3...`;
- stop labeling the generic Riesz boundary recurrence and seventh/ninth self-energy formulas as open;
- keep FB-04 and FB-05 as the selected action's live first breaks;
- retarget FB-04 toward same-state shifted Riesz x cross-parity source composition and falsification;
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

Green #159 moment jets and signed Riesz boundary identities are not RH. A contradiction still requires new arithmetic mathematics on the exact forced state, negative-root exclusion and the terminal zeta/Mathlib seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
