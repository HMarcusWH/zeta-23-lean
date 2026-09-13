# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, eventual merged-main commit/tree and relevant compiler/toolchain.

Compiler validity attaches only to the exact object actually checked. A control/docs-only green must not create theorem authority.

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

A skipped downstream step is not a passed gate.

`run_suite.py` also executes FFBBP and Control-v2 regression tests. Those guard research-control semantics; they do not grant theorem authority to the controller.

## Current theorem/control validation anchors

```text
latest theorem-bearing PR = #157
merged theorem-bearing main = e304f07c9e83165ebf066db0d67c2cc24f8961c2
validated theorem head = 4b517db1d4a50277d325e77e771a30fc0db5c777
validated theorem tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7
RHRC #1017 / run 34731682546 = SUCCESS
Permansson #790 / run 34731682544 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #157 validated PR head and merged main are different commit objects but share theorem tree `706dfde7...`. PR #117 remains the Control-v2 semantic authority because #157 changes mathematical state, not controller capability/authority semantics.

## Exact #157 gate evidence

At validated theorem head `4b517db1d4a50277d325e77e771a30fc0db5c777`, RHRC workflow run #1017 (`34731682546`) completed successfully. Permansson workflow run #790 (`34731682544`) also completed successfully.

Successful theorem-bearing closure includes:

```text
python-rhrc
r003-normalization-audit
lean
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden placeholder/project-axiom scan
Permansson independent formal verification
```

## What #157 validates

The new #157 modules are imported through `Zeta23.CCM` / `Zeta23.ExceptionalZero` and therefore lie in the authoritative aggregate build closure.

### Genuine complex production D transport

Validated declarations include:

```text
sourceEntrySecondDerivative_transport
sourceContractRealSecondDerivative_transport_with_defect
sourceContractRealSecondDerivative_transport
sourceAtomRealEnergy_eq_re_im_contracts
sourceAtomRealEnergySecondDerivative_eq_indexAction
```

This closes the prior real-to-complex implementation gap for the exact source-energy D-transport theorem. The permanent rule remains: no other real helper may be silently promoted to a complex production statement.

### Production endpoint jets

Validated declarations include:

```text
iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
iteratedDeriv_two_sourceAtomRealEnergy_eq_indexAction
iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
sourceAtomRealEnergy_boundaryFlat_jets_through_six
sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
```

Boundary-flat production carriers therefore have source-energy jets 1..6 zero. Even boundary-flat carriers have jets 1..8 zero.

### Exact complete production Riesz channel

Validated declarations include:

```text
canonicalRieszSourceChannelEnergy
canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
```

The complete transformed channel retains both reduced archimedean pieces and the scalar correction. No pointwise sign theorem is validated.

### Retained transformed-negative first-bad state

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
RegularCellMinimalNegativeEnergyCertificate.trial_evenCoefficient
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
```

Riesz-6 negativity is available on every retained certificate. Riesz-8 negativity is conditional on the retained first-bad parity being even.

### ExceptionalZero propagation

Validated declarations include:

```text
exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
exists_regularFirstBad_rieszSixNegativeCertificate_of_exists_offLine_zero
```

A hypothetical off-line zero therefore yields the complete retained Riesz-6 negative certificate.

## What remains outside theorem authority after #157

```text
independent nonnegative sign for the exact complete transformed residual
generic first Riesz boundary-term recurrence
exact seventh derivative = moment-three norm-square formula
exact ninth derivative = moment-four norm-square formula
regular selected-residual nonnegativity
canonical one-step domination
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The expected seventh/ninth coefficient formulas may be DERIVED from the current theorem inventory, but must not be labeled PROVED until exact declarations pass the authoritative build and axiom gates.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 remains the canonical historical example: a merged source file outside the validated import closure was not theorem authority until a later build consumed it.

Current example: the #157 source derivative transport, source jet, production Riesz, retained Riesz and ExceptionalZero Riesz-closure modules were imported by the aggregate targets and validated by the exact green builds.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. PR #157 advances compiler theorem authority beyond the current machine-promoted claim-ID surface.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, exact theorem names must agree across:

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

`promoted_binding_lint.py` enforces set equality, theorem-name equality and exact `#check`/`#print axioms` presence.

This docs/control sync deliberately leaves those promotion surfaces unchanged.

## Control-v2 validation law

`research/RHRC/control_v2/` is diagnostic research infrastructure only. Its CI gates enforce, among other things:

- no theorem/claim/terminal-answer authority;
- separate theorem and control-plane anchors;
- deterministic route certificates and score diagnostics;
- fail-closed missing retro-search / first-break requirements;
- exact archaeology scope and replay semantics;
- dead-route revival records when required;
- hard-coded current theorem/frontier/action smoke assertions.

The post-#157 sync must update the exact theorem anchor to #157, remove FB-03E/F from open first breaks, and make FB-04 the first live regular-Schur break.

Control v2 may rank an arithmetic falsifier cheaply, but that routing decision remains distinct from theorem authority.

## Vocabulary

- **source present** — file exists.
- **module compiles** — Lean elaborated that module.
- **umbrella build green** — named target and transitive imports compiled.
- **PR green** — all required gates for the exact PR object succeeded.
- **PROVED** — exact statement compiler-validated with acceptable axiom surface.
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface.
- **DERIVED** — mathematical consequence not separately theorem-locked.
- **LOCAL LEAN CHECK** — standalone/local compilation evidence outside merged theorem authority.
- **EXTERNAL DERIVED** — externally supplied exact/symbolic reasoning not yet repository-theoremized.
- **LEAD / HYPOTHESIS** — motivated research route.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — not established.

## Claim firewall

Green complex transport, exact production Riesz 6/8 and retained transformed negativity are not RH. A contradiction still requires an independent nonnegative arithmetic theorem on the exact same forced state, followed by negative-root exclusion and the terminal statement seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
