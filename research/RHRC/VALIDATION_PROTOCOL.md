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
theorem-state anchor = PR #153 merge 474a88d76ecd2f4eee6178685b2e8d8b104171ca
validated theorem head = b6622dadab911008c0a7238e9dc711c6f9946302
validated theorem tree = dd69f1c612047f2d2f15a7ba158664634284b42e
RHRC #994 / run 34709905190 = SUCCESS
Permansson #767 / run 34709905198 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #153 validated theorem head and merged main have the same tree `dd69f1c...`. PR #117 remains the Control-v2 semantic authority because #153 changes mathematical state, not controller capability/authority semantics.

## Exact #153 gate evidence

At validated theorem head `b6622dadab911008c0a7238e9dc711c6f9946302`, RHRC workflow run #994 (`34709905190`) completed successfully.

Successful RHRC jobs:

```text
python-rhrc
r003-normalization-audit
lean
```

The `lean` job successfully completed:

```text
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden placeholder/project-axiom scan
```

The normalization job successfully reran:

```text
cutoff-free CCM normalization lock
finite dictionary external-oracle guards
source-normalization semantic firewall
post-#150 selected-residual certification plumbing
post-#150 selected-residual scope scout
checked-in interval-certificate replay
R004 scalar-shift invariant audit
external-reference dependency firewall
```

Permansson workflow run #767 (`34709905198`) also completed successfully on the same theorem head, including `Reject placeholders and extra axioms`.

## What #153 validates

The #153 modules lie inside the authoritative `Zeta23.CCM` / `Zeta23.ExceptionalZero` aggregate build closure.

### Retained cell-minimal first-bad certificate

Validated declarations include:

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalFirstBadCertificate.L_pos
exists_regular_cellMinimal_firstBadCertificate
exists_regular_cellMinimal_firstBad
```

The structure retains the whole-cell minimality premise as well as the selected-aperture projection.

### Retained negative-energy certificate

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate
exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
exists_regular_cellMinimal_negativeCanonicalEnergy
```

The retained state includes predecessor nonnegativity, the exact negative explicit root equation, the unique preimage equation `A x0=b`, and strict parity/channel energy negativity.

### ExceptionalZero propagation

Validated declarations include:

```text
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero
```

Thus a hypothetical off-line zero now reaches the richer first-class certificate without discarding the whole-cell ancestry.

### Smooth source-atom layer

Validated declarations include:

```text
sourceAtomRealEnergy
sourceAtomRealEnergy_zero
contDiff_sourceEntry
contDiff_sourceAtomRealEnergy
```

This validates smoothness of the exact source-atom energy in the source coordinate. It does not validate high-order endpoint vanishing.

### Pole/source derivative-integral bridge

Validated declarations include:

```text
dictionaryPoleRHS_basis_eq_sourceEntry_integral
canonicalPoleMatrix_apply_eq_sourceEntry_integral
matrixRealEnergy_canonicalPoleMatrix_eq_integral_sourceAtom
matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral
```

### Finite prime cumulative derivative-integral bridge

Validated declarations include:

```text
canonicalPrimeCumulativeWeight
canonicalPoleCumulativeWeight
matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral
```

### Exact finite discrepancy normal form

Validated declarations include:

```text
canonicalPolePrimeDiscrepancy
canonicalPolePrimeDiscrepancyEnergy
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy
```

This is the exact production pole-minus-prime cancellation theorem. No infinite series/distribution interchange is required by the exported identity.

## Current theorem surface does not validate

```text
actual maximal endpoint-jet order of sourceAtomRealEnergy under boundary-flat constraints
historical suggested order-seven generic source-energy zero
historical suggested order-nine even-parity source-energy zero
sixth/eighth-order Riesz-smoothed discrepancy identities
generic repeated-IBP theorem instantiated to the selected state
sign of the transformed discrepancy pairing
regular selected-residual nonnegativity Ecanonical(c-x0)>=0
canonical one-step domination
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

Some items remain DERIVED research leads; none should be labeled PROVED merely because the old symbolic expansion suggested them.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 remains the canonical historical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source until a later build closure consumed it.

Current example: the #153 certificate/discrepancy modules are imported through the CCM/ExceptionalZero umbrellas and were validated by the exact #153 green aggregate build.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. PR #153 advances compiler theorem authority beyond the current machine-promoted claim-ID surface.

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

The post-#153 sync must therefore update the exact Control-v2 theorem anchor to #153, treat FB-01 and FB-02 as completed theorem prerequisites, and rewrite FB-03 as endpoint-jet discovery plus generic repeated integration by parts without presupposing order seven/nine.

The selected top-level action remains `E4_A4_REGULAR_SCHUR_ENERGY_SIGN`. Control v2 may still choose FB-04 as the cheapest decisive falsifier; that routing decision is distinct from the chronological theorem dependency that FB-03 must provide before a transformed FB-04 claim can be tested.

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

Green retained-certificate infrastructure and the exact finite discrepancy identity are not RH. A contradiction still requires an independent nonnegative sign on the exact same forced state, then negative-root exclusion and the terminal statement seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
