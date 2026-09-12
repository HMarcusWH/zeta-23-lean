# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, exact PR head checked by GitHub Actions, theorem tree, eventual merged-main commit/tree and relevant compiler version/toolchain.

Compiler validity attaches only to the exact object actually checked. A control/docs-only green must not create theorem authority.

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

A skipped downstream step is not a passed gate.

`run_suite.py` also executes FFBBP and Control-v2 regression tests. Those guard research-control semantics; they do not grant theorem authority to the controller.

## Current theorem/control validation anchors

```text
theorem-state anchor = PR #150 merge fb92d5749d6f7a65cfc9129d49d8213219c059db
validated theorem head = b1be9eca5f544d4356ea88089c0f7264f75d2220
validated theorem tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8
RHRC #971 / run 34690959720 = SUCCESS
Permansson #744 / run 34690959699 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #150 validated theorem head and merged main have the same tree `999ef44d...`. PR #117 remains the Control-v2 semantic authority because #150 changes mathematical state, not controller capability/authority semantics.

## Exact #150 gate evidence

At validated theorem head `b1be9eca5f544d4356ea88089c0f7264f75d2220`, RHRC workflow run #971 (`34690959720`) completed successfully.

Successful jobs:

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
R004 scalar-shift invariant audit
external-reference dependency firewall
```

Permansson workflow run #744 (`34690959699`) also completed successfully on the same theorem head.

## What #150 validates

The #150 modules lie inside the authoritative `Zeta23.CCM` / `Zeta23.ExceptionalZero` aggregate build closure.

### Full frozen source holomorphy

Validated declarations include:

```text
complexFrozenSourceDomain
isOpen_complexFrozenSourceDomain
analyticOnNhd_complexFrozenCanonicalPrimeMatrix_apply_sourceDomain
complexPoleQuadraticDenominator_ne_zero
analyticOnNhd_complexCanonicalPoleMatrix_apply_sourceDomain
analyticOnNhd_complexApertureScalarRemainder_sourceDomain
analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
```

### Intrinsic predecessor / log-cover holomorphy

Validated declarations include:

```text
analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
liftedFrozenPredecessorDomain
isOpen_liftedFrozenPredecessorDomain
add_two_pi_I_mem_liftedFrozenPredecessorDomain_iff
analyticOnNhd_liftedFrozenIntrinsicPredecessorRemainder_coord
analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
```

### Algebraic determinant rigidity

Validated declarations include:

```text
exists_nat_det_sub_smul_id_ne_zero
liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
liftedFrozenIntrinsicPredecessor_det_not_identically_zero
```

This nonidentity result is algebraic and independent of analytic continuation.

### Analytic determinant / regular-aperture selection

Validated declarations include:

```text
liftedFrozenRigidityDomain
isPreconnected_liftedFrozenRigidityDomain
liftedFrozenRigidityDomain_subset_liftedFrozenPredecessorDomain
analyticOnNhd_liftedFrozenIntrinsicPredecessorMatrix_apply
analyticOnNhd_liftedFrozenIntrinsicPredecessorDet
exists_mem_liftedFrozenRigidityDomain_det_ne_zero
liftedFrozenIntrinsicPredecessorDet_not_zero_on_rigidityDomain
exists_intrinsicPredecessorRegular_in_open_fixedCell
```

The exact regularity theorem states that every nonempty open real interval inside one physical cutoff cell contains a regular actual predecessor aperture.

### Cell-minimal regular first-bad / exact energy

Validated declarations include:

```text
CellAnyParityBad
exists_least_cellAnyParityBad_two_le
not_anyParityBad_of_lt_cellMinimal
exists_regular_cellMinimal_firstBad
exists_regular_cellMinimal_negativeCanonicalEnergy
```

### ExceptionalZero closure

Validated declarations include:

```text
exists_fixedCanonicalCutoffCell_point_above
exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero
```

These declarations establish the current formal endpoint:

```text
off-line zero
  -> finite actual-production regular selected state
  -> unique zero-shift preimage
  -> exact canonical source-channel energy < 0.
```

They do not prove the opposing nonnegative sign.

## Current theorem surface does not validate

```text
selected predecessor positive-definite as a separately named theorem
simultaneous regularity of all smaller predecessor blocks / both parities
full first-bad ancestry retained through the outer energy wrapper
post-#150 pole-minus-prime discrepancy identity
boundary-flat Taylor annihilation through order six/eight as dedicated declarations
Riesz-smoothed discrepancy identities
regular selected-residual nonnegativity Ecanonical(c-x0)>=0
canonical one-step domination
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

Some of these are DERIVED consequences or research leads; none should be labeled PROVED merely because the construction suggests them.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 remains the canonical historical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source until a later build closure consumed it.

Current example: the #150 source/predecessor/determinant/regularity/cell-minimal modules are imported through the CCM/ExceptionalZero umbrellas and were validated by the exact #150 green aggregate build.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. PR #150 is another example of compiler theorem authority advancing beyond the current machine-promoted claim-ID surface.

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

The post-#150 sync must therefore update the exact Control-v2 theorem anchor to #150, retire the completed regular-aperture action from the routable set, and select the existing `E4_A4_REGULAR_SCHUR_ENERGY_SIGN` action. These are routing facts, not theorem claims.

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

Green regularization infrastructure, determinant rigidity, open-interval regularity, cell-minimal selection and exact negative canonical energy are not RH. A contradiction still requires independent arithmetic nonnegativity on the exact forced state, then negative-root exclusion and the terminal statement seam.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
