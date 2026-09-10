# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, PR head, exact object checked by GitHub Actions, theorem tree, eventual merged-main commit/tree, and Lean version where relevant.

For control-only PRs record the exact control head/merge tree separately from the last theorem-bearing anchor. A control-only green must not advance theorem authority.

Compiler validity attaches only to the exact object actually checked.

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

`run_suite.py` also executes FFBBP and Control-v2 regression tests. These tests guard research-control semantics; they do not grant theorem authority to FFBBP or Control v2.

## Current theorem/control validation anchors

```text
theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #142 validated theorem head and merged main have the same tree. PR #117 remains the latest Control-v2 semantic authority because #142 changes mathematical state, not the controller capability/authority model.

## Exact #142 gate evidence

At validated theorem head `23d96af9aafd86ad26ae7913c3d6c14503d539de`, RHRC workflow run #889 (`34415009760`) completed successfully. Its jobs include the repository claim/regression suite, Control-v2 real-history smoke, normalization/source firewalls, aggregate Lean builds and forbidden-placeholder/project-axiom checks.

The authoritative aggregate targets are:

```text
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
```

The exact #142 umbrella imports include `CanonicalApertureContinuity` in `Zeta23.CCM` and `FixedCellWitnessPersistence` in `Zeta23.ExceptionalZero`, so those declarations lie in the validated build closure.

Permansson workflow run #662 (`34415009766`) also completed successfully on the same theorem head.

The new endpoint axiom prints expose only the accepted standard axiom surface (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` appeared in the checked endpoint output.

## What #142 validates

Compiler-validated theorem authority includes the #140 aperture-freedom/regularity scaffold and now additionally:

```text
Zeta23.CCM.continuousOn_canonicalSourceMatrix_apply_fixedCell
Zeta23.CCM.continuousOn_re_canonicalSourceQuadraticForm_fixedCell
Zeta23.CCM.exists_open_fixedCell_negativeCanonicalSourceWitness_persistence

Zeta23.ExceptionalZero.eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
Zeta23.ExceptionalZero.eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_exists_offLine_zero
```

The exact proof also theorem-locks the real regularized primitive identities used to obtain continuity, including:

```text
Zeta23.CCM.regularizedArchScale_eq_mul_archDensity
Zeta23.CCM.alphaL_eq_regularized_integral
Zeta23.CCM.betaL_eq_regularized_integral
Zeta23.CCM.regularizedSourceEq411LhsIntegrand_eq
```

These are **real-axis regularized integral identities and continuity theorems**. They do not validate complex analyticity, the later `x=L t` fixed-unit-interval reformulation, determinant nonidentity, dense regularity, successor positivity, negative-root exclusion, or RH.

The fixed-unit-interval rescaled formulas discussed in the post-#142 research pass are currently **DERIVED**, not merged declarations. High-precision comparison of those rescaled formulas is **EXPERIMENTAL SIGNAL**, not theorem authority.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 remains the canonical historical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source until a later build closure consumed it.

Current example: PR #142 wires `CanonicalApertureContinuity.lean` into `Zeta23.CCM` and `FixedCellWitnessPersistence.lean` into `Zeta23.ExceptionalZero`; both umbrella targets passed the exact-head build.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may also carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. PR #142 prints axioms for its continuity/persistence headline theorems; this does not by itself promote them into `CLAIM_REGISTRY.json`.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, exact theorem names must agree across:

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

`promoted_binding_lint.py` enforces set equality, theorem-name equality, and exact #check/#print-axioms presence.

Compiler-PROVED theorem authority beyond the current machine-promoted claim list must not be silently upgraded to `PROVED_UNCONDITIONAL` registry status. PR #142 is another example of theorem authority advancing without a corresponding automatic machine-claim promotion.

## Control-v2 validation law

`research/RHRC/control_v2/` is diagnostic research infrastructure only. Its CI gates enforce:

- no theorem/claim/terminal-answer authority;
- separate theorem and control-plane anchors;
- deterministic route certificates and score diagnostics;
- deterministic retro receipt hashes;
- fail-closed missing retro-search / first-break requirements;
- dead-route revival records when explicitly required;
- `as_of` Git replay that cannot see future commits;
- external time-travel replay that requires availability metadata;
- retro receipts bound to their declared Git search paths;
- exact sorted contiguous finite-prefix coverage for deformation budgets;
- no `PRUNE` from a numeric tail without a passed horizon certificate targeting the remaining deformation budget;
- no decision-bearing reduced-model `PRUNE` without decision commutation when that gate is required;
- no promotion from diagnostic commutation to decision commutation;
- no horizon certificate from a small local residual alone.

A Control-v2 recommendation is **not** a theorem, claim promotion, RH evidence, or a substitute for Lean.

## Vocabulary

- **source present** — file exists.
- **module compiles** — Lean elaborated that module.
- **umbrella build green** — named target and transitive imports compiled.
- **PR green** — all required gates for the exact PR object succeeded.
- **PROVED** — exact statement compiler-validated with acceptable axiom surface.
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface.
- **DERIVED** — mathematical consequence not separately theorem-locked.
- **LOCAL LEAN CHECK** — standalone/local compilation evidence outside merged theorem authority.
- **LEAD / HYPOTHESIS** — motivated research route.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — not established.

## Post-green synchronization

After every meaningful green result: verify exact evidence; read the proof/control result; compare history; analyze upstream/downstream implications; revisit dead routes; falsify clues; then synchronize registries, active route README, research-lead deltas, `CURRENT_RESEARCH_PLAN`, `VALIDATION_PROTOCOL` and public summaries.

Historical settlements and provenance snapshots remain historical.

A post-green sync must not rewrite a large historical ledger merely to manufacture currentness when the documentation law permits a new dated delta to supersede it. In that case, the living README/plan/route/control documents must point to the new delta explicitly.

## Claim firewall

Green supporting mathematics, aperture freedom, fixed-cell continuity, witness persistence, regularity interfaces, source normalization, finite nesting, parity geometry, determinant reductions, research-control recommendations, budget diagnostics and numerical agreement are not RH.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
