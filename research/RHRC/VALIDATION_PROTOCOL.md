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
theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #137 theorem head and merged main have the same theorem tree. PR #117 remains the latest Control-v2 semantic authority because later theorem PRs changed mathematical state but not the controller capability/authority model.

## Exact #137 gate evidence

At validated theorem head `64988e142590c82bd0ad43604279ede9a8e85eff`, RHRC workflow run #878 completed successfully. Its jobs included:

```text
python-rhrc                         SUCCESS
  RHRC claim and regression suite  SUCCESS
  Control v2 real-history smoke    SUCCESS

r003-normalization-audit            SUCCESS
  canonical normalization lock      SUCCESS
  dictionary/source firewalls       SUCCESS
  R004 shift-invariant audit        SUCCESS
  external-reference firewall       SUCCESS

lean                               SUCCESS
  lake build Zeta23.CCM             SUCCESS
  lake build Zeta23.ExceptionalZero SUCCESS
  forbidden-placeholder scan        SUCCESS
```

Permansson workflow run #651 also completed successfully.

The exact #137 umbrella imports include `CanonicalSourcePairing`, `CanonicalOneStepDomination`, and `GlobalFirstBadOneStepDomination`, so these declarations are in the validated build closure.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 is the canonical historical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source until a later build closure consumed it.

Current example: PR #137 wires `CanonicalSourcePairing.lean` and `CanonicalOneStepDomination.lean` into `Zeta23.CCM`, and `GlobalFirstBadOneStepDomination.lean` into `Zeta23.ExceptionalZero`. Both umbrella targets passed the exact-head build.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may also carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. PR #137 prints axioms for the headline determinant/sufficiency/global endpoint theorems, but this does not by itself promote them into `CLAIM_REGISTRY.json`.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, exact theorem names must agree across:

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

`promoted_binding_lint.py` enforces set equality, theorem-name equality, and exact #check/#print-axioms presence.

Compiler-PROVED theorem authority beyond the current machine-promoted claim list must not be silently upgraded to `PROVED_UNCONDITIONAL` registry status. PRs #112-#137 contain examples of theorem authority advancing faster than the explicit machine-promotion surface.

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
- **DERIVED** — straightforward consequence not separately theorem-locked.
- **LEAD / HYPOTHESIS** — motivated research route.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — not established.

## Post-green synchronization

After every meaningful green result: verify exact evidence; read the proof/control result; compare history; analyze upstream/downstream implications; revisit dead routes; falsify clues; then synchronize registries, active route README, research-lead deltas, CURRENT_RESEARCH_PLAN, VALIDATION_PROTOCOL and public summaries.

Historical settlements and provenance snapshots remain historical.

A post-green sync must not rewrite a large historical ledger merely to manufacture currentness when the documented authority law permits a new dated delta to supersede it. In that case, the living README/plan/route/control documents must point to the new delta explicitly.

## Claim firewall

Green supporting mathematics, source interfaces, finite nesting, parity geometry, determinant reductions, research-control recommendations, budget diagnostics and numerical agreement are not RH.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
