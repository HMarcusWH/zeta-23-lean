# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, PR head, exact synthetic merge checked by GitHub Actions, theorem tree, eventual merged-main commit/tree, and Lean version.

For control-only PRs record the exact control head/merge tree separately from the last theorem-bearing anchor. A control-only green must not advance theorem authority.

Compiler validity attaches only to the exact object actually checked.

## Authoritative repository gates

Current theorem/claim gates include:

~~~text
python research/RHRC/tools/run_suite.py
R003 normalization audit / dictionary guards / source-normalization firewall
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
~~~

A skipped downstream step is not a passed gate.

`run_suite.py` also executes FFBBP and Control-v2 regression tests. These tests guard research-control semantics; they do not grant theorem authority to FFBBP or Control v2.

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 is the canonical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source. PR #115 is the current theorem-state anchor: its E1 modules are imported into the CCM/ExceptionalZero umbrella closures and the PR merged green. PR #116 is a separate merged green control-plane anchor and did not change theorem authority.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

~~~lean
#check <theorem>
#print axioms <theorem>
~~~

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, exact theorem names must agree across:

~~~text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
~~~

`promoted_binding_lint.py` enforces set equality, theorem-name equality, and exact #check/#print-axioms presence.

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
- no generic standalone alias flood as an admission-quality deformation-budget search surface;
- exact sorted contiguous finite-prefix coverage for deformation budgets;
- no `PRUNE` from a numeric tail without a passed horizon certificate targeting the remaining deformation budget;
- no decision-bearing reduced-model `PRUNE` without decision commutation when that gate is required;
- no promotion from diagnostic commutation to decision commutation;
- no horizon certificate from a small local residual alone.

A Control-v2 recommendation is **not** a theorem, claim promotion, RH evidence, or a substitute for Lean.

## FFBBP v1.6 assurance overlay

The additive `ffbbp/v16_*` modules expose newer assurance contracts. They do not rewrite `FFBBP_REFERENCE.json`, `IMPLEMENTATION_CLOSURE_OVERLAY.json`, or the qualified RUN42C profile. In particular:

- v1.6 theory does not inherit RUN42C operational qualification;
- diagnostic commutation and decision commutation are separate gates;
- horizon-bearing use requires a horizon certificate;
- witness-bearing use requires visibility, perturbation margin and masking clearance.

## Vocabulary

- **source present** — file exists.
- **module compiles** — Lean elaborated that module.
- **umbrella build green** — named target and transitive imports compiled.
- **PR green** — all required gates for the exact PR merge object succeeded.
- **PROVED** — exact statement compiler-validated with acceptable axiom surface.
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface.
- **DERIVED** — straightforward consequence not separately theorem-locked.
- **LEAD / HYPOTHESIS** — motivated research route.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — not established.

## Post-green synchronization

After every meaningful green result: verify exact evidence; read the proof/control result; compare history; analyze upstream/downstream implications; revisit dead routes; falsify clues; then synchronize registries, active route README, research-lead deltas, CURRENT_RESEARCH_PLAN and public summaries.

Historical settlements and provenance snapshots remain historical.

## Claim firewall

Green supporting mathematics, source interfaces, finite nesting, parity geometry, research-control recommendations, budget diagnostics and numerical agreement are not RH.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
