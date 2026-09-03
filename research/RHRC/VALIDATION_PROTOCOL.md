# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, PR head, exact synthetic merge checked by GitHub Actions, theorem tree, eventual merged-main commit/tree, and Lean version.

Compiler validity attaches only to the exact object actually checked.

## Authoritative repository gates

Current gates include:

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

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 is the canonical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source.

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

After every meaningful green result: verify exact evidence; read the proof; compare history; analyze upstream/downstream implications; revisit dead routes; falsify clues; then synchronize registries, active route README, RESEARCH_LEADS, CURRENT_RESEARCH_PLAN and public summaries.

Historical settlements and provenance snapshots remain historical.

## Claim firewall

Green supporting mathematics, source interfaces, finite nesting, parity geometry and numerical agreement are not RH.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
