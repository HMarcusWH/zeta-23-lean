# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to keep the repository from drifting after rapid research changes.

## Authority order

When two sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — `CLAIM_REGISTRY.json`, `routes/ROUTE_REGISTRY.json`.
3. **Active route README** — e.g. `routes/R003_ccm_bridge/README.md`.
4. **Living research-control SSOTs** — `RESEARCH_LEADS.md` for accumulated option/status memory and `CURRENT_RESEARCH_PLAN.md` for current execution order.
5. **Current external build-plan / handover SSOT**.
6. **PR-specific settlement documents**.
7. **Historical roadmaps, release audits, numerical receipts and old implementation plans**.

The two living research-control SSOTs have different scopes and must not be used to overrule theorem truth: the lead ledger records hypotheses and research state; the current plan records priority and dependency decisions.

A green but unmerged PR is branch evidence, not merged repository truth.\n\nA merged source file is also not automatically theorem authority: compiler validity attaches only to declarations in the exact successful import/build closure or a module separately built by an authoritative gate.

## Document classes

### Living SSOTs

These must be updated when the underlying state changes:

- root `README.md`;
- `FORK_NOTES.md`;
- `AUDIT.md`;
- `research/RHRC/README.md`;
- claim/route registries;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- dead-route and obstruction ledgers;\n- `research/RHRC/VALIDATION_PROTOCOL.md` when validation semantics or gates change.

### Historical settlements

PR-specific settlement and dated audit files record what was known at that time. Do not rewrite their mathematical history merely to make them look current.

If necessary add a short banner:

```text
HISTORICAL SETTLEMENT
Current authority: live Lean/CI + registries + active route README.
```

### Immutable provenance snapshots

Do not rewrite:

- `UPSTREAM_BASELINE.json`;
- pinned external source/reference manifests;
- numerical receipts;
- historical normalization locks.

Create a new versioned object if current semantics need a new machine-readable map.

## Theorem-state anchors in living documents

A living documentation PR cannot know its own future merge SHA. Therefore living prose must not create an endless docs-only hash chase.

When recording repository state in living documents:

- use **live GitHub main** as the authoritative current head;
- record the last meaningful theorem-bearing merge as a **theorem-state anchor**;
- record its validated theorem tree when useful;
- do not open a follow-up PR merely to replace the anchor with the SHA of a docs-only merge;
- advance the theorem-state anchor when theorem/claim state materially changes.

Example:

~~~text
theorem-state anchor = PR #<theorem-bearing PR> merge <sha>
theorem tree = <tree>
live GitHub main = authoritative
~~~

Machine registries and compiler/CI evidence still outrank the prose anchor.

## Update triggers

After a post-green research pass, update documentation when any of these changes:

- canonical mathematical object;
- theorem status;
- dependency order;
- dead/quarantined route classification;
- source normalization or parameter convention;
- public repository identity;
- next critical gate;
- lead classification, resurrection or falsification state;
- execution priority, parallel-lane choice, route-selection gate or stop condition.

## Post-green synchronization sequence

After every meaningful green result:

1. verify exact head, theorem declarations, assumptions, axioms and CI;
2. update claim/route registries if formal truth changed;
3. update the active route README if the route state changed;
4. update RESEARCH_LEADS.md if a lead was added, promoted, blocked, falsified, superseded, resurrected or composed;
5. update CURRENT_RESEARCH_PLAN.md if execution order or a decision gate changed;
6. update the root/RHRC README when the public critical path changed;
7. leave historical settlements untouched except for an authority banner when necessary.

A green but unmerged PR remains branch evidence until merged and registered.

## Validated import-closure law

Repository presence, PR inclusion, merge inclusion and no-placeholder scanning are weaker states than Lean elaboration.

A theorem may be promoted only when its declaration is in the exact compiler-tested transitive import closure or its module was separately compiled by an authoritative successful gate. For production R003 promotion, the required `#check` / `#print axioms` surface must also be present.

PR #103 is the canonical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM`; `ParityBadness.lean` was merged but not imported.

See `VALIDATION_PROTOCOL.md`.

## Claim rule

Documentation may explain implications, but it may not promote a claim beyond the exact theorem surface.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.

## Promoted theorem-binding completeness

For R003, R003_PROMOTED_BINDINGS.json is the declared production binding surface. Every PROVED_UNCONDITIONAL R003 claim with a theorem must agree exactly across CLAIM_REGISTRY.json, R003_PROMOTED_BINDINGS.json, and the exact #check / #print axioms declarations in Zeta23/CCM/ClaimBindings.lean.

The RHRC suite enforces this through promoted_binding_lint.py. Supporting theorem checks may exist without individual registry promotion, so CI does not equate every #check with a claim; promotion intent must be declared explicitly.

## External handover transition after PR #103

The external v1.7 retirement condition has fired. PRs #100, #102 and #103 materially changed the dependency graph. Until external v2.0 is produced, living repository SSOTs control execution. External v2.0 should start from the validated post-#103 theorem state. Do not create it inside a repository PR unless explicitly requested.
