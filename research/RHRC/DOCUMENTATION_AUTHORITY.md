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

A green but unmerged PR is branch evidence, not merged repository truth.

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
- dead-route and obstruction ledgers.

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

## Claim rule

Documentation may explain implications, but it may not promote a claim beyond the exact theorem surface.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
