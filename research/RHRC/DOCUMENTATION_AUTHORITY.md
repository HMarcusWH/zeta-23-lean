# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to keep the repository from drifting after rapid research changes.

## Authority order

When two sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — `CLAIM_REGISTRY.json`, `routes/ROUTE_REGISTRY.json`.
3. **Active route README** — e.g. `routes/R003_ccm_bridge/README.md`.
4. **Current external build-plan / handover SSOT**.
5. **PR-specific settlement documents**.
6. **Historical roadmaps, release audits, numerical receipts and old implementation plans**.

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
- next critical gate.

## Claim rule

Documentation may explain implications, but it may not promote a claim beyond the exact theorem surface.

RH remains OPEN until the exact terminal theorem is proved and claim-validated.
