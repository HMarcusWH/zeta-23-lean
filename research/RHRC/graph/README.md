# RHRC Repository Knowledge Graph (RHKG)

RHKG is a deterministic, derived integration layer over the repository's existing
formal, control, research, and historical authority surfaces.

**It is not a proof layer and it cannot promote mathematical claims. RH remains OPEN.**

The governing document is [CONSTITUTION.md](CONSTITUTION.md).

## Phase 1

Phase 1 provides:

- complete tracked-file census and deterministic file classification;
- trust-zone classification independent of file class;
- mechanical nodes for control objects, historical deltas, research executables,
  fixtures, and workflow definitions;
- one local `LeanModule` node for every tracked Lean source;
- import edges parsed by the shared comment-aware parser also used by the
  arithmetic firewall;
- explicit external-module targets for non-local Lean imports;
- exact normalized mirrors of `CLAIM_REGISTRY.json` and `ROUTE_REGISTRY.json`;
- entrypoint reachability views;
- unresolved/deferred semantic-work reporting;
- byte-deterministic generated outputs;
- fail-closed validation in the main RHRC suite.

Phase 1 intentionally does **not** create declaration-level theorem dependencies,
claim promotion, authority resolution, GitHub history, dead-route semantics, or
research preflight. Those belong to later constitutional phases.

## Commands

From the repository root:

```bash
python research/RHRC/graph/build.py --check
python research/RHRC/graph/validate.py
```

To regenerate after an intentional graph-affecting repository change:

```bash
python research/RHRC/graph/build.py --write
python research/RHRC/graph/validate.py
```

Generated products live under `research/RHRC/graph/generated/`. They are
non-authoritative views and mirrors. If a generated record disagrees with an
authoritative source, the generated graph is wrong.
