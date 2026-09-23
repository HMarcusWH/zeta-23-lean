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

## Phase 2A

Phase 2A now normalizes the complete registered proved theorem surface without
widening theorem authority:

- `REGISTERED_THEOREM_BINDINGS.json` exactly mirrors all current
  `PROVED_UNCONDITIONAL` registered claims;
- `Zeta23/RHRC/RegisteredClaimBindings.lean` explicitly `#check`s and
  `#print axioms` for every one of those theorems;
- one `LeanDeclaration` node exists for every complete registered binding;
- exact `LeanModule DECLARES LeanDeclaration` relations use the registered
  source file/module;
- exact `LeanDeclaration PROVES RegisteredClaim` relations use the complete
  binding manifest;
- generated `THEOREM_CLAIM_MAP.json` has scope
  `ALL_PROVED_UNCONDITIONAL_REGISTERED_CLAIMS`;
- the unlinked set is required to equal the OPEN claim set exactly;
- the older `R003_PROMOTED_BINDINGS.json` and
  `Zeta23/CCM/ClaimBindings.lean` remain intact as an independently checked
  historical subset.

At the current state this means 75 proved registered claims are bound and the
three OPEN claims `C_RH`, `R001_PRIME_UPPER`, and
`R002_WINDOWED_VISIBILITY` are intentionally unbound.

Phase 2A still does **not** infer theorem dependencies from imports, emit
`USES_CONSTANT`, create claims, or promote RH. The complete binding surface is
the prerequisite for compiler-derived declaration dependency work in Phase 2B.

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

Generated products live under `research/RHRC/graph/generated/`. Phase 2A adds
`lean_declarations.jsonl` and `THEOREM_CLAIM_MAP.json`. They are
non-authoritative views and mirrors. If a generated record disagrees with an
authoritative source, the generated graph is wrong.
