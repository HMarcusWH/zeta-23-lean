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

Phase 2A deliberately stopped before declaration-level dependency extraction.

## Phase 2B

Phase 2B adds compiler-derived declaration dependencies without widening theorem
authority:

- `Zeta23/RHRC/DeclarationDependencyExport.lean` interrogates the elaborated Lean
  environment rather than source text or module imports;
- `research/RHRC/tools/lean_dependency_extract.py` deterministically checks the
  checked-in compiler receipt against the current Lean environment;
- recursion follows the local `Zeta23` dependency closure rooted at all registered
  proved declarations, while external Lean/Mathlib constants are retained as
  auditable boundary nodes and are not recursively expanded;
- `LeanDeclaration` is generalized into `REGISTERED_CLAIM_ROOT`,
  `LOCAL_DEPENDENCY`, and `EXTERNAL_BOUNDARY` graph roles;
- exact `LeanDeclaration USES_CONSTANT LeanDeclaration` relations use
  `LEAN_ENV_EXACT` provenance and distinguish use in declaration type, value/proof
  body, and structural declaration metadata;
- `THEOREM_DEPENDENCY_CLOSURE.json` exposes direct/transitive registered-root
  dependency closures for research queries.

`IMPORTS` remains module availability and is not treated as `USES_CONSTANT`.
Dependency-only declarations cannot receive `PROVES` edges. Genuine
expression-level self dependencies are retained when the compiler reports them;
structural self-membership bookkeeping is not promoted into a usage edge.

A materialized Phase 2B state requires the checked-in compiler receipt to match a
fresh extraction from the pinned Lean environment and all generated graph products
to be byte-current. The bootstrap-pending marker is transitional only and is not a
valid steady state.

The materialized receipt currently records **75 registered roots**, **3,064 local
dependency declarations**, and **4,425 external-boundary declarations**: **7,564
declarations total** with **270,951 exact declaration dependency relations**. The
first sealed extraction completed the Lean exporter in 126.71 seconds; Python
receipt parsing took 0.40 seconds. These are measured properties of the current
receipt, not theorem counts beyond the registered-root authority surface.

External compiler-boundary modules are tracked separately from syntactic Lean
`IMPORTS` targets. A declaration dependency on a constant from an external module
does not imply that a local source file directly imports that module.

The graph remains a derived integration layer and **RH remains OPEN**.

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

Generated products live under `research/RHRC/graph/generated/`. Phase 2B adds
`THEOREM_DEPENDENCY_CLOSURE.json`; the compiler-derived receipt lives separately
under `research/RHRC/graph/compiler/` and is checked by Lean CI before RHKG
consumes it. Generated graph products remain non-authoritative views and mirrors.
If a generated record disagrees with an authoritative or compiler-derived source,
the generated graph is wrong.
