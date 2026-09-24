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


## Phase 2C

Phase 2C consumes the exact Phase-2B compiler closure as a **research-analysis
surface**. It does not add Lean theorem authority.

`DEPENDENCY_FARMING_COHORTS.json` defines deterministic route selectors and
explicit proved-root cohorts. Every explicit member must resolve to the complete
registered `PROVED_UNCONDITIONAL` binding surface; OPEN or unknown claims fail
closed.

The generated research views are:

- `DEPENDENCY_KERNEL_ATLAS.json`: project-local declarations annotated by the
  registered roots and research cohorts that reach them;
- `DEPENDENCY_COHORT_OVERLAP.json`: exact cohort unions, intersections,
  per-member subtraction shells, pairwise overlaps, and exact set containments;
- `DEPENDENCY_SIGNATURE_CLASSES.json`: SHA-256 fingerprints of sorted local
  dependency closures, exact-equal closure classes, and strict closure
  containments.

The analysis deliberately separates the project-local kernel from external
Mathlib/Lean boundaries. Shared dependencies, equal closures, set containment,
high reach, and cohort membership are structural facts about the checked proof
implementation; none imply theorem equivalence, logical implication, mathematical
importance, or claim promotion.

A read-only query surface is available:

```bash
python research/RHRC/tools/query_dependencies.py --claim R001_PRIME_UPPER_EQUIV_RH
python research/RHRC/tools/query_dependencies.py --compare \
  R001_PRIME_UPPER_EQUIV_RH \
  AUDIT_GLOBAL_BOTTOM_RESIDUAL_EXCLUSION_RH_EQUIVALENCE
python research/RHRC/tools/query_dependencies.py --intersect RH_EQUIVALENCE_SURFACE
```

The primary Phase-2C research question is whether differently presented
RH-equivalent results share a nontrivial project-local dependency kernel after
their theorem-specific shells are subtracted. A negative result is informative:
it falsifies the naive implementation-level common-kernel hypothesis.

**RH remains OPEN.**

## Phase 2D

Phase 2D quotients the exact Phase-2C RH-equivalence dependency surface rather
than adding another theorem layer.

It fixes the current target cohort to the three proved RH-equivalent roots and
partitions their **root-excluding** project-local dependency closures into exact
membership atoms `A/B/C/AB/AC/BC/ABC`.

The generated products are:

- `DEPENDENCY_COHORT_ATOMS.json`: exact Venn-style dependency atoms;
- `DEPENDENCY_KERNEL_QUOTIENT.json`: factual module/kind/visibility profiles of
  those atoms;
- `DEPENDENCY_BRIDGE_FRONTIERS.json`: exact compiler `USES_CONSTANT` edges
  crossing atom boundaries, plus a separate containment-frontier probe from the
  global-bottom arithmetic residual back into the canonical prime-remainder
  normal-form substrate.

The compiler edge direction is always

```text
source declaration -> used constant
```

and is never reversed for narrative convenience.

Registered theorem-root endpoints are excluded from the
`bridge_candidate_eligible` subset. That subset is a discovery filter only; a
frontier edge is not a theorem implication and a small frontier is not a proof
that one missing lemma closes the mathematics.

The frozen research receipt
`research/RHRC/receipts/RHKG_POST259_KERNEL_FIRST_CONTACT_2026_09_24.json`
preserves the merged #259 first-contact counts and source Git objects without
turning those historical measurements into live theorem authority.

Additional read-only queries:

```bash
python research/RHRC/tools/query_dependencies.py --atoms RH_EQUIVALENCE_SURFACE
python research/RHRC/tools/query_dependencies.py --frontier RH_EQUIVALENCE_SURFACE
python research/RHRC/tools/query_dependencies.py --path \
  AUDIT_GLOBAL_BOTTOM_RESIDUAL_EXCLUSION_RH_EQUIVALENCE \
  Zeta23.CCM.canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
```

The Phase-2D research question is no longer merely whether a common kernel
exists. It asks where theorem-specific dependency shells attach to shared
structure and where the live global-bottom arithmetic endpoint first crosses
into the canonical prime-remainder substrate.

**RH remains OPEN.**

## Phase 2E

Phase 2E asks whether the Phase-2C/2D shared dependency structure survives when
the graph stops traversing theorem VALUE bodies.

The compiler receipt is unchanged. Phase 2E derives four deterministic traversal
projections from the exact `used_in_type`, `used_in_value`, and
`used_in_structure` flags already sealed by Phase 2B:

- `ANY`: the existing Phase-2D traversal over every compiler dependency edge;
- `TYPE_ONLY`: homogeneous traversal over TYPE edges only;
- `VALUE_ONLY`: homogeneous traversal over VALUE edges only;
- `THEOREM_VALUE_ERASED_SUPPORT`: TYPE and STRUCTURE edges are always followed,
  while VALUE edges are followed only when the source declaration is not a
  `THEOREM`.

The last projection is deliberately named narrowly. It erases traversal through
Lean theorem proof bodies while retaining definitional VALUE bodies needed by
the support graph. It is **not** a semantic dependency graph, a statement-meaning
graph, or a logical implication graph.

The generated products are:

- `DEPENDENCY_PROJECTION_SUMMARY.json`: count/hash summaries for all 75 proved
  registered roots and all existing farming cohorts;
- `DEPENDENCY_PROJECTION_QUOTIENTS.json`: exact A/B/C quotient atoms for the
  existing `RH_EQUIVALENCE_SURFACE` under each projection;
- `DEPENDENCY_PROJECTION_FRONTIERS.json`: exact projected cross-atom frontiers
  and a neutral `LEFT_ONLY / RIGHT_ONLY / SHARED` comparison of the canonical
  prime-remainder and global-bottom arithmetic closures.

The `ANY` projection is a regression baseline and must reproduce the sealed
Phase-2D results exactly. Other projections are allowed to change containment
relations; the pair comparison therefore reports one of `EQUAL`,
`LEFT_STRICT_SUBSET`, `RIGHT_STRICT_SUBSET`, or `INCOMPARABLE` rather than
assuming the Phase-2D strict containment survives.

Read-only queries accept an optional projection:

```bash
python research/RHRC/tools/query_dependencies.py \
  --claim R001_PRIME_UPPER_EQUIV_RH \
  --projection THEOREM_VALUE_ERASED_SUPPORT

python research/RHRC/tools/query_dependencies.py \
  --atoms RH_EQUIVALENCE_SURFACE \
  --projection THEOREM_VALUE_ERASED_SUPPORT

python research/RHRC/tools/query_dependencies.py \
  --frontier RH_EQUIVALENCE_SURFACE \
  --projection VALUE_ONLY
```

Omitting `--projection` preserves the existing `ANY` behavior.

Phase 2E remains research-only. A small projected frontier is not a missing
theorem, a large projected frontier does not falsify an RH route, and no
projection can promote a registered claim.

**RH remains OPEN.**

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
`THEOREM_DEPENDENCY_CLOSURE.json`; Phase 2C adds the dependency kernel atlas,
cohort-overlap view, and signature classes; Phase 2D adds dependency atoms,
kernel quotient, and bridge frontiers; Phase 2E adds dependency projection
summaries, quotients, and frontiers. The compiler-derived receipt lives separately
under `research/RHRC/graph/compiler/` and is checked by Lean CI before RHKG
consumes it. Generated graph products remain non-authoritative views and mirrors.
If a generated record disagrees with an authoritative or compiler-derived source,
the generated graph is wrong.


## Final semantic-closure pass

The repository-accounting closure layer adds three deterministic products:

- `lean_source_declarations.jsonl` — a source-navigation census of named Lean
  declaration commands across every local Lean module;
- `MODULE_SEMANTIC_CLOSURE.json` — one entry for every local Lean module,
  including explicit dispositions for every module outside the declared
  entrypoint closures;
- `DOCUMENT_SEMANTIC_CLOSURE.json` — one entry for every
  `DOCUMENTATION`/`LIVING_SSOT` file, with document role and exact textual
  claim/route navigation hints.

The source-declaration surface is intentionally separate from the exact compiler
dependency surface. It makes potentially forgotten source declarations
discoverable, but only the sealed compiler receipt may generate
`LeanDeclaration USES_CONSTANT LeanDeclaration` edges.

Document `MENTIONS` edges use `TEXTUAL_HINT` provenance and carry no
mathematical authority.

The generated unresolved report now distinguishes closed repository accounting
from deeper semantic work that remains optional/future. RH remains OPEN.
