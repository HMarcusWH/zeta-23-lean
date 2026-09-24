# RHKG Phase-2C Graph Contract

**Version:** 0.5  
**Scope:** Phase-1 repository census/import graph plus complete registered theorem bindings, compiler-derived declaration dependencies, and deterministic dependency-kernel research views  
**Authority:** derived only; subordinate to the RHKG Constitution and existing RHRC sources

## 1. Stable IDs

Phase 1 uses:

- `rh:repository:HMarcusWH/zeta-23-lean`
- `rh:file:<repository path>`
- `rh:module:<Lean module name>`
- `rh:claim:<CLAIM_REGISTRY id>`
- `rh:route:<ROUTE_REGISTRY route_id>`
- `rh:decl:<fully-qualified Lean declaration name>`
- `rh:rel:<sha256(kind|source|target)>`

Concept identity is separate from Git revision identity. Subject `RepoFile`
records carry their current Git blob hash. Generated RHKG products deliberately
do not carry their own blob hash, preventing recursive self-hashing.

## 2. Node types through Phase 2C

- `Repository`
- `RepoFile`
- `LeanModule`
- `LeanDeclaration`
- `RegisteredClaim`
- `Route`
- `ControlObject`
- `HistoricalDelta`
- `ResearchExecutable`
- `Fixture`
- `WorkflowDefinition`

The last five types are mechanically projected from deterministic file classes and
carry no additional scientific interpretation.

External Lean imports are represented as `LeanModule` records with
`repository_scope = EXTERNAL`; they are not treated as local formal authority.

## 3. Relations through Phase 2C

Phase 1 structural relations remain:

- `CONTAINS`
- `LOCATED_AT`
- `IMPORTS`
- `REGISTERED_IN`
- `MIRRORS`
- `PART_OF_ROUTE`
- `GOVERNED_BY`
- `GENERATED_BY`

Phase 2A additionally emits exactly:

- `LeanModule DECLARES LeanDeclaration`
- `LeanDeclaration PROVES RegisteredClaim`

The Phase-2A declaration population is complete over the exact reviewed
`REGISTERED_THEOREM_BINDINGS.json` surface: every current
`PROVED_UNCONDITIONAL` registered claim and no OPEN claim. The frozen
`R003_PROMOTED_BINDINGS.json` surface remains an independently linted historical
subset. RHKG does not discover or promote new claims.

Phase 2B additionally authorizes `LeanDeclaration USES_CONSTANT LeanDeclaration`
with provenance `LEAN_ENV_EXACT`. `IMPORTS` remains distinct from declaration
usage. Phase 2B still MUST NOT emit semantic mathematical `DEPENDS_ON`,
`KILLS_ROUTE`, `REOPENS`, or scientific supersession edges.

## 4. Provenance

- file/module location and local imports: `GIT_EXACT`
- claim/route mirrors and memberships: `REGISTRY_EXACT`
- Phase-2A `DECLARES` and `PROVES`: `REGISTRY_EXACT`, derived only from
  the complete registered-theorem manifest plus exact claim-registry
  source/theorem/route fields.

The explicit `Zeta23/RHRC/RegisteredClaimBindings.lean` compiler surface
independently checks that every registered proved theorem name exists and exposes
its axiom printout. The historical `Zeta23/CCM/ClaimBindings.lean` surface
continues to independently protect the frozen R003 promoted subset.

Phase 2B compiler-derived declaration usage has provenance `LEAN_ENV_EXACT`
only when the checked-in compiler receipt byte-matches a fresh extraction from the
pinned Lean environment. A bootstrap marker is a transient construction state,
not a valid materialized Phase-2B steady state.

No text-mined or LLM-derived relation is emitted through Phase 2B.

## 5. Import semantics

The import parser is factored into
`research/RHRC/tools/lean_imports.py` and is consumed by both the arithmetic
firewall and RHKG. It preserves the existing first-token import-regex semantics
while stripping Lean line comments and nested block comments first. A regression
self-test runs in the RHRC suite, and the arithmetic firewall remains an
independent fail-closed consumer of the shared parser.

Module import is availability, not theorem dependency.

## 6. Coverage

Every tracked file must be represented exactly once as a `RepoFile` and receive
one deterministic file class and trust zone.

Generated products are declared explicitly. Coverage includes them, while the
subject digest excludes the generated-product domain.

Required Phase-1 invariants:

```text
unindexed files              = 0
unclassified files           = 0
duplicate graph IDs          = 0
missing relation endpoints   = 0
missing source paths         = 0

CLAIM_REGISTRY projection    = exact
ROUTE_REGISTRY projection    = exact

all local Lean files         -> LeanModule
all local import targets     -> resolvable local module
all other imports            -> explicit EXTERNAL LeanModule

generated regeneration       = byte-deterministic
registered proved declarations = all PROVED_UNCONDITIONAL claims exact
compiler receipt roots           = registered theorem bindings exact
local dependency closure          = compiler receipt exact
historical R003 subset            = R003_PROMOTED_BINDINGS exact
DECLARES projection               = exact
PROVES projection                 = exact
USES_CONSTANT projection          = compiler receipt exact
unlinked registered claims     = exactly OPEN claims
terminal claim               = RH_OPEN
graph theorem promotion      = false
```

## 7. Entrypoint reachability

Reachability is descriptive only. Phase 1 reports closure from:

- `Zeta23`
- `Zeta23.CCM`
- `Zeta23.ExceptionalZero`
- comparator roots present in the tree

A module not reached by those roots is classified
`standalone_or_auxiliary`; this does not imply irrelevance or invalidity.

## 8. Exact registry mirrors

Claim and route nodes store an exact `projection` object copied from the
authoritative JSON registry, together with:

```text
authority_role = NORMALIZED_MIRROR
source_authority = <authoritative repository path>
```

Validation compares the projection objects back to the live authoritative files.

## 9. Determinism

For the same subject file contents, declared generated-product set, class rules,
and generator version, generated bytes must be identical.

Semantic outputs contain no generation timestamp and do not depend on network
access.

## 10. Claim firewall

RHKG reports repository structure. It does not create theorem authority.

**RH remains OPEN.**


## 11. Phase-2A complete registered theorem authority

`REGISTERED_THEOREM_BINDINGS.json` is the complete Phase-2A binding authority.
It must be exactly equal to the set of current registered claims with
`status = PROVED_UNCONDITIONAL`, carrying the exact registered theorem, source,
and route where present.

For every complete binding, RHKG requires:

- an existing `PROVED_UNCONDITIONAL` registered claim;
- exact theorem/source/route equality between manifest and claim registry;
- an indexed local Lean source from the claim registry;
- one `LeanDeclaration` node;
- one exact `DECLARES` edge from that source module;
- one exact `PROVES` edge to the registered claim;
- explicit `#check` and `#print axioms` coverage in
  `Zeta23/RHRC/RegisteredClaimBindings.lean`.

The frozen `R003_PROMOTED_BINDINGS.json` and
`Zeta23/CCM/ClaimBindings.lean` remain intact as an independently checked
historical subset. Each declaration record marks whether it belongs to that
historical R003 surface.

The generated `THEOREM_CLAIM_MAP.json` must therefore bind all and only the
current proved registered claims. Its unlinked set must be exactly the OPEN claim
set. At this state that set is:

- `C_RH`
- `R001_PRIME_UPPER`
- `R002_WINDOWED_VISIBILITY`

An unlinked OPEN claim is not a graph error. Binding one of these as proved is.

Repository-wide declaration census beyond the compiler-reachable closure remains
deferred. Phase 2B only follows local `Zeta23` dependencies rooted at the complete
registered proved theorem surface; external dependencies terminate at explicit
boundary declarations.

**RH remains OPEN.**


## 12. Phase-2B compiler-derived declaration dependencies

The checked-in compiler receipt is
`research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl`.
It is derived from the pinned Lean environment by
`Zeta23/RHRC/DeclarationDependencyExport.lean` and
`research/RHRC/tools/lean_dependency_extract.py`.

For every compiler-reachable declaration, the receipt records declaration kind,
module, local/external scope, internal/private status, graph role, and exact direct
constant usage split into type, value/proof body, and structural channels.

The recursive traversal begins at every theorem in
`REGISTERED_THEOREM_BINDINGS.json`, follows only declarations whose defining
module is local `Zeta23`, and retains external constants as non-recursive boundary
nodes. The graph must project this receipt exactly. The steady-state receipt MUST use
schema `RHKG-phase2b-compiler-dependencies-0.4`; the
`RHKG-phase2b-bootstrap-pending` marker is forbidden once Phase 2B is
materialized and sealed.

A dependency present in more than one channel remains one conceptual
`USES_CONSTANT` edge under the stable relation identity
`sha256(kind|source|target)`; channel booleans are metadata on that edge.
Expression-level self dependencies are preserved when Lean reports them in the
TYPE or VALUE channel. Trivial self-membership introduced only by structural
declaration-family metadata is not emitted as a dependency edge.

`REGISTERED_CLAIM_ROOT` declarations are the only declarations permitted to
participate in `PROVES`. `LOCAL_DEPENDENCY` and `EXTERNAL_BOUNDARY` declarations
never acquire theorem authority merely by appearing in the dependency graph.

**RH remains OPEN.**


## 13. Phase-2C dependency-kernel research views

Phase 2C introduces no new graph relation kind and no Lean theorem authority. It
derives deterministic research views from the exact Phase-2B compiler receipt and
the complete registered proved-root surface.

`research/RHRC/graph/DEPENDENCY_FARMING_COHORTS.json` is an audit-only
configuration. Route cohorts are resolved mechanically from the live claim
registry and complete proved binding manifest. Explicit cohorts fail closed if a
member is unknown, OPEN, duplicated, or absent from the complete proved binding
surface.

The generated products are:

- `DEPENDENCY_KERNEL_ATLAS.json`
- `DEPENDENCY_COHORT_OVERLAP.json`
- `DEPENDENCY_SIGNATURE_CLASSES.json`

The following firewalls are normative:

```text
shared dependency            != theorem equivalence
equal dependency closure     != theorem equivalence
closure containment          != logical implication
high root coverage           != mathematical importance
graph centrality             != mathematical importance
module IMPORTS               != declaration USES_CONSTANT
registry dependency          != declaration USES_CONSTANT
external-library overlap     != project-local mathematical kernel
cohort membership            != theorem authority
Phase-2C output              != claim promotion
```

Project-local kernel views include only compiler declarations with
`repository_scope = LOCAL`. External Lean/Mathlib constants remain available in
the Phase-2B closure as audit boundaries but are excluded from the primary kernel
and shell calculations.

Cohort overlap is reported as exact integer set arithmetic. Pairwise Jaccard data
is stored as numerator/denominator counts rather than floating-point scores.
Per-member shells are exact set differences from the cohort-wide intersection.

Dependency signatures are SHA-256 hashes over the sorted, NUL-delimited local
dependency names. Equal signatures mean exact equality of those dependency sets
only. Strict closure containment is an exact set relation only.

All Phase-2C products must carry:

```text
terminal_claim = RH_OPEN
graph_theorem_promotion = false
```

**RH remains OPEN.**
