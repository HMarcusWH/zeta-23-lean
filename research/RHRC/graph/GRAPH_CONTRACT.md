# RHKG Phase-2D Graph Contract

**Version:** 1.0  
**Scope:** complete repository accounting through the final semantic-closure pass: file/module/import census, registered compiler dependency graph, dependency-kernel research views, source-declaration discovery surface, document nodes, and explicit standalone-module dispositions  
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


## 14. Phase-2D kernel quotient and bridge frontiers

Phase 2D consumes the Phase-2C dependency closures without changing theorem
authority. It partitions one configured proved-root cohort into exact Venn-style
dependency atoms, profiles those atoms, and projects the compiler
`USES_CONSTANT` graph across atom boundaries.

The configured target is `RH_EQUIVALENCE_SURFACE`, with labels:

```text
A = R001_PRIME_UPPER_EQUIV_RH
B = AUDIT_CANONICAL_ARITHMETIC_CRITERIA_RH_EQUIVALENCE
C = AUDIT_GLOBAL_BOTTOM_RESIDUAL_EXCLUSION_RH_EQUIVALENCE
```

### Root-exclusion invariant

Phase-2D atoms are computed from each root's
`transitive_local_dependencies` exactly as emitted by
`THEOREM_DEPENDENCY_CLOSURE.json`. The root theorem itself is **not** inserted
into its own dependency closure.

This invariant is fail-closed. A root-including closure changes the partition and
is not an equivalent representation.

### Edge-direction invariant

A frontier edge has the exact compiler direction

```text
source declaration -> compiler-reported used constant
```

It is not reversed to match an intuitive mathematical dependency narrative.

### Reachability-monotonicity invariant

For the A/B/C atom quotient, every cross-atom compiler edge must move from a
strictly smaller root-membership set to a strictly larger one. If a declaration
reachable from a given root uses another local declaration, that dependency is
reachable from the same root as well.

Therefore transitions such as `A -> ABC`, `B -> BC`, or `BC -> ABC` are
structurally compatible with the closure construction, while `ABC -> A` is not.

This monotonicity is a graph invariant, **not** independent evidence that the
larger-membership declaration is a mathematically decisive reconvergence point.

### Generated products

Phase 2D adds:

- `DEPENDENCY_COHORT_ATOMS.json`
- `DEPENDENCY_KERNEL_QUOTIENT.json`
- `DEPENDENCY_BRIDGE_FRONTIERS.json`

The atom product records all nonempty membership signatures, including zero-count
atoms, exact declaration sets, module/kind/role profiles, visibility counts, and
hashes.

The quotient product is a factual compression of those profiles. It does not
label any module or declaration as generic, important, canonical, or decisive.

The frontier product records exact local compiler edges whose endpoints lie in
different atoms. It also separately probes the exact strict dependency-set
containment

```text
R003_CANONICAL_PRIME_REMAINDER_NORMAL_FORM
  subset of
EZ_GLOBAL_BOTTOM_ARITHMETIC_RESIDUAL
```

to expose the compiler boundary between the canonical prime-remainder substrate
and the larger global-bottom arithmetic-residual implementation.

### Candidate firewall

A `bridge_candidate_eligible` edge is only an exact cross-region edge whose
endpoints are not `REGISTERED_CLAIM_ROOT` declarations. Eligibility is a filter,
not a ranking or theorem claim.

Normative firewalls:

```text
dependency atom              != logical class
cross-atom edge              != logical implication
frontier declaration         != missing theorem
small frontier               != mathematical sufficiency
large frontier               != mathematical irrelevance
module concentration         != mathematical importance
shortest dependency path     != proof of semantic necessity
bridge-candidate eligibility != theorem authority
Phase-2D output              != claim promotion
```

All Phase-2D products must preserve:

```text
terminal_claim = RH_OPEN
graph_theorem_promotion = false
```

**RH remains OPEN.**

## 15. Phase-2E theorem-value erasure and dependency projections

Phase 2E does not alter the Phase-2B compiler receipt or the sealed Phase-2D
`ANY` dependency semantics. It derives additional traversal projections over the
same exact `USES_CONSTANT` edges.

The supported projection names are:

```text
ANY
TYPE_ONLY
VALUE_ONLY
THEOREM_VALUE_ERASED_SUPPORT
```

Their exact traversal laws are:

```text
ANY
    admit every compiler dependency edge

TYPE_ONLY
    admit iff used_in_type = true

VALUE_ONLY
    admit iff used_in_value = true

THEOREM_VALUE_ERASED_SUPPORT
    admit TYPE edges
    admit STRUCTURE edges
    admit VALUE edges only when source declaration_kind != THEOREM
```

`THEOREM_VALUE_ERASED_SUPPORT` removes recursive traversal through theorem
VALUE/proof bodies while preserving declaration TYPE support, structural
declaration-family support, and VALUE bodies of non-theorem declarations. It does
not claim to erase every proof object that may occur inside definitions and does
not create a semantic or logical dependency relation.

### Phase-2D regression lock

The `ANY` projection MUST remain exactly equivalent to the pre-existing
Phase-2D dependency traversal. For the current sealed RH-equivalence quotient this
includes the exact atom counts

```text
A   = 12
B   = 78
C   = 72
AB  = 0
AC  = 0
BC  = 1463
ABC = 599
```

and the exact 1,026 cross-atom frontier edges.

The canonical-prime-remainder/global-bottom `ANY` pair must reproduce the
Phase-2D counts 224, 2,659, 2,435 right-only, 972 cross-region edges, and 949
eligible cross-region edges.

### Neutral pair semantics

Projected pair analysis MUST NOT assume Phase-2D containment survives. The two
closures are partitioned as:

```text
LEFT_ONLY
RIGHT_ONLY
SHARED
```

and the exact relation is reported as one of:

```text
EQUAL
LEFT_STRICT_SUBSET
RIGHT_STRICT_SUBSET
INCOMPARABLE
```

Containment or incomparability under a compiler-support projection is descriptive
only.

### Projection reachability invariant

For any projection, if a root reaches a source declaration and the projected
graph admits an edge from that source to a local target declaration, then the root
also reaches the target. Therefore cross-atom edges in a projection must move from
a strict subset of root-membership labels to a strict superset.

This is a graph-closure invariant, not evidence of mathematical reconvergence.

### Generated products

Phase 2E adds:

- `DEPENDENCY_PROJECTION_SUMMARY.json`
- `DEPENDENCY_PROJECTION_QUOTIENTS.json`
- `DEPENDENCY_PROJECTION_FRONTIERS.json`

The summary materializes compact count/hash data across the complete 75-root
registered proved surface. Full declaration lists are materialized only for the
configured RH-equivalence quotient and its pair probe to avoid duplicating the
entire compiler closure several times.

### Normative firewalls

```text
TYPE_ONLY closure                    != theorem-statement semantics
VALUE_ONLY closure                   != proof necessity
THEOREM_VALUE_ERASED_SUPPORT         != logical dependency
THEOREM_VALUE_ERASED_SUPPORT         != theorem equivalence
projection overlap                   != mathematical importance
projection collapse                  != missing theorem
small projected frontier             != mathematical sufficiency
large projected frontier             != route falsification
projected containment                != logical implication
Phase-2E output                      != claim promotion
```

All Phase-2E products must preserve:

```text
terminal_claim = RH_OPEN
graph_theorem_promotion = false
```

**RH remains OPEN.**


## 18. Final semantic-closure pass

The final closure pass closes the repository-accounting blind spots exposed by
the post-#262 audit without widening theorem authority.

### 18.1 Named Lean source-declaration surface

Every local Lean module is scanned deterministically after Lean comments are
removed by the same shared comment-aware parser used by the import firewall.
Named source commands (`theorem`, `lemma`, `def`, `abbrev`, `opaque`, `axiom`,
`structure`, `class`, `inductive`, and explicitly named `instance`s) are emitted
as `LeanSourceDeclaration` nodes and connected by
`LeanModule SOURCE_DECLARES LeanSourceDeclaration`.

This surface has provenance `LEAN_SOURCE_EXACT` and authority role
`SOURCE_DISCOVERY_ONLY`.

It exists to make named source material discoverable even when the declaration
is outside every registered theorem dependency closure. It is **not** a
compiler declaration census, it does not create `USES_CONSTANT` edges, and it
does not promote a declaration to a registered claim.

The existing compiler-derived `LeanDeclaration` / `USES_CONSTANT` layer
remains the only declaration-dependency authority.

### 18.2 Document semantic coverage

Every file classified as `DOCUMENTATION` or `LIVING_SSOT` receives one
source-backed `Document` node with an exact `LOCATED_AT` relation.

Exact textual mentions of existing registered claim IDs and route IDs generate
`MENTIONS` edges with provenance `TEXTUAL_HINT`. These are navigation hints
only. They do not mean support, implication, supersession, equivalence, or
theorem authority.

The five living SSOT documents receive explicit document roles in
`SEMANTIC_CLOSURE_CONFIG.json`; ordinary documentation receives the default
`DOCUMENTATION_ARTIFACT` role.

### 18.3 Standalone-module dispositions

The exact current `standalone_or_auxiliary` module set must equal the keys of
`SEMANTIC_CLOSURE_CONFIG.json::standalone_module_roles`.

This converts reachability from an unresolved orphan-like bucket into a reviewed
operational disposition while preserving the constitutional rule that lack of
entrypoint reachability does not imply irrelevance.

### 18.4 Generated closure products

The final pass adds:

- `lean_source_declarations.jsonl`
- `MODULE_SEMANTIC_CLOSURE.json`
- `DOCUMENT_SEMANTIC_CLOSURE.json`

`MODULE_SEMANTIC_CLOSURE.json` covers every local Lean module, records its
entrypoint reachability/disposition, named source-declaration count, exact
registered dependency-surface declaration count, and registered-root count.

`DOCUMENT_SEMANTIC_CLOSURE.json` covers every documentation/living-SSOT file
and records its document role plus exact claim/route token mentions.

### 18.5 What remains deliberately open

Repository accounting is closed at the file, module, document, and named
source-command discovery layers. Later semantic deepening may still add:

- a compiler-wide local declaration census beyond the registered dependency
  closure and source-navigation surface;
- multi-axis current-state/authority resolution beyond document-role indexing;
- Git/PR/workflow execution provenance;
- explicit dead-route/obstruction/revival semantic objects and relations;
- operational concept preflight.

These are deeper semantic layers, not missing repository artifacts.

Final-closure firewall:

```text
LeanSourceDeclaration            != compiler LeanDeclaration
SOURCE_DECLARES                  != USES_CONSTANT
Document MENTIONS claim/route    != support or implication
standalone disposition           != theorem authority
semantic accounting closure      != RH closure
terminal claim                   = RH_OPEN
graph theorem promotion          = false
```


### Integration-derived generated products

The integration foundation adds generated receipts outside
`research/RHRC/graph/generated/`:

- `research/RHRC/integration/generated/SOURCE_CANDIDATE_RESOLUTION.jsonl`
- `research/RHRC/integration/generated/RH_CORE_SOURCE_ONLY_THEOREMS.jsonl`
- `research/RHRC/integration/generated/SOURCE_CANDIDATE_SUMMARY.json`

These files are declared generated products for RHKG subject-digest purposes and
are therefore excluded from the repository subject digest, avoiding a recursive
graph -> exactification receipt -> graph hash cycle. Their exact producer is
`research/RHRC/integration/candidate_exactify.py`, not `graph/build.py`.

They remain covered `RepoFile` nodes and receive exact `GENERATED_BY`
relations. The graph builder continues to byte-regenerate only its own
`graph/generated` product set; the candidate exactifier independently
byte-checks the integration-derived receipts.

This separation is an authority and determinism boundary, not a theorem claim.


### FFBBP-derived generated product

The FFBBP RHKG assurance report

- `research/RHRC/ffbbp/generated/RHKG_CANDIDATE_REDUCTION_ASSURANCE.json`

is also a declared generated product. Its exact producer is
`research/RHRC/ffbbp/rhkg_assurance.py`. Its bytes are excluded from the RHKG
subject digest for the same acyclicity reason as the integration candidate
receipts: the report is derived from the admitted repository state and must not
recursively perturb the state digest it records.

This does not grant FFBBP theorem authority. The report remains
`RESEARCH_CONTROL_ONLY`, and RH remains OPEN.
