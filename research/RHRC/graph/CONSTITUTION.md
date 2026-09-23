# RHRC Repository Knowledge Graph Constitution

**Version:** 0.1  
**Status:** Foundational governance document  
**Applies to:** the RHRC repository knowledge-graph layer and all generated graph products  
**Repository:** HMarcusWH/zeta-23-lean  
**Adoption base:** commit fcf585f8d4ead741dfd0be2ce1ac9d068e9873f5, tree ff55f016bf8bf604eef2c9e5d410c0b67bcbd940  
**Terminal claim at adoption:** RH_OPEN

> **Foundational rule:** the graph exists to make repository state discoverable, traceable, queryable, and hard to misread. It does not create mathematical truth, research authority, or RH closure.

This constitution adapts the theory-state / knowledge-graph architecture already used elsewhere in the project to the specific needs of a Git- and Lean-backed Riemann Hypothesis research repository. The RHRC graph is a **derived integration layer over existing repository authorities**, not a replacement for them.

Compiler/CI evidence remains authoritative for formal validity. Existing RHRC machine registries remain authoritative for the claims and control semantics they already govern. Historical records remain historical. Experimental results remain experimental. **RH remains OPEN unless and until the exact terminal theorem is proved and passes the repository's full claim-validation gates.**

---

# Article I — Purpose

The RHRC Repository Knowledge Graph ("RHKG") exists to solve five concrete repository problems:

1. **Zero-miss navigation:** every tracked repository artifact must be discoverable and classified.
2. **Semantic navigation:** mathematically and scientifically meaningful objects must be linked across Lean, research tooling, documentation, Git history, PRs, CI, and historical route records.
3. **Authority separation:** formal theorem authority, control semantics, bounded research evidence, experimental signals, documentation state, and historical provenance must remain distinct.
4. **Dependency visibility:** the project must be able to answer what a theorem, route, obstruction, experiment, or claim actually depends on.
5. **Post-green research support:** every meaningful green result must be connectable to downstream implications, upstream assumptions, prior failures, reopened routes, and the accumulated theorem inventory.

The graph is therefore a **repository nervous system**, not a new proof layer.

---

# Article II — Scope

RHKG covers the repository as a whole, including:

- Zeta23 Lean sources and root Lean entrypoints;
- comparator libraries and challenge/solution roots;
- research/RHRC;
- claim, route, control, boundary, and promotion registries;
- research scripts, fixtures, receipts, audits, countermodels, and historical deltas;
- Git commits, trees, pull requests, branches, and releases when captured;
- GitHub Actions workflow definitions, runs, jobs, and results when captured;
- external-source manifests already admitted by RHRC;
- generated RHKG views and snapshots.

RHKG does not automatically confer semantic importance on every file. It does require every file to have a declared repository role.

---

# Article III — Existing authority is preserved

RHKG is constitutionally subordinate to existing repository authority.

The graph MUST NOT replace or silently reinterpret:

- Lean kernel/compiler evidence;
- CI validity gates;
- research/RHRC/BOUNDARY.json;
- research/RHRC/CLAIM_REGISTRY.json;
- research/RHRC/R003_PROMOTED_BINDINGS.json;
- research/RHRC/routes/ROUTE_REGISTRY.json;
- research/RHRC/control_v2/CONTROL_STATE.json;
- research/RHRC/control_v2/ACTION_REGISTRY.json;
- research/RHRC/DOCUMENTATION_AUTHORITY.md;
- research/RHRC/VALIDATION_PROTOCOL.md;
- dead-route, obstruction, revival, and historical evidence rules already enforced by RHRC tooling.

When the graph mirrors one of those sources, the graph record MUST identify itself as a projection or normalized mirror and MUST point back to the authoritative source.

A graph disagreement with an authoritative source is a **graph defect**, not a reason to mutate the source silently.

---

# Article IV — The graph is a projection, not an authority generator

Encoding an object in RHKG does not promote its status.

In particular:

- a LeanDeclaration node is not automatically a registered claim;
- a registered claim node is not automatically proved;
- a successful workflow run is not automatically theorem authority;
- a research result node is not automatically mathematical evidence beyond its declared evidence class;
- a generated view is not an authoritative source merely because it is convenient;
- a relation inferred from text is not a formal dependency;
- a newer artifact does not automatically supersede an older one.

The graph may **report** authority. It may not invent it.

---

# Article V — Stable conceptual identity

Scientific and repository objects SHOULD have stable conceptual identifiers independent of transient presentation details.

Examples:

    rh:file:Zeta23/CCM/GlobalParityBottomSpectrum.lean
    rh:module:Zeta23.CCM.GlobalParityBottomSpectrum
    rh:decl:Zeta23.CCM.parityRayleighBottom
    rh:claim:R003_GLOBAL_PARITY_BOTTOM_SPECTRUM
    rh:route:R003_ccm_bridge
    rh:dead-route:DR-021
    rh:obstruction:OBS-060
    rh:pr:247
    rh:commit:7438f2a23750...

Stable identity prevents renames, moves, new documentation, or later PRs from erasing conceptual continuity.

---

# Article VI — Conceptual identity and revision identity are distinct

A conceptual object may have multiple immutable revisions.

For source-backed objects, the graph SHOULD distinguish:

    conceptual object
        ↓ HAS_REVISION
    revision at exact Git blob / commit / tree

A declaration with the same Lean name at two commits is the same conceptual declaration only if the project intentionally treats it as continuous. The exact source revision remains separately identifiable.

A claim, route, or research artifact that materially changes meaning MAY require a new conceptual identity rather than a new revision.

Identity changes must be explicit, not inferred from filename continuity alone.

---

# Article VII — Repository census is complete or it fails

The first graph invariant is physical coverage.

Every tracked repository file MUST be one of:

1. indexed and classified as a subject artifact; or
2. declared as a generated RHKG product.

No tracked file may disappear into an implicit ignore set.

The graph MUST be able to generate:

    REPOSITORY_COVERAGE
    UNINDEXED_FILES
    UNCLASSIFIED_FILES

with the long-term hard requirement:

    UNINDEXED_FILES = []
    UNCLASSIFIED_FILES = []

File-count totals must be computed from the live repository and MUST NOT be permanently hard-coded from the adoption snapshot.

---

# Article VIII — Physical coverage and semantic coverage are separate

Physical coverage answers:

> Does the graph know that this file exists, and what repository role it has?

Semantic coverage answers:

> Does the graph know what scientifically meaningful objects this file contains or supports?

A file may be physically indexed but not semantically rich.

Examples:

- a license file may be fully classified with no research relations;
- a fixture may need a consumer experiment relation;
- a Lean source must at minimum map to a Lean module;
- a promoted theorem must map to an exact Lean declaration;
- a research executable should map to an experiment, replay, or validation role;
- a historical dead-route delta should map to the relevant route/dead-route objects.

The graph MUST report semantic gaps separately from physical coverage.

---

# Article IX — File classification is deterministic

Repository file classes SHOULD be assigned by deterministic rules with explicit exceptions.

Initial classes include:

- LEAN_SOURCE
- LEAN_ROOT
- RESEARCH_EXECUTABLE
- RESEARCH_FIXTURE
- RESEARCH_RECEIPT
- COUNTERMODEL
- LIVING_SSOT
- FROZEN_RESEARCH_DELTA
- FROZEN_OBSTRUCTION_DELTA
- FROZEN_DEAD_ROUTE_DELTA
- REGISTRY
- CONTROL_STATE
- CI_WORKFLOW
- DOCUMENTATION
- EXTERNAL_SOURCE_MANIFEST
- BUILD_CONFIGURATION
- GENERATED_GRAPH_PRODUCT
- LICENSE_OR_METADATA
- OTHER_CLASSIFIED

An unknown class is a validation failure unless explicitly permitted by a temporary migration rule.

---

# Article X — Trust zones are independent of file classes

File type does not determine trust.

A Lean source may belong to different trust zones, for example:

- RH_FORMAL_CORE
- UPSTREAM_DERIVED
- AUXILIARY_FORMALIZATION
- COMPARATOR_TRUSTED_MATHLIB_ONLY
- COMPARATOR_UNTRUSTED_ZETA_IMPORTS
- RESEARCH_ONLY
- AUDIT_ONLY

The graph MUST preserve distinctions already encoded by the build structure, import firewalls, comparator layout, and formalization policy.

A file being Lean does not mean it belongs to the same claim-bearing trust surface as every other Lean file.

---

# Article XI — Core graph record classes

The initial ontology SHOULD remain compact.

Core node types are:

- Repository
- RepoFile
- LeanModule
- LeanDeclaration
- RegisteredClaim
- Route
- Obstruction
- DeadRoute
- ResearchLead
- Experiment
- Countermodel
- Fixture
- Evidence
- Gate
- Test
- Result
- Verdict
- PullRequest
- Commit
- Tree
- WorkflowDefinition
- WorkflowRun
- WorkflowJob
- Authority
- SourceLocator
- ExternalSource
- Release

Subtypes SHOULD be attributes unless separate identity is required.

The ontology must not expand merely because a new filename or PR title appears.

---

# Article XII — Relation vocabulary is typed

Core relation types include:

    CONTAINS
    DECLARES
    IMPORTS
    USES_CONSTANT

    PROVES
    FORMALIZES
    EQUIVALENT_TO
    SPECIALIZES
    GENERALIZES
    ASSUMES

    REGISTERED_IN
    PART_OF_ROUTE
    REQUIRES
    DEPENDS_ON
    BLOCKS
    UNBLOCKS

    SUPPORTS
    CONTRADICTS
    FALSIFIES
    DOES_NOT_ESTABLISH

    KILLS_ROUTE
    REOPENS
    PRESERVES_NEGATIVE_RESULT

    INTRODUCED_BY
    MODIFIED_BY
    VALIDATED_AT
    VALIDATED_BY
    REPLAYED_BY

    GENERATED_BY
    DERIVED_FROM

    SUPERSEDES
    REPAIRS
    PRESERVES

    GOVERNED_BY
    RESOLVED_BY
    LOCATED_AT

Relation semantics must be documented before they are used as authority-bearing facts.

---

# Article XIII — Relation provenance is mandatory

Every nontrivial relation MUST carry or inherit a provenance class.

Initial provenance classes are:

- FORMAL_EXACT
- GIT_EXACT
- CI_EXACT
- REGISTRY_EXACT
- CURATED_SEMANTIC
- TEXTUAL_HINT

The graph MUST NOT collapse these into a single undifferentiated edge.

In particular:

- TEXTUAL_HINT may guide discovery;
- TEXTUAL_HINT may not promote a claim;
- CURATED_SEMANTIC requires a source locator;
- FORMAL_EXACT must ultimately be traceable to Lean/compiler-checked structure.

---

# Article XIV — Lean module imports are not theorem dependencies

The graph MUST distinguish:

    LeanModule IMPORTS LeanModule

from:

    LeanDeclaration USES_CONSTANT LeanDeclaration

and both from:

    LeanDeclaration PROVES RegisteredClaim

A module import means availability, not necessarily mathematical use.

A declaration dependency means the elaborated declaration body or type references another constant.

A claim-binding relation means an RHRC authority explicitly binds that declaration to the claim.

No layer may be inferred from a weaker one merely for convenience.

---

# Article XV — Existing import-firewall semantics are preserved

RHRC already uses import-graph logic in anti-circularity tooling such as the arithmetic firewall.

RHKG MUST reuse or remain behaviorally consistent with those semantics.

The graph MUST NOT weaken any existing firewall by introducing a broader aggregate root or by treating audit-only or terminal modules as ordinary dependencies.

If import-graph code is refactored into shared infrastructure, existing firewall tests must prove behavioral equivalence before the old implementation is removed.

---

# Article XVI — Lean declarations and registered claims are separate populations

The repository may contain thousands of Lean declarations and only a much smaller curated set of registered claims.

Therefore:

    LeanDeclaration != RegisteredClaim

A registered claim may point to one or more declarations through explicit registry/promotion machinery.

A declaration becomes claim-bearing only through an existing or newly reviewed RHRC binding.

Automatic theorem-name discovery MUST NOT mutate CLAIM_REGISTRY.json.

---

# Article XVII — Gate, Test, Result, and Verdict are distinct

Validation state MUST be represented in four layers:

    Gate
      → Test
        → Result
          → Verdict

Definitions:

- **Gate:** the rule or criterion being enforced.
- **Test:** a concrete execution of that gate on a specific object.
- **Result:** the raw or normalized outcome of the execution.
- **Verdict:** the scoped scientific/formal interpretation of the result.

Example:

    Gate: no-sorry / axiom firewall
    Test: workflow job on exact PR head
    Result: success
    Verdict: exact declaration passed that formal-validity gate

A successful result does not determine a verdict without gate semantics.

---

# Article XVIII — Workflow success is not a single evidence type

Workflow jobs MUST be classified, where possible, as:

- FORMAL_VALIDITY_GATE
- REGRESSION_GATE
- RESEARCH_PRODUCING_CHECK

A workflow definition may therefore be MIXED.

The graph MUST support:

    workflow definition exists
    -/-> workflow ran on this PR

    workflow run success
    -/-> theorem promotion

    regression replay success
    -/-> new research authority

    research scout success
    -/-> formal theorem

Historical jobs still running must never be silently treated as passed.

---

# Article XIX — Scientific state is multi-axis

There is no single scalar "latest state" for RHRC.

The resolver MUST permit simultaneous scoped states such as:

- formal theorem authority;
- control-semantic authority;
- independent bounded research evidence;
- experimental scout evidence;
- current documentation interpretation;
- historical evidence;
- route phase;
- obstruction state;
- dead-route state.

These may legitimately point to different PRs or commits.

The graph MUST NOT collapse them into "newest wins."

---

# Article XX — Resolution is partitioned by subject, axis, scope, and facet

The current-state resolver SHOULD operate on a key equivalent to:

    subject
    × state axis
    × resolution facet
    × scope

Authority applies within its declared partition.

A newer document cannot supersede a theorem merely because it is newer.

A theorem-equivalence audit cannot supersede an experimental result on a different axis.

An experimental scout cannot replace a frozen independent bounded-research anchor unless the governing authority explicitly says so.

---

# Article XXI — Authority must be explicit and scoped

Every authority record SHOULD state:

- authority identifier;
- controlled subject or subject family;
- state axis;
- scope;
- admissible source types;
- precedence;
- supersession behavior;
- failure behavior.

When authority is absent or conflicting, the resolver MUST fail closed or report UNKNOWN / conflict.

It MUST NOT infer authority from recency, filename, PR title, or rhetorical emphasis.

---

# Article XXII — Git provenance is first-class

Git provides immutable provenance and SHOULD be used wherever possible.

Source-backed graph records SHOULD preserve:

- repository path;
- blob SHA;
- commit SHA;
- tree SHA;
- parentage when relevant;
- introducing PR/commit when known.

Commit and tree identity matter because compiler/CI authority applies to exact checked objects.

"Same filename" is not enough.

---

# Article XXIII — Pull requests are change events, not theorem statements

A pull request node MAY carry:

- PR number;
- title/body;
- base/head refs;
- final validated head SHA;
- merge commit;
- merge tree;
- changed files;
- workflow runs;
- declarations introduced/changed;
- claims or routes affected;
- documentation/verdict changes.

However:

    PR title/body
    -/-> mathematical theorem

Only exact compiled declarations and validated bindings can establish formal theorem state.

PR change-impact edges must distinguish file touch from actual declaration or claim change.

---

# Article XXIV — Claim firewall is constitutional

RHKG inherits the RHRC claim firewall.

The graph MUST preserve at least the distinctions:

- **PROVED** — exact statement established by Lean/compiler/CI.
- **DERIVED** — straightforward consequence of proved results, not separately formalized.
- **LEAD / HYPOTHESIS** — motivated route worth testing.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence.
- **OPEN** — not established.

Existing registry-specific statuses remain authoritative where they are more granular.

The graph MUST NOT convert:

- numerical evidence → theorem;
- synthetic countermodel → theorem;
- successful regression → theorem;
- historical note → theorem;
- RH-equivalent criterion → truth of that criterion;
- green infrastructure → RH;
- supporting lemma → RH.

**RH remains OPEN until the exact RH theorem passes the complete proof and claim-validation gates.**

---

# Article XXV — Research evidence retains its declared class

The graph MUST preserve evidence classes used by RHRC, including distinctions such as:

- exact executable research;
- rigorous point research;
- rigorous bounded research;
- rigorous bounded partial research;
- experimental signal;
- synthetic countermodel;
- unresolved;
- falsified mechanism;
- representation/dependency unresolved.

A result may be scientifically valuable without being theorem authority.

No graph view may erase the words "bounded", "synthetic", "experimental", "partial", or "unresolved" when those qualifiers are part of the evidence class.

---

# Article XXVI — Negative results are permanent knowledge

A dead, falsified, quarantined, or failed route is not trash.

Negative-result records SHOULD preserve:

- route/dead-route identifier;
- exact proposal tested;
- failure reason;
- source evidence;
- scope of falsification;
- what remains unrefuted;
- original blocker;
- later changes relevant to the blocker;
- reopening conditions.

Historical failures must remain queryable after later progress.

The graph MUST support the question:

> What failed before, why did it fail, and has the premise responsible for failure changed?

---

# Article XXVII — Revival requires explicit changed-premise evidence

RHKG does not invent a second revival law.

It adopts the existing RHRC revival principle:

> A dead or quarantined route may not be silently resurrected.

A revival must identify:

1. the original blocker;
2. the changed premise;
3. evidence for the change;
4. the proposed revived route.

A generated REOPENING_CANDIDATES view may suggest candidates, but it cannot itself reopen a route.

Actual revival remains governed by the existing RHRC revival mechanism.

---

# Article XXVIII — Source locators are first-class

Every curated semantic record SHOULD be traceable through a SourceLocator.

For Git-backed sources, the preferred identity is:

    repository
    path
    blob SHA
    commit/tree context
    semantic anchor

Semantic anchors may include:

- Lean declaration name;
- Markdown heading;
- JSON key/path;
- Python symbol;
- fixture row/key;
- workflow/job identifier;
- PR number;
- commit SHA.

Line numbers are convenience metadata only. They are not durable identity.

---

# Article XXIX — Minimum completeness questions

A valid graph release SHOULD be able to answer, or explicitly mark unknown, at least these questions:

1. What tracked files exist?
2. What class and trust zone does each file belong to?
3. Which Lean modules exist?
4. Which aggregate roots reach each module?
5. Which registered claims exist?
6. Which exact Lean declarations bind to promoted claims?
7. Which routes contain those claims?
8. What current authorities govern theorem, control, research, and documentation state?
9. Which obstructions and dead routes are relevant to a route?
10. Which experiments/countermodels have tested the route?
11. Which workflow gates validated the relevant commit?
12. Which historical failures may deserve re-evaluation because dependencies changed?
13. Which relevant artifacts remain semantically unlinked?
14. What is still unknown?

A graph that cannot expose its unknowns is not complete enough for research planning.

---

# Article XXX — Generated views are disposable, reproducible products

Generated views are conveniences derived from the graph.

Examples include:

- REPOSITORY_COVERAGE.json
- UNINDEXED_FILES.json
- UNCLASSIFIED_FILES.json
- UNLINKED_SEMANTIC_FILES.json
- LEAN_IMPORT_GRAPH.json
- ENTRYPOINT_REACHABILITY.json
- THEOREM_CLAIM_MAP.json
- AUTHORITY_MAP.json
- CURRENT_STATE.json
- ROUTE_DEPENDENCY_MAP.json
- OBSTRUCTION_MAP.json
- DEAD_ROUTE_MAP.json
- REOPENING_CANDIDATES.json
- WORKFLOW_HARVEST_MAP.json
- PR_IMPACT_MAP.json
- CHANGE_IMPACT.json
- CANONICAL_READ_ORDER.md

Generated views MUST identify their inputs and generator version.

They are never stronger than their sources.

---

# Article XXXI — Change impact is explicit

For each meaningful repository change, RHKG SHOULD support change-impact analysis across:

- files;
- Lean modules;
- declarations;
- registered claims;
- routes;
- obstructions;
- dead routes;
- experiments;
- workflow gates;
- authorities;
- generated current-state views.

File-level change impact and semantic change impact are distinct.

Touching a file does not automatically mean every declaration or route in that file changed.

---

# Article XXXII — Repository entrypoints are descriptive, not completeness gates

The graph SHOULD record reachability from declared entrypoints such as:

- the headline Zeta23.lean root;
- Zeta23.CCM;
- Zeta23.ExceptionalZero;
- comparator roots;
- other formal aggregate roots explicitly declared by the project.

But lack of reachability from a headline root does not imply irrelevance.

Some audit-only, experimental, auxiliary, historical, or intentionally unimported modules are legitimate.

The graph must classify the role rather than label every standalone module an orphan.

---

# Article XXXIII — Deterministic generation is mandatory

Given the same repository tree, same frozen external snapshots, same configuration, and same generator version, graph generation MUST be deterministic.

Determinism includes:

- stable IDs;
- canonical ordering;
- stable serialization;
- no timestamps in semantic output unless they are source data;
- no network-dependent CI generation;
- no random ordering;
- no LLM-dependent authority decisions.

A regeneration check SHOULD be able to prove byte-for-byte equality for checked-in generated products.

---

# Article XXXIV — The graph must not hash itself recursively

Generated graph products create a self-reference hazard.

Therefore a graph release MUST distinguish:

- **subject repository payload**; and
- **declared generated graph products**.

Subject digests MUST exclude the declared generated-product domain while coverage validation still verifies that those generated files are present and declared.

No implicit wildcard exclusion is permitted.

The release record must say exactly what was hashed.

---

# Article XXXV — Schema and validation are fail-closed

RHKG schema validation SHOULD be stricter than a free-form property bag for authority-bearing record types.

At minimum:

- every record has id and type;
- every relation has typed endpoints and provenance;
- every source-backed semantic record has a source locator;
- every registered-claim projection identifies its source registry;
- every proved-claim binding identifies the Lean declaration;
- every workflow result identifies the exact run/job when available;
- every authority record declares its axis/scope;
- every dead-route revival reference resolves to an existing dead-route record;
- every relation endpoint exists;
- duplicate stable IDs are forbidden.

Unknown or malformed authority-bearing records fail validation.

---

# Article XXXVI — Historical archaeology reuses existing RHRC machinery

RHKG SHALL NOT build a parallel archaeology engine while existing RHRC retro tooling provides:

- Git-history search;
- all-ref archaeology mode;
- concept aliases;
- historical source-family registry;
- external archive ingestion;
- time-bounded replay;
- revival records.

The graph SHOULD consume outputs or shared primitives from that machinery.

If shared code is factored out, existing retro tests and search semantics must remain valid.

Historical search completeness must always state its search domain.

---

# Article XXXVII — External-source evidence remains separately typed

External papers, architecture documents, version families, and archived sources MAY appear as ExternalSource nodes.

They MUST preserve:

- source family;
- version if known;
- provenance;
- availability date if relevant;
- authority class;
- ingestion status;
- exact artifact/hash when available.

External material cannot become formal theorem authority merely by being linked.

Historical architecture sources remain historical unless independently promoted through the relevant RHRC process.

---

# Article XXXVIII — Operational preflight becomes mandatory only after validation

The long-term operational goal is:

> No substantial theorem plan should be made without first traversing the RHKG neighborhood of the target concept.

A mature preflight SHOULD return:

- current formal theorem state;
- relevant Lean modules/declarations;
- exact claim bindings;
- route membership;
- open obstructions;
- dead routes;
- revival records;
- historical clues;
- relevant experiments/countermodels;
- relevant workflow outcomes;
- current research evidence;
- unresolved graph items.

However, this operational requirement MUST NOT be activated until the graph has passed its census, declaration, authority, history, and semantic-coverage validation stages.

An incomplete graph must not create false confidence.

---

# Article XXXIX — Post-green integration

After every meaningful green theorem or research PR, RHKG SHOULD make it possible to update or generate the following relationships:

- exact object that became green;
- gates that passed;
- declaration or research object changed;
- assumptions/imports/interfaces used;
- workflow-harvest results;
- upstream dependencies;
- downstream consumers;
- dead routes whose blocker may have changed;
- experiments newly relevant;
- new or resolved obstructions;
- claim-status consequences, if any.

Green is an event in the graph, not the end of the investigation.

---

# Article XL — Current-state resolution must reproduce source truth

RHKG's current-state resolver is valid only if it reproduces the state encoded by the governing repository sources.

It may not "improve" them.

Legitimate simultaneous state can include:

    formal theorem authority              -> one exact validated theorem PR
    Control-v2 semantic authority         -> its frozen authority
    independent bounded research evidence -> its current declared anchor
    experimental scout evidence           -> later research PRs
    current documentation                 -> current main-tree files
    terminal claim                        -> RH_OPEN

If the resolver produces a different answer from the authoritative source, the graph is wrong until reconciled.

---

# Article XLI — No silent supersession

Supersession must be explicit and scoped.

A record may be:

- preserved;
- repaired;
- superseded;
- partially superseded;
- reinterpreted;
- frozen historically;
- replaced only on one state axis.

The graph MUST preserve the older record unless repository policy explicitly authorizes deletion.

"Newer" is not a supersession relation.

---

# Article XLII — Claim-bearing edges require elevated review

The following relation families are claim-bearing and require exact or curated support:

- PROVES;
- EQUIVALENT_TO;
- ASSUMES;
- DEPENDS_ON when asserted as mathematical dependency;
- KILLS_ROUTE;
- REOPENS;
- SUPERSEDES for scientific state;
- authority assignments.

Automated extraction may propose such edges, but proposal does not equal acceptance.

Claim-bearing graph mutations must be reviewable in ordinary Git diffs.

---

# Article XLIII — Text mining is discovery-only

Text search, embeddings, LLM extraction, keyword overlap, filename similarity, and concept aliases may discover candidate relations.

They MUST be typed as discovery output until curated or replaced by stronger provenance.

No machine-learned or heuristic relation may:

- alter CLAIM_REGISTRY.json;
- alter terminal claim status;
- reopen a dead route;
- establish theorem dependency;
- supersede formal authority.

---

# Article XLIV — Unknown is a legitimate state

RHKG must prefer explicit unknowns to invented completeness.

Examples:

- historical workflow metadata unavailable from GitHub;
- declaration-level dependency extraction not yet implemented;
- a historical document not yet semantically normalized;
- source locator known only at file level;
- relation suspected but not curated.

These should appear as UNKNOWN, UNRESOLVED, PARTIAL, or another controlled incomplete state.

Unknown is not failure unless a gate requires completeness for that scope.

---

# Article XLV — Constitutional integrity and amendment

This constitution governs the graph layer.

It may be amended only through ordinary repository review, with explicit description of:

- article(s) changed;
- reason for change;
- impact on existing graph records;
- migration requirements;
- whether any authority or claim-bearing behavior changes.

An amendment MUST NOT silently alter RHRC theorem, claim, control, or evidence authority.

Changes that would let RHKG promote claims, bypass Lean/CI authority, erase negative results, or infer RH closure from nonformal evidence require explicit rejection unless the underlying RHRC authority model itself is separately changed.

---

# Appendix A — Initial repository integration map

RHKG begins as a composition layer over existing machinery.

| Existing source | Graph role |
|---|---|
| BOUNDARY.json | terminal-claim and promotion firewall |
| CLAIM_REGISTRY.json | registered-claim authority |
| R003_PROMOTED_BINDINGS.json | exact R003 promoted claim bindings |
| routes/ROUTE_REGISTRY.json | route membership/state |
| control_v2/CONTROL_STATE.json | current descriptive/control research state |
| control_v2/ACTION_REGISTRY.json | frozen Control-v2 semantics |
| DOCUMENTATION_AUTHORITY.md | documentation/authority precedence |
| VALIDATION_PROTOCOL.md | evidence interpretation and validation law |
| control_v2/retro/* | archaeology, aliases, archives, revival discipline |
| tools/arithmetic_firewall_lint.py | existing Lean import-graph firewall semantics |
| tools/promoted_binding_lint.py | claim-to-theorem binding gate |
| .github/workflows/* | workflow definitions |
| Git | file/blob/commit/tree provenance |
| GitHub PR/Actions metadata | PR and execution provenance when captured |

RHKG should normalize these sources without duplicating their authority.

---

# Appendix B — Initial relation vocabulary

The first implementation SHOULD support only relations that can be explained precisely:

    CONTAINS
    CLASSIFIED_AS
    DECLARES
    IMPORTS
    REGISTERED_IN
    PART_OF_ROUTE
    MIRRORS
    GOVERNED_BY
    LOCATED_AT
    GENERATED_BY

Later phases may add the broader relation vocabulary from Article XII.

Expansion requires tests and documented semantics.

---

# Appendix C — Initial file-classification examples

Examples, not exhaustive rules:

    Zeta23/**/*.lean
        -> LEAN_SOURCE

    Zeta23.lean
        -> LEAN_ROOT

    research/RHRC/routes/**/*.py
        -> RESEARCH_EXECUTABLE

    research/RHRC/routes/**/fixtures/**
        -> RESEARCH_FIXTURE

    research/RHRC/receipts/**
        -> RESEARCH_RECEIPT

    research/RHRC/RESEARCH_LEADS_POST_*.md
        -> FROZEN_RESEARCH_DELTA

    research/RHRC/OBSTRUCTION_LEDGER_POST_*.md
        -> FROZEN_OBSTRUCTION_DELTA

    research/RHRC/DEAD_ROUTES_POST_*.md
        -> FROZEN_DEAD_ROUTE_DELTA

    .github/workflows/*.yml
        -> CI_WORKFLOW

    research/RHRC/graph/generated/**
        -> GENERATED_GRAPH_PRODUCT

Rules must be deterministic and validated against the live tree.

---

# Appendix D — Initial implementation sequence

The constitution is intentionally broader than the first implementation.

## Phase 1 — Repository census and module import graph

Build:

- deterministic file inventory;
- file classes/trust zones;
- Lean module nodes;
- module import graph;
- registry/route mirror nodes;
- physical-coverage reports;
- entrypoint reachability;
- unresolved-item report.

No theorem or research authority changes.

## Phase 2 — Lean declaration graph

Add:

- declaration extraction;
- declaration source locators;
- declaration-level constant dependencies where safely extractable;
- promoted claim → declaration bindings;
- axiom-surface views.

No automatic claim promotion.

## Phase 3 — Authority/current-state projection

Normalize:

- boundary;
- claim authority;
- route state;
- control state;
- documentation authority;
- research evidence facets.

Build a resolver that reproduces source truth.

## Phase 4 — Git/PR/workflow provenance

Add:

- commit/tree graph;
- PR change events;
- frozen GitHub metadata snapshots;
- workflow/run/job graph;
- gate/result classification.

No network-dependent normal CI.

## Phase 5 — Historical research memory

Normalize:

- obstructions;
- dead routes;
- research leads;
- countermodels;
- revival records;
- historical deltas;
- retro-search receipts.

Generate reopening-candidate views without auto-revival.

## Phase 6 — Operational preflight

Generate concept-centered research preflight and change-impact views.

Only after validation may RHKG become mandatory before substantial theorem planning.

---

# Appendix E — Phase-1 hard acceptance gates

The first implementation phase should not be considered complete until CI can verify:

    tracked subject files        == indexed subject files
    declared generated products  == actual generated products

    unindexed files              == 0
    unclassified files           == 0

    duplicate graph IDs          == 0
    missing relation endpoints   == 0
    missing source paths         == 0

    CLAIM_REGISTRY projection    == exact
    ROUTE_REGISTRY projection    == exact

    all Lean files               -> LeanModule node
    all local import targets     -> resolvable module or explicit external target

    generated regeneration       -> deterministic
    terminal claim               -> RH_OPEN
    graph theorem promotion      -> false

Semantic-link gaps may remain in Phase 1, but they must be reported rather than hidden.

---

# Appendix F — Prohibited graph behavior

The following are constitutional violations:

1. Promoting RH or any claim from generated graph state.
2. Treating a green research workflow as a theorem.
3. Treating a module import as mathematical dependence.
4. Treating every Lean declaration as a registered claim.
5. Treating recency as supersession.
6. Treating an unreachable module as automatically irrelevant.
7. Treating missing historical GitHub metadata as a passed or absent event.
8. Reopening a dead route without a revival record.
9. Erasing a negative result because a later route looks promising.
10. Changing frozen historical deltas to make current state look cleaner.
11. Fetching live GitHub metadata during deterministic CI and treating it as reproducible state.
12. Letting embeddings, LLM output, or text similarity create claim-bearing authority.
13. Using line numbers as the sole durable source identity.
14. Hashing generated graph products into a recursive self-hash.
15. Replacing existing RHRC registries with generated graph mirrors.
16. Allowing graph validation to weaken existing anti-circularity firewalls.

---

# Appendix G — Required standing queries

A mature RHKG should support queries equivalent to:

- What exact files, declarations, claims, experiments, and dead routes concern concept X?
- Which theorem declarations are used by theorem Y?
- Which registered claims are proved by a declaration introduced in PR N?
- Which routes depend on claim C?
- Which dead routes failed because of premise P?
- Has P changed since that route died?
- Which experiments tested the same mechanism with different evidence classes?
- Which workflow jobs actually ran on the exact theorem head?
- Which results were regressions versus research-producing checks?
- Which current-state axes disagree or remain unresolved?
- What files are not semantically linked?
- What should be read before planning the next PR on concept X?
- What did the last green result make possible that was not possible before?

---

# Appendix H — Adoption baseline

At the adoption base:

    main commit = fcf585f8d4ead741dfd0be2ce1ac9d068e9873f5
    main tree   = ff55f016bf8bf604eef2c9e5d410c0b67bcbd940
    terminal claim = RH_OPEN

The repository already contains the core registries, validation firewalls, retro archaeology machinery, revival discipline, and current-state documentation that RHKG is designed to compose.

This baseline is historical provenance only. It MUST NOT be used as a permanent hard-coded file-count or authority snapshot.

---

# Final constitutional statement

RHKG exists because the repository is now too large and too historically dense for reliable research navigation by memory, filename search, or a handful of README files.

The graph's job is to make the entire accumulated state visible **without changing what any source means**.

Its success condition is not "a prettier map."

Its success condition is:

> **When a new theorem, experiment, or route is proposed, the project can reliably see every relevant formal dependency, research result, dead end, authority boundary, historical prerequisite, and unresolved gap before acting.**

That is the standard this constitution establishes.
