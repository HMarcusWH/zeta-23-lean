# Stage1 full compiler receipt infrastructure

This is validator/producer infrastructure, not an all100 proof result. The
original100 roots and28 acceptance units remain mandatory. RH, Step4 and the
independent closing inequalities remain OPEN. No full Lean build or all100
compiler receipt was produced in this task. No parent acceptance was created.

## Changed tracked files

- `research/RHRC/integration/opica_followup/build_receipt.py`
- `research/RHRC/integration/opica_followup/validate_contract.py`
- `research/RHRC/integration/opica_followup/tests/test_receipt.py`
- `research/RHRC/integration/opica_followup/tests/test_contract.py`

No frozen input, registry, parent mathematical source, Lean exporter, workflow,
SOURCE_REGISTER, continuation manifest, or parent acceptance capture changed
here. The parent task owns commits, documentation, final manifest pin and pushes.

## New full compiler path

The existing explicit `--preparation-only`41-root producer retains its original
schema, census and meaning. It cannot satisfy the new full receipt reader.

Without `--preparation-only`, `build_receipt.py` attempts the explicit schema
`OPICA_FOLLOWUP_FULL_COMPILER_RECEIPT_V1`. Before invoking Lean it requires:

1. The exact frozen BUILD_SPEC, BUILD_MANIFEST, PUBLIC_ROOTS, PAPER_CROSSWALK,
   PARENT_EXTENSION and PROTECTED_STATE bytes;100 original roots,28 full units,
   all41 mathematical/facade modules plus Validation.
2. A separately reviewed semantic/type record sealed by the hardcoded
   `FULL_REVIEW_SHA256`. This constant is deliberately **None** now. No genuine
   full review exists; changing this must be a reviewed implementation change.
3. The exact current committed head/tree, accepted parent d53dd70.../12691099...
   relationship and clean tracked bytes, recomputed against every Git blob.
4. Actual pinned clean Mathlib and dependency Git checkouts, rather than an
   enclosing repository accidentally satisfying a package pin.
5. Actual facade import reachability; comments cannot manufacture import edges.

Only after these gates, the producer creates a fresh local Git clone outside
the output directory, checks out the exact checked commit with line-ending
conversion disabled, and rechecks its complete source census. Its own
`.lake/build` must be absent. Only manifest-pinned dependency packages share
cache objects, through one explicit package-directory symlink. It removes
inherited Lean paths and disables the Lake artifact cache. It never deletes or
shares the main project's cache. Unsupported symlink privileges fail closed.
Git commands disable lazy fetching. The cold workspace stays outside the
uploadable receipt folder and is retained for inspection, not silently deleted.

Full commands run with one Lean thread. They build every frozen final target
plus the type codec, and compile a deterministic external driver. That driver
is generated from the separately sealed original exporter template, replacing
only its query array and public-module array, and adding fixed module imports.
All root and consumer identifiers pass a code-free ASCII grammar. The driver
hash and complete query inventory are receipt-bound; arbitrary Lean fragments
are not accepted as generator input.

The reader validates every public declaration, constructor, complete type DAG,
approved axiom list, generated-equation provenance and private transitive
TYPE/VALUE/STRUCTURE expansion using the actual existing strict protocol
checker. It rejects duplicate terminators, truncated exports, unreviewed types,
unsupported axioms, missing consumers, omitted public dependencies and hidden
private channels. It requires each assigned expected/physical consumer to have
an actual compiler-use path to its root. That necessary use path does not itself
establish physical meaning; the independent sealed semantic review does that.

It also requires the source-bound original parent projection, all298 claims
and294 bindings, and exact registered dependency lists recomputed through the
complete compiler graph. The immutable parent builder and the reviewed parent
projection validator are separately hash-pinned before loading under unique
Python module identities. Any change to the latter requires an explicit
reviewed pin update; do not silently repin to make a gate pass.

`validate_full_receipt_structure` deliberately returns a status ending
`REPLAY_STILL_REQUIRED`. A matching JSON/log/object bundle is forgeable.
`verify_full_receipt_replay` is the compiler linkage: it executes a second new
cold project clone/build/export and compares all mathematical records, source
identity, complete inventories, semantic seal, cache-isolation policy and
registered dependency provenance. Variable elapsed times/build chatter do not
become theorem identity. Caller-provided contract or review overrides are not
accepted by the reader.

## Independent review record and sealing procedure

The future record belongs under `SOURCE_REGISTER.json.full_receipt_review`.
Its schema is `OPICA_FOLLOWUP_FULL_REVIEW_V1`. It must be authored/reviewed from
the frozen paper clauses and actual Lean expected types, rather than generated
by copying inferred theorem types and declaring that adequate.

Required fields include:

- Status `INDEPENDENT_EXPECTED_TYPES_AND_PHYSICAL_DOMAINS_REVIEWED`, scope
  `FULL_100_ORIGINAL_ROOTS`, primary_roots100, acceptance_units28, exact frozen
  input hashes, and all three OPEN claim flags.
- `source_sha256`: exact defining files for all41 mathematical/facade modules
  and Validation; no omitted or unlisted file.
- `roots`: all100 in frozen order, each full_name, hash of the **entire** frozen
  root object, full type-DAG SHA256, exact canonical expected consumer name,
  nonempty physical_or_domain_consumers, a substantive domain_review, and status
  `FULL_FROZEN_CLAUSES_AND_ACTUAL_DOMAINS_REVIEWED`.
- `consumers`: exact union of expected and assigned domain/physical names,
  each a named theorem in `Zeta23.OPICAFollowup.Validation`, with its explicit
  source, reviewed full type digest and status
  `INDEPENDENT_EXPLICIT_TYPE_AND_DOMAIN_REVIEWED`. Unnamed `example` declarations
  cannot serve as the only machine-linked consumer. Use canonical ASCII names.
- `units`: all28 in frozen order, each hash of its entire frozen crosswalk
  object, status `ALL_CLAUSES_AND_PHYSICAL_DOMAINS_REVIEWED`, and every required
  root's assigned consumer. Root-only coverage cannot omit companion clauses.
- `accepted_registry_extension_sha256`: canonical object digest of the complete
  separately reviewed V2 `accepted_registry_extension` record.
- `registered_type_table_sha256`: canonical object digest of the exact full100
  WORKFLOW_CONTRACT implemented_root_type_sha256 table, identical to reviewed
  root types. Mutable matching metadata alone is not compiler authority.
- `implementation_dependency_amendment_sha256`: canonical digest of the complete
  independently reviewed origin/import refinement record in SOURCE_REGISTER.
- `required_definitions`: all83 mathematical manifest entries in manifest order,
  each exact full_name, original_module, actual_module, kind, type_sha256,
  substantive reason, relocation_amendment_id and status
  `CANONICAL_DEFINITION_SEMANTICS_AND_ORIGIN_REVIEWED`. The code checks origin,
  kind and type against the actual full compiler census. It cannot independently
  infer a transparent alias's intended mathematical semantics.

Canonical object hashing is UTF8 `json.dumps(sort_keys=True, ensure_ascii=False,
separators=(',', ':'))`. Only after independent whole-record review may its
canonical digest be placed in `FULL_REVIEW_SHA256`. The complete synthetic
fixture in test_receipt.py shows the shape but explicitly is not a proof,
semantic review, registry authority or a permitted source for the real seal.
The compiler receipt always keeps independent_human_review NOT_ESTABLISHED;
it never manufactures human approval or release acceptance.

## CLI linkage and deliberately unfinished companions

`validate_contract.py --phase release --formal-receipt ... --output ...`
now runs the full structural reader and an actual fresh cold compiler replay.
Only that executed success allows its static preflight to inspect the fully
registered child context. Supplied status strings cannot enable that branch.
Its full compiler result is reported separately.

Overall release is still unconditionally closed, with explicit errors for:

1. Exact trusted parent acceptance intake and current-tree P0 compiler replay.
2. Source-bound full runtime/regression and numerical dispositions.
3. Canonical generated-state freshness and complete required workflow harvest.

`capture_parent.py --phase acceptance` is untouched and still closed. The
historical PARENT_INTAKE records same-tree compiler/CI evidence; it is not a new
fresh parent compiler receipt. SOURCE_CAPTURE_ONLY is never acceptance.
Parent receipt/workflow provenance needs its own genuine trusted validation
companion. Do not remove these hard blockers by accepting matching editable JSON.

The existing parent projection's protected-footprint/doc amendment interaction
also remains subject to its original validation. New full evidence cannot
paper over a parent projection failure; any necessary bounded correction must
be separately reviewed and tested, then deliberately repinned.

All83 canonical required definitions in the mathematical manifest also must
appear in the compiler public census. Their exact names cannot be replaced by
missing aliases, prose or root-only proof coverage. The independently sealed
review records the original module, actual module, exact declaration kind and
full type digest for each, plus a substantive reason. A module relocation needs
the explicitly recorded current dependency amendment ID, whose entire object
is bound by the full semantic review seal. Unchanged origins require a null
relocation ID. Only DEFINITION, INDUCTIVE or OPAQUE kinds qualify; a theorem
with the same short name cannot stand in for a required definition.

## Evidence and next work

`TEST_EXECUTIONS.json` and full-child-normal/optimized.log record the complete
child suite. Synthetic tests mock Git/runtime/registry side effects explicitly;
the actual100/28 frozen contract, type parser, artifact bytes, review seal,
deterministic driver and consumer linkage use real implementations. Current
checkout firewall probes and exact four source hashes are in
`CURRENT_FIREWALL_PROBES.json`, with both raw rejection logs. The real producer
rejects the unset full review seal before creating a workspace or invoking any
compiler. Release with the historical41 receipt also fails.

Final exact-code result: **185 tests PASS normally and185 PASS with -O**,
including48 receipt tests and62 contract tests. The four source files were
unchanged during both runs. No newly pushed CI workflow or Lean proof build was
executed by this infrastructure task; no workflow status is inferred from local
Python success. Actual failure probes ran at head
`9ccea78eb5ee0c097bde05424e43de58a589b713` with active uncommitted Stage1 work.
Exact source SHA256 values:

| File | SHA256 |
| --- | --- |
| build_receipt.py | 595f6ddca04699c9bc47e61cdcfa3a4c50a6e95d44871cd839b6976e7d688c8a |
| validate_contract.py | 4e0fe00909b8e18018bbb8161598237d8cbbac8c6c67a13eb671526e58190766 |
| tests/test_receipt.py | 05178dec40cd432eb0d2d1707fc9f01073917e16d8b2e3d7f3827afbe6527872 |
| tests/test_contract.py | 5d18b98b74ad3cef78d9d10755f3a665f5385b4e5b0979b57d4ae8f7fd0fb8e1 |

Highest-leverage next steps: complete actual missing mathematics and named
clause consumers; independently review/seal all100 types and all28 domains;
exercise the real cold full path in Linux CI with pinned dependency cache and
no project artifacts; then implement and adversarially test each remaining
release companion. No full production success is claimed by these synthetic
infrastructure tests. No new mathematical implication or RH progress follows
from green validator tests alone.
