# Frameworks and governed deduction

FFBBP, OoL-MVS and Permansson help this project organize research, preserve
evidence and check how results are used. OPICA connects their bounded interfaces
to exact Lean theorem attempts. **RH, Step 4 and the independent closing
inequalities remain OPEN.**

This guide describes the research implementation at the
[21 November 2026 archive snapshot](https://github.com/HMarcusWH/zeta-23-lean/tree/7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9).
The linked configurations determine exact scope and pins; a documentation page
or a historical green run does not replace current source and CI evidence.
Start with the [repository guide](../README.md) for the mathematical routes and
project history, or [reusing a component](#reusing-a-component) for adaptation
outside this particular attempt. The [reproduction guide](REPRODUCIBILITY.md)
separates a bounded component example from complete production acceptance.

## What each framework does here

| Component | Question it helps answer | Repository implementation |
|---|---|---|
| FFBBP typed assurance | Did the declared reduction preserve the required information, and did every required evidence gate actually pass? | [FFBBP guide](../research/RHRC/ffbbp/README.md), [OPICA adapter](../research/RHRC/ffbbp/opica_composition.py) |
| OoL-MVS operational semantics | Are evidence, premises, witnesses, phases and interface outputs bound to the same declared route and context? | [OoL guide](../research/RHRC/ool/README.md), [OPICA adapter](../research/RHRC/ool/opica_composition.py) |
| Permansson policy adapter | Which affordable action from this frozen finite menu should be attempted next, given the durable attempt history? | [Permansson guide](../research/RHRC/permansson/README.md), [selector](../research/RHRC/permansson/opica_composition.py) |
| Lean and the claim gates | Does the exact proof establish the independently specified proposition under its actual assumptions? | [governed runner](../research/RHRC/integration/opica_composition/README.md), [independent checker](../research/RHRC/integration/opica_composition/evidence.py) |

The common authority boundary is recorded in
[INTEGRATION_BOUNDARY.json](../research/RHRC/integration/INTEGRATION_BOUNDARY.json).
Only the Lean/compiler and required claim-validation gates confer mathematical
proof authority. Conditional results retain their hypotheses. Framework
agreement, graph contact and numerical agreement cannot supply a missing premise.

## The governed OPICA loop

The current runner freezes exact project, package, checker and worker identities.
It retrieves a bounded menu from compiler types and accepts a finite expression
plan. Trusted drivers elaborate and check that plan against an independently
registered target. Candidate data cannot select a different target, checker,
import policy or mathematical world.

```mermaid
flowchart TD
    A[Exact frozen source, targets and compiler inventory] --> B[Bounded composition search]
    B --> C[Frozen finite menu]
    C --> D[Journal and Permansson policy select an action]
    D --> E[Isolated Lean attempt]
    E --> F[Independent replay and expected-type consumer]
    F --> G[FFBBP reconstructs all required evidence gates]
    G --> H[Journal publishes the verified proof packet]
    H --> I[OoL checks exact interface and context bindings]
    I --> J[Checked application export]
```

The implementation is connected in
[service.py](../research/RHRC/integration/opica_composition/service.py).
[Journal](../research/RHRC/integration/opica_composition/journal.py) freezes menus,
records attempt counts transactionally, verifies the event chain and preserves
source generations. Its publication path repeats the independent native checker
and reconstructs four FFBBP gates: `SOURCE`, `KERNEL`, `AXIOMS` and
`INDEPENDENT_EXPECTED_TYPE`.

OoL then checks the actual dependent proof packet, exact context and witness
bindings. Different producer and consumer objects require a checked transport.
[Application records](../research/RHRC/integration/opica_composition/applications.py)
derive their ports from the native packet; callers cannot manufacture implication
by relabeling an association edge.

The Permansson adapter uses least-attempted actions first, then priority, cost
and action ID. The journal supplies the counts. This supports deterministic
selection and conditional fairness over the declared finite menu; it does not
establish globally optimal theorem search or probabilities of discovery.

Search has explicit state, depth and candidate budgets. A resource stop does
not prove a goal unprovable. An empty approved menu leaves the target OPEN.
The runner's [profile](../research/RHRC/integration/opica_composition/PROFILE.json),
[search contracts](../research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json)
and [target registry](../research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json)
define the accepted scope.

## Permansson has three distinct surfaces

1. **Embedded host formalization.**
   [GeneralFramework.lean](../Zeta23/Permansson/GeneralFramework.lean) constructs
   a joint Markov kernel from the policy, physical transition and state-update
   kernels. [Theorem31.lean](../Zeta23/Permansson/Theorem31.lean) establishes the
   path-law existence-and-uniqueness statement of Theorem 3.1. This is a separate
   auxiliary formalization, checked by
   [its own workflow](../.github/workflows/permansson-formal.yml).
2. **Historical external reference.**
   [FRAMEWORK_REGISTRY.json](../research/RHRC/integration/FRAMEWORK_REGISTRY.json)
   records a v0.1.8 external snapshot at `c018f79…` with its historical
   bridge-pending scope. That entry is not the active OPICA selected-provider pin.
3. **Selected OPICA provider.**
   [FRAMEWORK_PROVIDERS.json](../research/RHRC/integration/opica_composition/FRAMEWORK_PROVIDERS.json)
   and [selected_exports.json](../research/RHRC/integration/opica_composition/providers/permansson/selected_exports.json)
   identify the active three-API selection. At this checkpoint it is commit
   `17c315f7df7abf457eb94d393bd526d46da6f6f4`, in the provider's separate Lean 4.34
   environment. The host remains pinned to Lean 4.33.0-rc2.

Those selected APIs establish executable rational value/specification agreement,
an admissible maximizing control with fixed tie breaking, and attainment of the
finite-horizon value by the computed controller. The
[provider runner](../research/RHRC/integration/opica_composition/provider.py)
rebuilds the selected source closure, compiles
[independent consumers](../research/RHRC/integration/opica_composition/providers/permansson/ProviderAudit.lean.in),
audits axioms and repeats the build independently. Provider and host compiled
objects never mix. Admission remains `POLICY_ADAPTER_ONLY`, with
`host_theorem_authority: false` and `model_optimality: NOT_ESTABLISHED`.

## The discovery graph is a separate pipeline

RHKG inventories repository objects and compiler dependencies. Its framework
products help researchers find candidates for a new proof attempt. They do not
run the governed proof loop above or establish theorem composition by reachability.

```mermaid
flowchart TD
    A[Registered compiler dependencies] --> B[RHKG source census]
    B --> C[Lean candidate exactification]
    C --> D[FFBBP snapshot reduction assurance]
    C --> E[Source-only compiler dependency export]
    E --> F[Contact-quotient views]
    D --> G[OoL Phase Atlas]
    F --> G
    G --> H[Research lead for a new exact Lean attempt]
```

[materialize_derived_state.py](../research/RHRC/tools/materialize_derived_state.py)
owns the ordered pipeline and restores previous generated products if a producer
fails. See the [RHKG guide](../research/RHRC/graph/README.md) for graph semantics.

FFBBP's selected `MODULE_VISIBILITY_SNAPSHOT` reduction preserves declared
visibility diagnostics and source-only decisions on the exact finite snapshot.
It supplies navigation cohorts, not mathematical relevance rankings or guarantees
for future repository states. The negative module-only control tests why module
identity alone loses required information.

OoL's atlas uses `THEOREM_VALUE_ERASED_SUPPORT`: it erases theorem proof-body
value edges while retaining type and structure edges and non-theorem support
values. It removes shared support before counting interface-distinctive contact.
A surviving contact is a discovery lead; it must return to exact theorem types
and a new proof attempt.

Use the generated
[FFBBP report](../research/RHRC/ffbbp/generated/RHKG_CANDIDATE_REDUCTION_ASSURANCE.json)
and [OoL report](../research/RHRC/ool/generated/RHKG_OOL_PHASE_ATLAS.json) for their
source-bound counts and dispositions. Historical counts in older handovers
describe their named snapshots.

The later [Round 6 constraint graph](../research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json)
adds an explicit catalogue of joint inputs, alternatives and context. Its
`SURVIVOR_ROUTE` still has the joint open inputs `ACTUAL_UPPER` and
`PAPER_ROUTE_VALIDATION`. The original source-register rows remain provenance
records, excluded from logical premises. An exact source anchor or a path in
this graph does not discharge either input. The
[stored-graph example](EXAMPLES.md#infrastructure-replay) shows that boundary in
a short executable query.

## Reusing a component

The smallest reusable surfaces are the canonical codec, finite-menu selector
and finite evidence/interface checks. The complete governed runner is more
coupled: its target registry, Lean expression grammar, import policy, compiler
exports, sandbox and source contracts describe this repository. Treat a new
application as a new reviewed configuration, with its own independent target
and checker. Renaming RH fields in an old receipt does not establish that the
new experiment passed.

| Component | Inputs you must supply | What can be adapted | Dependencies and evidence boundary |
|---|---|---|---|
| [Canonical codec](../research/RHRC/integration/opica_composition/canonical.py) | Closed JSON records, explicit identity domains and canonical logical paths | A bounded record schema and content identities for another experiment | Python standard library. Hash identity and corruption detection do not establish the truth of a record. The codec rejects floats and arbitrary Python-object fallbacks. |
| [Finite-menu selector](../research/RHRC/permansson/opica_composition.py), `Action` / `select_action` | One source identity, the complete finite eligible menu, trusted attempt counts and a nonnegative integer budget | Action names, costs and reviewed priorities | Python standard library plus the local canonical module. The real journal supplies counts transactionally; a caller-supplied fixture has only demonstration scope. Selection is `POLICY_ADAPTER_ONLY`. |
| [Journal](../research/RHRC/integration/opica_composition/journal.py) | An external SQLite database, source/profile generations, frozen menus and expected revisions | Durable event history, compare-and-swap updates and explicit stale-generation handling | Python `sqlite3` and repository contracts. The verified publication path is coupled to actual native replay; an event hash or `PASS` string cannot replace it. |
| [FFBBP gates](../research/RHRC/ffbbp/opica_composition.py), `verify_required_gates` | An independently defined required-gate inventory, source/run identities, raw evidence and a trusted replay function | The evidence obligations of a new finite experiment | Python standard library plus the codec. Every expected gate must appear exactly once and replay successfully. The replay function belongs to trusted evaluator code. |
| [OoL interfaces](../research/RHRC/ool/opica_composition.py), `verify_interfaces` / `check_context` | Exact producer, consumer, context, witness, source and phase bindings | A new route's interfaces and independently checked transports | Python standard library plus the codec. Open obligations cannot enter as discharged premises; different objects need a checked transport. |
| [Expected-type replay](../research/RHRC/integration/opica_composition/evidence.py), `verify_application` | A frozen snapshot, independent `TargetSpec`, restricted proposal and real prepared worker | The registered target and allowed grammar, through a new contract | Pinned Lean/Mathlib, compiler exports and the worker boundary. It re-elaborates the proposal and then checks a fresh consumer against the expected type, axioms and dependencies. |
| [Graph materializer](../research/RHRC/tools/materialize_derived_state.py) and [constraint queries](../research/RHRC/integration/opica_round6/constraint_graph.py) | Reviewed source inventory, declaration anchors, relation semantics and ordered producers | A catalogue and discovery view for another project | Source parsing and, for canonical compiler-backed products, the actual Lean environment. Reachability is navigation; a source-only census is not compilation. |

### Start with the finite-menu example

Run from the repository root:

```sh
python -B docs/examples/infrastructure_replay.py --part policy
```

This calls the existing `select_action` implementation on three actions. It
demonstrates that a lower attempt count precedes priority, unaffordable actions
are excluded, no affordable action gives an explicit stop, and a policy
intervention cannot change the target inventory. It does not launch a worker or
qualify the external Permansson provider. The
[full walkthrough](EXAMPLES.md#infrastructure-replay) shows the expected output
and a separate query of the stored constraint graph.

For a different application, preserve the distinction between the menu's source
identity and the journal's current generation. Freeze the full menu and attempt
history before selection, record the selected action against that same revision,
and invalidate stale results when the source changes. The production implementation
provides those operations through `Journal` and the service layer; calling the
pure selector alone does not provide transactional dispatch.

### Reuse evidence checking with a real evaluator

The FFBBP and OoL adapters expose replay callbacks because the relevant evidence
may have different native forms. A new integration must supply an evaluator that
actually checks its required artifacts. A callback returning `True`, a matching
digest, or a copied producer status demonstrates only plumbing. Keep synthetic
fixtures in their explicit scope, and keep the expected gate/interface inventory
outside candidate control.

The native proof path in `verify_application` illustrates the stronger contract:
it verifies the source snapshot and exact target, regenerates the restricted
attempt from the proposal, runs it in a fresh process, generates an independently
specified consumer, checks that consumer's actual type and axioms, and verifies
the expected object exists. A changed target, missing export, different source,
resource stop or incomplete evidence remains a distinct result. A new prover
backend would need to implement the corresponding independent check rather than
inherit the Lean label.

The [runner's contracts](../research/RHRC/integration/opica_composition/contracts.py),
[executor](../research/RHRC/integration/opica_composition/executor.py) and
[runtime profile](../research/RHRC/integration/opica_composition/PROFILE.json)
are therefore required reading for extracting the complete service. Its current
Linux worker boundaries and eleven-lane acceptance recipe are documented in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md#8-reproduce-full-governed-acceptance).
The package is a concrete research implementation, not a backend-independent
library already qualified for every new domain.

## Reading evidence without overstating it

- A compiled declaration proves its exact Lean statement, including every hypothesis.
- An independently checked application records one source-bound conditional application.
- A source-only declaration is absent from a registered-root dependency closure;
  that label does not establish independence, novelty or usefulness.
- A finite interval enclosure does not establish a uniform source estimate or
  exact kernel/resonance identity.
- OoL certificate `VALID` authenticates a reviewed evidence binding; its RHRC
  adapter does not certify physical or mathematical truth.
- FFBBP 1.7 assurance does not inherit the separate RUN42C synthetic runtime
  qualification or establish RUN46F execution authority.
- Repeated origins and aliases do not create independent mathematical information.

For current theorem status, follow exact-source compiler and CI evidence and the
required claim gates. For current provider scope, follow the selected-provider
configuration. For framework history, use the versioned references linked in each
framework's guide.

## Citation

Cite Marcus Hermansson's exact repository snapshot and the component paths you
adapt. If you use the embedded Permansson formalization, the selected external
provider, FFBBP or OoL theory, retain their own versioned source references as
well. [CITATION.cff](../CITATION.cff) and the
[citation guide](REPRODUCIBILITY.md#citation) provide the repository format;
[UPSTREAM_README.md](../UPSTREAM_README.md) and [LICENSE](../LICENSE) retain
inherited attribution and terms. This guide does not change the status or
license of an external framework or its included material.
