# Zeta23 / RHRC

## A Riemann Hypothesis proof checked by Lean and Nanoda

This repository contains a formal proof of Mathlib's exact
`RiemannHypothesis` statement. The proof combines Zeta23's native spectral
construction (Steps 1–3) with credited external arithmetic for Step 4.
Stock Lean accepted the proof, including a fresh replay of its dependency
chain. The separate Nanoda checker accepted the same submitted solution. The
checks ran on revision `75c200a9`. The proof source is on `main`. Independent
human mathematical review and formal project admission remain pending.

- [Terminal Lean proof](Zeta23/RHReference/CompactEnergyAdapter.lean)
- [Pinned verification and reproduction instructions](https://github.com/HMarcusWH/zeta-23-lean/blob/75c200a9c90f96c5b67e468afd1d8a3afeda4188/verification/opica-strict-step4/README.md#reproduction)
- [Lean, Nanoda, and review packet workflow](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/45992350728)
- [Review packet](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/45992350728/artifacts/15236109332)

The repository also contains finite detectors, exact spectral and arithmetic
identities, causal approximation tools, conditional criteria, counterexamples,
and a formal research framework. Many of these results can be used independently.

## Direct arithmetic-window candidate

A new [direct-window route](docs/direct-arithmetic-window.md) extracts complete
cofinal arithmetic windows from the original Alpöge development before its
zero-exclusion consumer. It feeds those windows into the native literal energy,
C1, and the actual generated even/odd trial contradiction. The implementation
and its [separate verification workflow](verification/direct-arithmetic-window/README.md)
are under validation; this new terminal has no completed independent-checker
receipt yet. The checked compact/Perron route and its receipts above retain
their existing scope.

## Choose a reading route

| I want to… | Start here | Continue with |
| --- | --- | --- |
| Inspect the checked RH proof | [Terminal theorem](Zeta23/RHReference/CompactEnergyAdapter.lean) | [Native spectral handoff](Zeta23/RHReference/Step123MomentHandoff.lean), [Step 4 composition](Zeta23/RHReference/CompactEnergyClosure.lean) |
| Understand what the RH attempt built | [Project guide](docs/PROJECT_GUIDE.md) | [Mathematical glossary](docs/MATHEMATICAL_GLOSSARY.md), [paper/result map](docs/RESULTS_AND_FORMALIZATION.md) |
| Read the November 21 research snapshot | [Frozen current state](docs/CURRENT_STATE.md) | [Final arithmetic routes](research/RHRC/integration/opica_round6/README.md), [earlier closure alternatives](research/RHRC/integration/opica_round4/CLOSURE_OBLIGATIONS.json) |
| Reuse a theorem or technique | [Reusable components](docs/REUSABLE_COMPONENTS.md) | [Worked examples](docs/EXAMPLES.md), [reproduction recipes](docs/REPRODUCIBILITY.md) |
| Inspect the Lean source and checks | [Repository map](docs/REPOSITORY_MAP.md) | [Results and formalization](docs/RESULTS_AND_FORMALIZATION.md), [reproducibility](docs/REPRODUCIBILITY.md) |
| Understand or adapt the research tooling | [Framework guide](docs/FRAMEWORKS.md) | [Governed runner](research/RHRC/integration/opica_composition/README.md), [graph guide](research/RHRC/graph/README.md) |
| Learn from failed approaches | [Failure lessons](docs/PROJECT_GUIDE.md#what-failed-and-what-would-justify-reopening-it) | [Countermodels](research/RHRC/countermodels/README.md), [dead-route records](research/RHRC/DEAD_ROUTES.md) |

Contributors and AI agents should read [AGENTS.md](AGENTS.md) and the
[agent guide](docs/AGENT_GUIDE.md) before changing source or claims.

## What is in the repository

The project builds on [Anthropic's Zeta23](https://github.com/anthropics/zeta-23-lean),
which formalizes *More than two thirds of the zeros of the Riemann zeta function
are simple and on the critical line*. That upstream theorem has a different
scope from the fork's RH programme. The [upstream README](UPSTREAM_README.md),
[upstream audit](UPSTREAM_AUDIT.md), [LICENSE](LICENSE) and [NOTICE](NOTICE)
preserve its statements, provenance and attribution.

| Part | What was built | Entry point |
| --- | --- | --- |
| Upstream analytic and linear algebra foundations | Zeta and Dirichlet zero-proportion results, explicit-formula inputs, Hermitian linear algebra and independent comparator statements | [Upstream account](UPSTREAM_README.md), [comparator](comparator/README.md) |
| Finite Weil / CCM mathematics | Canonical finite forms, normalization, boundary-flat carriers, parity maps, Schur/contact calculus and source identities | [Project guide](docs/PROJECT_GUIDE.md), [CCM source](Zeta23/CCM) |
| Exceptional-zero and Step 1–3 construction | A hypothetical actual off-line zero produces a packet retaining its detector, finite image, source and quantitative consequences | [Complete output](Zeta23/ExceptionalZero/Step123CompleteOutput.lean), [typed consumer](Zeta23/RHRC/Step123CompleteOutputConsumer.lean) |
| OPICA and native follow-up | Obstruction transport, source transforms, window rates, Fourier/co-Poisson results, observations and their costs | [Original OPICA](research/RHRC/integration/opica/README.md), [follow-up](research/RHRC/integration/opica_followup/README.md) |
| Rounds 2–4 | Causal Gram/filter certificates, common-aperture parity negativity, newborn witnesses, signed spectral/source budgets and conditional closure consumers | [Package index](research/RHRC/integration/README.md), [Round 4](research/RHRC/integration/opica_round4/README.md) |
| Arithmetic frontier and Round 5 | Moment-slice bounds, zero-strip rate equivalences, exact finite certificates and a parity-moment exact sequence | [Frontier guide](research/RHRC/integration/opica_round4/arithmetic_frontier/README.md), [parity bridge](Zeta23/OPICARound5/ParityMomentBridge.lean) |
| Round 6 finite arithmetic | Native signed cells, prime-factor paths, survivor and partner accounting, parity-deficit products and finite stopping trees | [Round 6 guide](research/RHRC/integration/opica_round6/README.md), [finite source](Zeta23/OPICARound6/PrimeFactorPaths) |
| Research infrastructure | Source-bound evidence, bounded proof composition, independent consumers, finite-menu selection and dependency/constraint graphs | [Framework guide](docs/FRAMEWORKS.md), [repository map](docs/REPOSITORY_MAP.md) |

Package numbers are development layers. They are not the four mathematical
steps, percentages of a proof, or interchangeable verification scopes.

## The proof route

RH says that every nontrivial zeta zero has real part `1/2`. This programme starts
with a hypothetical actual zero away from that line and tracks what it forces.

| Step | Mathematical role | Boundary |
| --- | --- | --- |
| **1. Fingerprint** | Produce a sign-sensitive obstruction while retaining source and multiplicity. | Detection does not exclude the zero. |
| **2. No-hide** | Show that suitable canonical finite detectors must reveal the obstruction. | Existence of a negative witness does not establish positivity of all detectors. |
| **3. Synchronized tracking** | Carry the same source lineage through finite, spectral, Fourier, arithmetic and causal descriptions. | An exact identity or transport does not supply an independent upper bound. |
| **4. Contradiction** | Apply a credited fixed-strip zero-free estimate. A Perron transfer turns it into a ramp-energy upper bound. The native comparison gives bounds contradicted by the original even and odd witnesses. | The checked proof uses the supplied arithmetic. |

The proof uses [`principal_fixed_strip`](Zeta23Arithmetic/NativePrincipal.lean)
at one threshold. The fully quantified arithmetic theorem is equivalent to RH.
The [arithmetic port notice](Zeta23Arithmetic/PORT_NOTICE.md) credits the
upstream work of Levent Alpöge with Claude and Anthropic.

The [project guide](docs/PROJECT_GUIDE.md) develops the native argument, including a
same-aperture, same-cutoff even/odd ground example. Its four modern Paths A–D
cover complete signed observation, causal approximation, detector/contact energy
and pole-neutral parity geometry. The final November work makes several signed
arithmetic targets and their quantifiers more explicit. It also distinguishes
finite Lean transfer results from growing-horizon arguments that remain at
paper level.

## Using results outside this attempt

Start with the [component catalogue](docs/REUSABLE_COMPONENTS.md), which separates
abstract statements, source-specific constructions and research infrastructure.
Promising entry points include finite Gram witnesses, Schur derivative and
kernel-safe completion formulas, analytic-jet identities, exact-data positivity
certificates, weighted finite identities and stopping-cover duality.

Mathematical portability and software packaging are separate. Some modules have
small Mathlib-only import surfaces; a generic statement elsewhere may import a
large part of the zeta development. A new application must retain the theorem's
hypotheses or prove the adapter that changes them. The
[examples](docs/EXAMPLES.md) and [reproduction guide](docs/REPRODUCIBILITY.md)
show how to inspect that boundary.

## Read a claim with its evidence

| Description | What to inspect |
| --- | --- |
| Formal theorem, conditional implication or equivalence | Exact Lean declaration, all hypotheses, source pin, consumer and axiom/compiler receipt |
| Paper theorem or composition | Manuscript version, proof location and correspondence to formal ingredients |
| Finite certificate | Complete input domain, arithmetic method and independent reconstruction |
| Numerical or search observation | Tested range, uncertainty, configuration and scientific disposition |
| Counterexample or negative control | The precise inference refuted and the assumptions retained |
| Open target | The missing proposition and its quantifiers |

The [result map](docs/RESULTS_AND_FORMALIZATION.md) records these distinctions at
result level. A `FINAL` or `PROOFREAD` filename is not a referee report. A green
historical replay retains its historical scope, and a graph contact is not a
mathematical implication. The [authority policy](research/RHRC/DOCUMENTATION_AUTHORITY.md)
explains how source, contracts, evidence and narrative relate.

## Build, reproduce and cite

Reproduce the terminal proof with the
[pinned strict instructions](https://github.com/HMarcusWH/zeta-23-lean/blob/75c200a9c90f96c5b67e468afd1d8a3afeda4188/verification/opica-strict-step4/README.md#reproduction).
They reconstruct the checked Lean 4.35.0 and Mathlib source tree.

The default `lake build` follows the inherited [Zeta23 root](Zeta23.lean); it does
not compile every research module in the repository. Use the
[reproducibility recipes](docs/REPRODUCIBILITY.md) for a named theorem, package,
finite replay or full governed acceptance. Compiler/package pins live in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
Historical replay, source-inventory checks and fresh proof checks have distinct
roles.

The [paper index](papers/README.md) and
[manifest](papers/MANIFEST_2026-11-21.json) retain the original PDF identities and
hashes. Cite a particular result with its paper version or source commit, and
retain upstream attribution when using inherited work. See [CITATION.cff](CITATION.cff)
and the [archive overview](docs/RESEARCH_ARCHIVE_2026-11-21.md).

## Historical records

The [November 21 research snapshot](docs/CURRENT_STATE.md) records how the
programme stood at archive commit `7597acd`. The
[original manuscripts](papers/README.md) preserve the written research.

[FORK_NOTES.md](FORK_NOTES.md), [AUDIT.md](AUDIT.md), dated handovers and old
research deltas preserve how the programme developed. Their former “current”
labels describe those checkpoints. The preserved block below is a historical
Control-v2 receipt; the [21 November overview](docs/CURRENT_STATE.md) is the
human entry point for this archive.

<details>
<summary>Historical Control-v2 snapshot: frozen PR #287 scope</summary>

This preserved machine block is a historical receipt, not current PR routing.

<!-- RHRC_CURRENT_STATE_BEGIN -->
## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #287
- validated final head = 40495f39b7510b49a7fe3493b42d9fe3880d6d22
- merge commit = ecc6450f28eb6aed944bda8fe9a09296d033fc3e
- tree = a105ffd52c96cd0c39712dcdba45e967282efc9d
- status = MERGED_GREEN_THEOREM_STATE
- PR #275 full-space small-aperture coercive base = PROVED
- PR #276 exact legal successor ground >= 1 on 0 < L <= 1/512 = PROVED
- fixed-N production continuity = PROVED_MERGED_PR_278
- same-N off-line-zero contact = PROVED_MERGED_PR_278
- PR #284 compressed contact calculus = PROVED_MERGED_PR_284_C2_AND_INHERITED_FIRST_VARIATION; F04_PAIR_BALANCE_AND_FRONTIER_PROMOTED_AFTER_MERGED_PR_287
- PR #285 post-284 source-inertia package = PROVED_MERGED_PR_285
- PR #287 post-285 M70-M77 build = PROVED_MERGED_PR_287
- PR #272 CofinalCanonicalArithmeticCertificates <-> Mathlib RiemannHypothesis = PROVED / AUDIT-ONLY
- RH = OPEN

CURRENT RESEARCH FRONTIER
- current candidate PR = #NONE / NO_OPEN_CANDIDATE_PR
- candidate theorem-validation head = NONE
- candidate theorem-validation status = NONE
- merged experimental research evidence = PR #273 / CERTIFIED_CURRENT_PRIME_GROUND_RESPONSE
- fixed-N sign opposition = PROVED_MERGED_PR_277
- global ground propagation strength = RH_SUFFICIENT_AUDIT_PROVED_PR_277
- uniform domination strength = RH_SUFFICIENT_AUDIT_PROVED_PR_277
- active obstruction = OBS-060_GROUND_SPECTRUM_FIRST_CROSSING_BARRIER
- active subobligation = OBS-060O_CONTACT_CONDITIONED_PRODUCTION_SATURATION_EXCLUSION
- F04 production derivative authority = PROVED_MERGED_PR_287
- M74 canonical secular instantiation = PROVED_MERGED_PR_287
- next research target = POST285_CANONICAL_SECULAR_RAY_PRIME_FREE_F04_AND_FULL_ARITHMETIC_SOURCE_INEQUALITY
- required new information = INDEPENDENT_FULL_ARITHMETIC_SOURCE_RESTRICTION_ON_THE_RESOLVENT_SELECTED_CONTACT_RAY
- RH-sufficient terminal formulations are not counted as independent sub-RH progress

FRAMEWORK / GRAPH STATE
- PR #270 = FFBBP 1.7 / OoL-MVS 2.7.7 framework architecture authority
- post-#276 exactified source-only theorem/lemma roots = 711
- post-#276 FFBBP source-only module cohorts = 212
- post-#276 OoL theorem-value-erased frontier contacts = 522
- post-#276 RHKG relations = 311826
- framework output -> Lean theorem authority = FORBIDDEN

RESEARCH / CONTROL FIREWALL
- latest independent bounded research evidence = PR #223
- merged first-contact atlas evidence = PR #273 / EXPERIMENTAL_SIGNAL_ONLY
- frozen Control-v2 semantic authority = PR #117
- selected formal first break = E4A4-SCHUR-FB-05 (historical/frozen control semantics)
- R003 phase = DISCOVERY
- confirmatory execution = NOT AUTHORIZED
- terminal claim = RH_OPEN
<!-- RHRC_CURRENT_STATE_END -->

</details>
