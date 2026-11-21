# Reproducing a result or a research check

Choose the check that answers your question. Reading a declaration, replaying an
exact finite calculation, compiling a module and qualifying a complete release
produce different evidence. This guide gives a short path to each and names
what its result can establish.

The research and manuscript baseline is
[`7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9`](https://github.com/HMarcusWH/zeta-23-lean/tree/7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9)
(21 November 2026 archive), tree
`9248b76d7aff60aab3bb775c4be9750dc6006003`. The documentation successor is a
separate reviewed change on top of that baseline. Record the actual checkout
for a new run. **RH, Step 4 and the independent closing inequalities remain OPEN.**

## What each check establishes

| Check | Positive result means | Scope still to establish separately |
|---|---|---|
| Read a source declaration | You have inspected the literal proposition and its binders | Fresh elaboration, transitive axioms, source identity and external mathematical interpretation |
| Exact source-scope check | The checkout satisfies the reviewed path/hash policy | Compilation, canonical generated-state freshness and mathematics |
| Exact finite Python replay | The specified finite computation reproduces its recorded result | An asymptotic estimate or a Lean theorem about the native source |
| Numerical/Arb replay | The selected bounded computation satisfies its numerical contract | Any unproved bridge from native entries to enclosures, exact kernel identity or uniform estimate |
| `lake build` | The configured default target and its imports build | Later RH module families outside that target |
| Named module and typed consumer | Those exact declarations elaborate in that environment | Complete registered-root coverage and independent release gates |
| Axiom audit | The selected declarations have the reported transitive axioms | Whether their hypotheses, definitions and domains match the intended informal claim |
| Full comparator run | Its selected trusted statements match the checked solution exports | Unselected topics and later RH work |
| Full governed acceptance | All required current-source lanes and independent replays meet the package contract | Independent specialist review and any explicitly OPEN scientific premise |

`PROVED` in a source catalogue is a recorded disposition, not a fresh compiler
receipt. A green workflow wrapper also needs its individual job, consumer,
scientific disposition and completeness read. The
[authority guide](../research/RHRC/DOCUMENTATION_AUTHORITY.md) explains which
contracts and dated records govern each kind of claim.

## Before running a command

Run the recipes from the repository root. Record the source before and after:

```sh
git rev-parse HEAD 'HEAD^{tree}'
git status --short
cat lean-toolchain
python --version
```

Retain the command, exit code, full log, operating system and dependency versions
with any result you report. A working-tree edit matters even when `HEAD` is
unchanged. Store new logs, scratch consumers and receipts outside the checkout;
the governed runner rejects unreviewed files in its exact source inventory.

A full clone contains large manuscript and evidence archives. A blob-filtered
or sparse checkout is useful for reading, but omitted files are still tracked
repository content. For example, the bounded graph example needs the committed
`research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json`; a checkout of only
Markdown, Lean and Python will omit it. Add that exact tracked path through your
sparse-checkout configuration before running the example. Use `git ls-tree -r
--name-only HEAD` for a complete frozen inventory, rather than counting local
files. Full acceptance also needs the required Git history and runtime; a
source-only CORE export does not supply either automatically.

## 1. Read the source without installing Lean

Start with the [repository map](REPOSITORY_MAP.md),
[reusable components](REUSABLE_COMPONENTS.md) and
[result crosswalk](RESULTS_AND_FORMALIZATION.md). Each identifies a source file
and declaration. Read the full type, including variables established earlier in
the namespace, then follow its imported definitions. A file name is not
necessarily a namespace: most Round 2 declarations live directly in
`Zeta23.OPICARound2`.

For the paper archive, use [papers/README.md](../papers/README.md) and its
Git-blob/byte manifest. For later arithmetic work, start at the
[12 November frontier handover](../research/RHRC/integration/opica_round4/arithmetic_frontier/HANDOVER_2026-11-12.md),
[Round 5 bridge](../Zeta23/OPICARound5/ParityMomentBridge.lean) and
[Round 6 guide](../research/RHRC/integration/opica_round6/README.md).
The forty-three PDFs do not exhaust those later developments.

This is sufficient to inspect statements, locate missing hypotheses and compare
routes. It is not a substitute for elaboration or a transitive axiom check.

## 2. Run a small exact calculation

The documentation examples require only Python 3.10 or newer:

```sh
python -B docs/examples/exact_examples.py
python -B docs/examples/infrastructure_replay.py
```

The [examples guide](EXAMPLES.md) explains all seven examples and their output.
The first script uses `fractions.Fraction`. The second queries a stored graph
and calls the real finite-menu selector on a small fixture. Neither writes
generated research state, runs a proof search or emits a release receipt.

For a replay of **committed research evidence**, the following standard-library
script checks three specified genuine rough squarefree labels and a negative
control, then byte-compares its result with the committed JSON:

```sh
python -B research/RHRC/integration/opica_round6/evidence/step4-parity-deficit-2026-11-20/check_divisor_halves.py
python -B -O research/RHRC/integration/opica_round6/evidence/step4-parity-deficit-2026-11-20/check_divisor_halves.py
```

Expected success output in each mode: `Verified DIVISOR_HALVES_EXACT.json`.
The receipt's scope is three individual labels in whole terminal shells. It
does not execute an asymptotic selector or prove a uniform theorem. Supply
`--output /absolute/external/path/result.json` to export newly calculated bytes
after the comparison succeeds. `--write` regenerates a tracked product and
belongs to an explicitly reviewed update, not ordinary reproduction.

## 3. Prepare the pinned Lean environment

The host pins are:

| Component | Exact pin or source of truth |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` in [lean-toolchain](../lean-toolchain) |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` in [lakefile.toml](../lakefile.toml) |
| Transitive Lake packages | [lake-manifest.json](../lake-manifest.json) |
| Full governed Python runtime | Python 3.13.5 in [rhrc_opica_composition.yml](../.github/workflows/rhrc_opica_composition.yml) |
| Python numerical checks | [Round 2 lock](../research/RHRC/integration/opica_round2/python-checks.lock), [follow-up lock](../research/RHRC/integration/opica_followup/python-checks.lock), [RHRC requirements](../research/RHRC/requirements.txt) |
| Selected external Permansson provider | Commit `17c315f7df7abf457eb94d393bd526d46da6f6f4`, with its own Lean 4.34.0 environment |

With `elan` installed, use the host pin and inspect the selected compiler:

```sh
elan toolchain install leanprover/lean4:v4.33.0-rc2
lake env lean --version
```

The optional Mathlib cache command is `lake exe cache get`. It can download a
substantial cache; coordinate one owner for broad cache-writing work. Package
downloads require network access. Use native objects for the actual platform;
Linux `.olean`/native outputs are not a Windows runtime. An exported dependency
cache without its expected Git metadata needs the documented local package
overrides, not a change to the upstream pins.

Do not run `lake update`, alter the Mathlib revision, reset a shared cache or
reuse stale objects as evidence that modified source compiled. Provider Lean
4.34 and host Lean 4.33 objects stay separate. The selected-provider qualification
does not confer host theorem authority; see [frameworks](FRAMEWORKS.md).

## 4. Build the inherited headline target

```sh
lake build
```

In this repository, `defaultTargets = ["Zeta23"]`. The root
[Zeta23.lean](../Zeta23.lean) imports twelve inherited headline modules. Under the
pinned Lake version, a library's default roots are its own name and its default
globs are `Glob.one` for those roots; the default build follows their imports.
See [LeanLibConfig.lean at the pinned release](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/lake/Lake/Config/LeanLibConfig.lean)
and [Lake's library build](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/lake/Lake/Build/Library.lean).

The frozen comment-aware import census gives 313 project modules in that root's
closure. It does not include the CCM, ExceptionalZero, OPICA, RHRC, Spectral or
Permansson families. This count is source-graph evidence, not a fresh build
receipt. Build a named later module or run its package workflow to cover it.

For a quick axiom inspection of the inherited seventeen A–E statements:

```sh
lake build Solution
lake env lean comparator/PrintAxioms.lean
```

Review the printed axiom sets; the allowed standard axioms are `propext`,
`Classical.choice` and `Quot.sound`. A zero-exit process alone does not establish
that its output matches the required inventory.

For **full comparator verification**, follow
[comparator/README.md](../comparator/README.md), its trusted challenge definitions
and per-topic configuration. Let comparator build in its own sandbox for a run
you intend to rely on; do not substitute a prebuilt solution. The trusted
challenge files deliberately contain `sorry` statement templates, while the
solution exports are checked separately. Those templates are not unfinished
project proofs. PairCeiling's `EnclOK` hypothesis is explained in the retained
[upstream README](../UPSTREAM_README.md) and [upstream audit](../UPSTREAM_AUDIT.md);
it is not an unconditional theorem or a claim supplied by the fork's front page.

## 5. Check a named finite module and its consumers

A low-dependency starting point is the exact certificate theorem:

```sh
lake build Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness
lake env lean Zeta23/OPICARound4/ArithmeticFrontier/FiniteCertificateSoundness.lean
```

Its [worked example](EXAMPLES.md#positivity-certificate) includes an optional
generic consumer. For the complete finite Round 6 interface, use:

```sh
lake build Zeta23.OPICARound6.PrimeFactorPaths.Verify
lake env lean -DwarningAsError=true -j2 -s262144 Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean
```

[Verify.lean](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean) checks 73 finite
statements at the frozen research baseline. The
[Round 6 workflow](../.github/workflows/rhrc_opica_round6.yml) additionally splits
compiler ownership and axiom checks into `round6`, `prior-parity` and
`other-history`, and checks negative type controls. Those are separate parts of
the evidence. A module build does not replace them.

For an individual result, inspect its full type, create an independently written
expected-type consumer and print its transitive axioms. Keep any output outside
the tracked source tree and retain the actual source/hash/compiler binding.
The complete Step 1–3 consumer recipe is in
[example 6](EXAMPLES.md#step123-packet).

<a id="round-6-graph-and-finite-replays"></a>
## 6. Check the Round 6 graph and finite replays

With the committed JSON products and referenced source material present:

```sh
python -B research/RHRC/integration/opica_round6/constraint_graph.py --explain SURVIVOR_ROUTE
python -B research/RHRC/integration/opica_round6/constraint_graph.py --explain P303_OPPOSED_PRODUCT_ROUTE
python -B research/RHRC/integration/opica_round6/constraint_graph.py --explain N20_NESTED_ROUTE
python -B research/RHRC/integration/opica_round6/constraint_graph.py --check --check-rhkg
```

Unlike the stored-product documentation example, these CLI queries rebuild the
constraint graph from its catalogue and verify the historical-register binding
before answering. `--check` compares the product bytes; `--check-rhkg` also
checks its source identities against the committed canonical RHKG products.
Neither operation compiles Lean. The source anchors in the catalogue receive
their own compiler checks in the workflow.

Read `depends_on` as joint inputs, `alternatives` as alternative routes and
`context` as navigation with no inferential force. Statuses do not propagate
automatically through reachability. The original source-register dispositions
remain distinct from their relevance to closure. In particular, the survivor
route still requires both `ACTUAL_UPPER` and `PAPER_ROUTE_VALIDATION`.

The [Round 6 README](../research/RHRC/integration/opica_round6/README.md#reproduce-the-graph-and-finite-checks)
lists the full bounded replay suite: divisor halves, cofactor pairs, fingerprint
counts, geometry, selected-pair controls, stopping cuts, disjoint cuts, divisor
spacing, Buchstab transport and cone parity. Each receipt specifies its actual
population, horizon, normalization and negative controls. Running all of them
still does not prove the growing-horizon arithmetic upper.

## 7. Check source policy and generated-state freshness

The documentation successor accounts explicitly for the archive and this reviewed
documentation delta. Run:

```sh
python -B -m research.RHRC.integration.documentation_2026_11_21.source_scope --check
python -B -m research.RHRC.integration.opica_composition.cli inspect --output /absolute/external/path/source-inspection.json
```

Choose a fresh external output file for `inspect`. Its result is a source
inspection, not a proof build. Full `--check` requires a clean committed checkout,
hashes every tracked working-tree blob without Git clean/EOL filters, and rejects missing files, `skip-worktree`
and `assume-unchanged` index states. A sparse clone can instead inspect committed
Git objects without claiming a complete working tree:

```sh
python -B -m research.RHRC.integration.documentation_2026_11_21.source_scope --check-tree
```

That mode returns `PASS_COMMITTED_TREE_SCOPE_ONLY`; production uses the full
working-tree validation. The successor preserves the historical validators
and their pinned inputs; it does not broaden an old policy to accept arbitrary
files. The original Round 6 policy predates the paper-archive commit, so applying
that historical policy directly to the archive can report an inventory mismatch
even when its previously declared blobs are unchanged.

Canonical generated-state freshness is a **separate** requirement:

```sh
python -B research/RHRC/tools/materialize_derived_state.py --check
```

This checks the ordered RHKG, candidate, dependency, contact, FFBBP and OoL
products. It can require real compiler exports and the complete pinned runtime;
it is not merely a Markdown or JSON parser. A source-scope pass does not assert
that this command has passed. `--write` runs the controlled regeneration path,
with rollback of prior generated products on a producer failure. Regeneration
changes source-bound outputs and must be reviewed and checked before acceptance.

The documentation workflow has a separate, branch-scoped `canonical-refresh`
job. It uses the pinned Lean environment, runs the unchanged materializer with
`--write` followed by `--check`, and exports a candidate patch only if every
change belongs to the existing 77 active generated paths. It does not push the
patch or grant acceptance to the original stale tree. Apply/review the patch
on its exact input head, then run the ordinary current-source gates on the
resulting commit. The ordinary documentation job checks source, links and finite
examples independently of that compiler-backed regeneration.

Use [the successor contract](../research/RHRC/integration/documentation_2026_11_21/README.md)
for its exact inventory and current freshness disposition. Do not hand-edit a
generated graph, relax unknown-file classes, relabel a failed receipt or copy an
older result to make a current check appear successful.

## 8. Reproduce full governed acceptance

The executable contract is
[rhrc_opica_composition.yml](../.github/workflows/rhrc_opica_composition.yml),
with runtime provisioning in
[opica4-runtime/action.yml](../.github/actions/opica4-runtime/action.yml) and
the [runner README](../research/RHRC/integration/opica_composition/README.md).
Inspect the CLI before preparing a run:

```sh
python -B -m research.RHRC.integration.opica_composition.cli --help
```

The eleven required lanes are `CONTRACT`, `PARENT_REGRESSION`,
`CURRENT_COMPATIBILITY`, `COMPOSITION_FORMAL`, `SEMANTIC_NEGATIVES`,
`FRAMEWORK_ADAPTERS`, `PROVIDER_SELECTED`, `REPLAY_CAMPAIGN`, `GENERATED_STATE`,
`MATHEMATICAL_SUPPORT` and `SOURCE_NUMERICS`. Full acceptance independently
reconstructs their raw evidence for the same checkout, run and attempt. An
acceptance receipt cannot supply its own missing inputs. Earlier jobs cannot
fill missing lanes in a later attempt; rerun all required jobs together.

Production uses Linux with read-only source/package/toolchain mounts, isolated
network and process namespaces, a hard 4 GiB cgroup memory ceiling and a hard
4 GiB output tmpfs. The separate virtual-address ceiling is 64 GiB. Exact
process, CPU, file and wall-time budgets are bound into the runtime contracts.
Windows execution and portability candidates remain development evidence unless
the actual production qualification says otherwise. Do not copy hosted-runner
disk-reclamation commands onto a personal machine.

The provider lane builds the separately pinned Permansson environment and its
independent selected consumers. It never mixes host/provider objects. The
native producer and independent replay must both actually run; transport,
hashing, fixture tests and a successful wrapper are insufficient substitutes.

This guide does not report a fresh complete acceptance run. The documentation
update executed the small Python examples and the named finite replay, while
Lean compilation, canonical generated-state checking and full production
acceptance require their own recorded evidence.

## Workflow index

The frozen research snapshot contains **46 workflow files**. The tables below
account for each by role; they are an inventory, not a table of successful runs.
Some are manual, reusable, resource-heavy or capable of publishing generated
updates. Read their inputs and guards before dispatch. The documentation update
adds [documentation.yml](../.github/workflows/documentation.yml) for the reviewed
source/navigation/example checks and the separately scoped canonical refresh
candidate described above; neither confers theorem authority.

### Package and auxiliary formalization gates — 10

| Workflow | Evidence or operation |
|---|---|
| [permansson-formal.yml](../.github/workflows/permansson-formal.yml) | Embedded Permansson formalization, separate from the selected external provider |
| [rhrc.yml](../.github/workflows/rhrc.yml) | General RHRC Python, compiler-receipt, normalization and Lean jobs |
| [rhrc_closure_campaign.yml](../.github/workflows/rhrc_closure_campaign.yml) | Closure-campaign integrity, module groups, binding/strength/contact and first-crossing checks |
| [rhrc_opica.yml](../.github/workflows/rhrc_opica.yml) | Original OPICA contract, formal, regression, dependency and component checks |
| [rhrc_opica_followup.yml](../.github/workflows/rhrc_opica_followup.yml) | Native follow-up original-contract and aggregate/generated/research gates |
| [rhrc_opica_round2.yml](../.github/workflows/rhrc_opica_round2.yml) | Round 2 exact-source core, controls, ancestry, aggregate and acceptance |
| [rhrc_opica_round3.yml](../.github/workflows/rhrc_opica_round3.yml) | Scoped current-source formal, runtime-regression and source-evaluator acceptance |
| [rhrc_opica_composition.yml](../.github/workflows/rhrc_opica_composition.yml) | Eleven-lane current governed acceptance and separate historical baseline replay |
| [rhrc_opica_round6.yml](../.github/workflows/rhrc_opica_round6.yml) | Constraint graph, bounded finite replay and disjoint compiler-audit groups |
| [rhrc_contact_quotient.yml](../.github/workflows/rhrc_contact_quotient.yml) | Post-279 contact-quotient research and its checks |

### Earlier arithmetic and geometry diagnostics — 12

| Workflow | Evidence or operation |
|---|---|
| [rhrc_post190_canonical_realizability.yml](../.github/workflows/rhrc_post190_canonical_realizability.yml) | Canonical realizability diagnostic |
| [rhrc_post192_parity_trajectory_rigidity.yml](../.github/workflows/rhrc_post192_parity_trajectory_rigidity.yml) | Parity-trajectory rigidity investigation |
| [rhrc_post194_parity_trajectory_sharp_enclosure.yml](../.github/workflows/rhrc_post194_parity_trajectory_sharp_enclosure.yml) | Sharp trajectory enclosures |
| [rhrc_post196_q14_residual_cell_replay.yml](../.github/workflows/rhrc_post196_q14_residual_cell_replay.yml) | Q14 residual-cell replay |
| [rhrc_post198_q14_parity_source_mechanism.yml](../.github/workflows/rhrc_post198_q14_parity_source_mechanism.yml) | Q14 parity-source mechanism |
| [rhrc_post200_q14_discrepancy_mechanism.yml](../.github/workflows/rhrc_post200_q14_discrepancy_mechanism.yml) | Q14 discrepancy mechanism |
| [rhrc_post202_q14_composite_parity_gap.yml](../.github/workflows/rhrc_post202_q14_composite_parity_gap.yml) | Composite parity-gap investigation |
| [rhrc_post204_pair_d_structural_countermodel.yml](../.github/workflows/rhrc_post204_pair_d_structural_countermodel.yml) | Pair-D structural countermodel |
| [rhrc_post214_kernel_dual_geometry.yml](../.github/workflows/rhrc_post214_kernel_dual_geometry.yml) | Kernel-dual geometry investigation |
| [rhrc_post222_biregular_zero_shift_scalar.yml](../.github/workflows/rhrc_post222_biregular_zero_shift_scalar.yml) | Biregular zero-shift scalar investigation |
| [rhrc_post268_audit.yml](../.github/workflows/rhrc_post268_audit.yml) | Audit, runner regressions and extended harvest |
| [rhrc_post272_first_contact_atlas.yml](../.github/workflows/rhrc_post272_first_contact_atlas.yml) | First-contact atlas investigation |

### Contact frontier, Step 3 and Step 1–3 output — 13

| Workflow | Evidence or operation |
|---|---|
| [rhrc_post280_saturation_frontier.yml](../.github/workflows/rhrc_post280_saturation_frontier.yml) | Production Lean frontier and research measurement |
| [rhrc_post281_generated_contact_frontier.yml](../.github/workflows/rhrc_post281_generated_contact_frontier.yml) | Generated/production contact Lean, research and Arb lanes |
| [rhrc_post282_contact_calculus.yml](../.github/workflows/rhrc_post282_contact_calculus.yml) | Compressed/contact calculus, calibration and Arb balance |
| [rhrc_post284_source_inertia.yml](../.github/workflows/rhrc_post284_source_inertia.yml) | Full K3, source-inertia Lean and source falsification |
| [rhrc_post287_focused.yml](../.github/workflows/rhrc_post287_focused.yml) | Focused Step 3 and modified-prime checks |
| [rhrc_post287_numerical.yml](../.github/workflows/rhrc_post287_numerical.yml) | WP2 K2 and WP4 K2/K3/fourth-order numerical lanes |
| [rhrc_post287_wp4_full_continuum.yml](../.github/workflows/rhrc_post287_wp4_full_continuum.yml) | Manual full-continuum sharding and aggregation |
| [rhrc_post287_wp6.yml](../.github/workflows/rhrc_post287_wp6.yml) | Bounded signed-ray investigation |
| [rhrc_post290_k3_completion.yml](../.github/workflows/rhrc_post290_k3_completion.yml) | Manual D2 SECOND continuation |
| [rhrc_post290_step123_output.yml](../.github/workflows/rhrc_post290_step123_output.yml) | Step 1–3 Lean components, exact controls and native observations |
| [rhrc_post290_unrun460.yml](../.github/workflows/rhrc_post290_unrun460.yml) | Guarded SECOND460 search waves and fresh checker batches |
| [rhrc_post290_unrun460_check_batch.yml](../.github/workflows/rhrc_post290_unrun460_check_batch.yml) | Reusable fresh-checker batch invoked by the preceding campaign |
| [rhrc_post292_d2_frozen_checker_only.yml](../.github/workflows/rhrc_post292_d2_frozen_checker_only.yml) | Consent/freeze verification, fresh SECOND checker shards and assembly |

### Evidence transport, review intake and guarded refresh — 8

| Workflow | Evidence or operation |
|---|---|
| [rhrc_post292_independent_review_intake.yml](../.github/workflows/rhrc_post292_independent_review_intake.yml) | Independent 44-field review artifact intake |
| [rhrc_post292_offline_bootstrap.yml](../.github/workflows/rhrc_post292_offline_bootstrap.yml) | Pinned offline compiler artifact transport |
| [rhrc_post292_one_shot_rhkg_refresh.yml](../.github/workflows/rhrc_post292_one_shot_rhkg_refresh.yml) | Guarded one-shot generated-state refresh |
| [rhrc_post292_release_candidate.yml](../.github/workflows/rhrc_post292_release_candidate.yml) | Manual complete-output release-candidate assembly |
| [rhrc_post292_source_snapshot.yml](../.github/workflows/rhrc_post292_source_snapshot.yml) | Source export for offline investigation |
| [rhrc_post292_workflow_harvest_intake.yml](../.github/workflows/rhrc_post292_workflow_harvest_intake.yml) | Prerequisite scientific workflow-harvest intake |
| [rhrc_post299_rhkg_refresh.yml](../.github/workflows/rhrc_post299_rhkg_refresh.yml) | PR300 guarded RHKG refresh |
| [rhrc_post300_k5_rhkg_refresh.yml](../.github/workflows/rhrc_post300_k5_rhkg_refresh.yml) | PR301 guarded K5 RHKG refresh |

### Later candidates and portability — 3

| Workflow | Evidence or operation |
|---|---|
| [rhrc_post299_parity_candidate.yml](../.github/workflows/rhrc_post299_parity_candidate.yml) | Parity candidate compiler evidence; not full release acceptance |
| [rhrc_post300_k5_research.yml](../.github/workflows/rhrc_post300_k5_research.yml) | K5 exact geometry and finite-source candidate research |
| [rhrc_post300_runtime_portability_candidate.yml](../.github/workflows/rhrc_post300_runtime_portability_candidate.yml) | Candidate runtime/portability, replay, parity, producer/independent and support-gate evidence; read each disposition |

## Historical Stage 19 evidence retrieval

Four links in the preserved Stage 19
[Python validation note](../research/RHRC/integration/opica_followup/continuation/2026-10-22/evidence/current-codex/stage19/python/VALIDATION.md)
and [workflow harvest](../research/RHRC/integration/opica_followup/continuation/2026-10-22/evidence/current-codex/stage19/workflow/HARVEST.md)
name loose files that are not tracked at those locations. All four are available
inside the committed archives below. This retrieval note leaves the historical
reports and archive bytes unchanged.

| Archive | Internal member | Member SHA-256 |
|---|---|---|
| [Python validation ZIP](../research/RHRC/integration/opica_followup/continuation/2026-10-22/evidence/current-codex/stage19/python/PRELIMINARY_PYTHON_VALIDATION.zip) | `controlled-temp/commands.json` | `2b6ad70a53279a40fbc0b60cebe4e7add7b576fbedc6e36a0aae7f665e256f6a` |
| Same Python validation ZIP | `linux-parent/summary.json` | `24e2ccc2f2f5ea8f6fcbb5da966ad397f71afbd91142394cfed3c737fe8d687c` |
| Same Python validation ZIP | `frozen-controls/summary.json` | `555f132a83fdb55da3f7412b55ae95b4a5765925b899935e2688a5e71565b4af` |
| [Baseline workflow ZIP](../research/RHRC/integration/opica_followup/continuation/2026-10-22/evidence/current-codex/stage19/workflow/BASELINE_WORKFLOW_AUDIT_2026-10-24.zip) | `native-panel-differences.json` | `6072042488e8de3eb66f50d093addb1f28b2c02f22367ed999842cddf6c5fe83` |

At snapshot `7597acd`, the Python ZIP itself has SHA-256
`5bccfb27b403bf9d03f84ec3981c793dd427f07ac39f39dd7a5df47dc69b5bc5`;
the baseline workflow ZIP has SHA-256
`57e9d5a96d1a0f5cadbe4ac42016d932ba1b9554078afbd64244285cf4b083f3`.
Read a member without extracting into the source tree:

```sh
python -B - <<'PY'
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile

stage19 = Path("research/RHRC/integration/opica_followup/continuation/2026-10-22/evidence/current-codex/stage19")
with ZipFile(stage19 / "python/PRELIMINARY_PYTHON_VALIDATION.zip") as archive:
    member = "controlled-temp/commands.json"
    data = archive.read(member)
    print(member, sha256(data).hexdigest())
    print(data.decode("utf-8"))
PY
```

Select another listed archive/member to inspect it. These are historical
validation and harvest records, including their recorded failures and incomplete
gates. Recovering or hashing the archived bytes is not a new replay or compiler
receipt.

## Troubleshooting by failure scope

| Observation | Next useful check |
|---|---|
| `lean` or `lake` is missing | Install/select the pinned host toolchain; keep the Python-only examples separate |
| A tracked JSON or PDF is absent locally | Check the Git tree and sparse-checkout rules before treating it as a repository omission |
| A named import is missing | Build that named module with the pinned dependencies; the default root may not import it |
| Source policy rejects a path | Compare the exact successor delta and source identity; do not loosen the historical allowlist |
| A generated product is stale | Read the producer failure and run the ordered materializer in a reviewed environment |
| A native lane times out or is killed | Preserve resource evidence; this is not a theorem rejection or an unprovability result |
| A wrapper succeeds but a consumer/export is absent | The required gate is incomplete; inspect the per-job raw evidence |
| An old green result exists for a different commit or attempt | Treat it as historical evidence and reproduce the required current scope |

## Citation

Use [CITATION.cff](../CITATION.cff) for repository metadata. Identify **Marcus
Hermansson** as author of this fork's research and manuscripts, while preserving
the inherited authorship and notices in [UPSTREAM_README.md](../UPSTREAM_README.md)
and [LICENSE](../LICENSE). A repository-wide citation does not replace credit
to Mathlib, the inherited Anthropic work or a cited external source.

For a theorem, give the repository, exact commit, source path, fully qualified
declaration and the hypotheses relevant to your application. For example:

> Marcus Hermansson, *zeta-23-lean*, source snapshot
> `7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9`,
> `Zeta23/OPICARound4/ArithmeticFrontier/FiniteCertificateSoundness.lean`,
> `Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor`.
> Applied with exact real entries, a positive shift and the strict squared
> Frobenius-residual bound.

For a paper, copy its exact title, paper number, revision and date from
[the archive catalogue](../papers/README.md), and give the archived filename or
Git blob SHA-1 from [the manifest](../papers/MANIFEST_2026-11-21.json). Add the source
snapshot and theorem names when you rely on formalized ingredients. State
separately whether you performed a fresh compiler check, replayed a finite
calculation or only read the cited source. Do not invent a DOI or describe
manuscript consequences as independently compiled declarations.
