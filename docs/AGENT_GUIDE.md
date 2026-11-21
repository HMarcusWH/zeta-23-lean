# Contributor and AI-agent guide

Read [AGENTS.md](../AGENTS.md) first. This guide explains the repository workflow;
it does not override the parent project instructions or source-preservation rules.
Start from the [21 November frozen snapshot](CURRENT_STATE.md),
[repository map](REPOSITORY_MAP.md) and [reproducibility guide](REPRODUCIBILITY.md),
then read the relevant package's exact contract, source and receipt. Historical
PRs describe their own checkpoints. A documentation branch does not resume the
mathematical research programme or promote an open claim.

## Establish the object before changing it

1. Record checkout, branch, commit, tree and working-tree changes. An old ZIP,
   screenshot or handover is reference material until reconciled with live source.
2. Read definitions and full theorem statements, including dependent hypotheses,
   domains, quantifier order, carrier metrics and imports. Inspect axioms and the
   exact independent expected-type consumer.
3. Identify the governed source scope. The
   [documentation successor](../research/RHRC/integration/documentation_2026_11_21/README.md)
   authenticates the unchanged Round 6 policy, the exact paper-archive delta, and
   the named documentation operations. Its policy binds exact blob IDs and the
   validator template; it cannot authorize arbitrary edits to itself. Historical
   Round 4 and Round 6 policies remain unchanged. Renderer blocks and the AGENTS
   instruction tail are preserved byte-for-byte.
4. Check live jobs and reviews for the exact run head, including failed steps
   inside workflows still running. Page all jobs and attempts. Do not substitute
   a mutable nested pull-request head for an Actions run's recorded `head_sha`.

## Preserve the research boundary

Project-mirror `sources/` files are read-only references. Preserve protected
parent mathematics, registries, configurations, foundational PDFs and compiler
pins. Do not apply historical overlays wholesale. Never add project axioms,
placeholders or a packet hypothesis that silently assumes the desired result.

Keep the complete physical source and metric. Preserve mixed arithmetic terms,
prime-power seams, complements and normalization costs. A fitted matrix,
truncated expression or synthetic analogue can falsify a proposed general law;
it cannot replace the actual zeta construction in a positive theorem claim.

Use **PROVED**, **DERIVED**, **EXPERIMENTAL SIGNAL**, **LEAD / HYPOTHESIS** and
**OPEN** as defined in the [README](../README.md). A conditional implication is
proved with its hypotheses; an OPEN hypothesis is not established by compiling
its definition. RH and Step 4 remain OPEN unless their exact complete statements
pass the full mathematical and claim-validation gates.

## Build and test the relevant scope

The [Lean pin](../lean-toolchain) and [Mathlib manifest](../lake-manifest.json)
are authoritative. Do not run `lake update`, reset shared caches or change pins
to make a proof pass. Windows and Linux compiled Lean objects are incompatible.
Assign a single owner to broad cache-writing builds; independent narrow checks
need controlled outputs and genuine dependencies.

Read the workflow and declared test inventory before choosing a command. From
the repository root, the runtime's documented interface starts with:

```text
python -B -m research.RHRC.integration.opica_composition.cli --help
python -B -m research.RHRC.integration.documentation_2026_11_21.source_scope --check
python -B -m research.RHRC.integration.documentation_2026_11_21.check_documentation
python -B research/RHRC/control_v2/render_current_state.py --check
python -B -m unittest research.RHRC.integration.documentation_2026_11_21.test_source_scope
python -O -B -m unittest research.RHRC.integration.documentation_2026_11_21.test_source_scope
```

The renderer check protects the preserved historical block; it does not update
current routing. The successor requires a clean, committed source checkout.
`--check-tree` is a separately labelled sparse-clone Git-object inspection; it
does not qualify the production working tree. The policy tests check rejection
of undeclared changes, not Lean proofs. The [examples](EXAMPLES.md) have smaller
bounded recipes. Production lane commands and their environment requirements are in
[rhrc_opica_composition.yml](../.github/workflows/rhrc_opica_composition.yml),
the [runtime guide](../research/RHRC/integration/opica_composition/README.md)
and [test inventory](../research/RHRC/integration/opica_composition/EXPECTED_TESTS.json).

Use relevant checks for the change, then required acceptance gates. A narrow
module check does not replace the original follow-up's full-release gate.
Do not weaken an old test or relabel a failure to publish an incomplete slice.
Historical suites keep their frozen source selectors; current compatibility
checks the child independently. Native production tests fail when setup is
missing rather than silently skipping.

## Evidence and generated state

Store run evidence outside the governed Git source tree. Record commands, exit
codes, source hashes, compiler/package identity, full expected types, assumptions,
transitive axioms and raw logs. A successful wrapper with a failed consumer is
a failed gate. A historical receipt applies only to its exact source object.

The canonical [materializer](../research/RHRC/tools/materialize_derived_state.py)
orders the graph/framework producers transactionally. Update the explicit
reviewed source manifest and file classifications, include authored files in
the tracked census, regenerate through the canonical producers and run their
validators. Do not edit generated outputs or broaden a path whitelist by prefix.
Keep authored navigation separate from generated semantic products. Documentation
changes can affect the tracked-file census and document semantic products even
when no Lean source changes. A passing documentation/source-scope check does not
replace the independent canonical `--check` gate. The 77 active generated paths
and four frozen historical products retain their existing boundary.

Local Windows execution is development evidence. Round 4 Linux production
qualification additionally requires read-only project/package/toolchain mounts,
isolated processes/network, hard resource limits, exact environment identity
and independent bundle reconstruction. Historical-native canonical replay checks
rendering/structure; it cannot stand in for fresh kernel execution.

The eleven-lane aggregate requires every declared bundle from the same source
and run. Optional diagnostic uploads can explain a failed bootstrap; they are
not acceptance artifacts. Check every workflow, not only this aggregate, for
its scientific result and scope.

## Review and handover

Prepare focused fixes, run relevant checks and push without waiting for unrelated
long jobs when the user has authorized pushing. Keep pending statuses explicit.
Never merge without the maintainer's instruction. Leave a handover with exact
head, changed statements, local/production evidence, open obligations and where
to inspect results.

After meaningful green results, read the actual proof and harvest all workflow
dispositions. Compare history, trace assumptions upstream and consequences
downstream, revisit failed routes and test combinations. Falsify proposed clues
at degenerate cases, seams, normalization changes and countermodels before
building around them. The full persistent Post-Green instructions remain in
[AGENTS.md](../AGENTS.md); green begins the next mathematical investigation.
