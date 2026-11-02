# Riemann project: contributor and agent entry point

Read [README.md](README.md), [docs/CURRENT_STATE.md](docs/CURRENT_STATE.md),
[docs/AGENT_GUIDE.md](docs/AGENT_GUIDE.md) and the relevant package contract.
The live PR head and exact compiler/CI receipts determine validation scope.
RH, Step 4 and independent source restrictions remain OPEN.

The current closing-attempt work is [PR #299, Madness?](https://github.com/HMarcusWH/zeta-23-lean/pull/299)
on `research/madness`, descended from merged Round 4 PR #298. Read the
[2 November research handover](research/RHRC/integration/opica_round4/progress/2026-11-02/HANDOVER.md) and its portable evidence inventory before continuing.
Research is paused at the maintainer request after this publication; no automatic
continuation or theorem promotion is authorized by archived documents. The
[original Round 4 contract](research/RHRC/integration/opica_round4/INTEGRATION_HANDOVER.md)
and [closure obligations](research/RHRC/integration/opica_round4/CLOSURE_OBLIGATIONS.json)
retain their exact scopes. Use the current checkout and reconcile historical overlays.

The original native follow-up remains a separate 100-root / 28-unit scope.
Its [continuation guide](research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md)
and Stage 22 ledger distinguish 41 historical source-bound roots from 59 narrow
local gates; this is not full original-contract release acceptance.
Frozen renderer blocks and older checkpoint instructions retain their historical
scope. The preserved instructions below continue to govern source integrity,
build discipline and Post-Green research. The newer documentation migration is
an exact named set, not permission for arbitrary parent changes.

Keep the original Markdown/JSON contracts and both foundational PDFs unchanged.
Read their full statements and physical/domain requirements. Record necessary
implementation refinements explicitly; never silently narrow a required domain,
assume a desired conclusion in a packet, replace an actual construction with a
synthetic object, or introduce project axioms/placeholders. Preserve parent
mathematics, historical registries/configuration and all OPEN claims.

The Post-Green Amendment v1.1 is additional supporting research. Its four
proposals do not become mandatory roots without an explicit versioned promotion.
Preserve the C3 counterexample and the distinction between its unrestricted
false inequality and repaired supporting forms.

## Build discipline

- Keep Lean and Mathlib pinned by `lean-toolchain` and `lake-manifest.json`.
- Use a real compatible toolchain/cache; Linux objects cannot be reused by native
  Windows Lean. The source-only CORE delivery does not contain its advertised
  optional offline runtime or complete Git history.
- Do not run `lake update`, reset shared caches or change the pins to make a proof
  compile. An exported cache without package Git metadata needs explicit local
  package overrides, as described in the preserved delivery documentation.
- Assign a single owner to broad cache-writing builds. Independent narrow
  modules can use separate controlled output paths with real dependencies.
- Never count a stale inherited object as compilation of modified source.
- Use the continuation runner for all 28 continuation modules and independent
  consumers. It is a narrow gate, not a full-100 receipt.
- Record exact source hashes, compiler version, checkout/head/tree, command exit
  codes, logs, assumptions and transitive axioms. A successful process with a
  failed consumer or missing export is not a successful acceptance gate.
- Keep preparation, narrow/subset evidence and full-release readiness separate.
  Do not disable or relabel the full-release gate to publish an incomplete slice.

All continuation artifacts are individually listed and hash-bound in
`CONTINUATION_MANIFEST.json`. New work must update the explicit checkpoint
provenance/pin when changing those artifacts; this never grants proof authority
or permission to edit protected parent files.

The explicit DOC_NAV_2026_10_22_01 refinement covers seven named documentation
paths only. Verify their exact bytes through the manifest; it does not authorize
other parent changes. After changing ledger stages, run the continuation's
`refresh_navigation.py --write` and check its module table. Refresh the artifact
manifest after reviewed documentation changes and preserve renderer blocks.

## Green begins the next investigation

After every meaningful green result, inspect the actual proof and what it means.
Compiler and exact-source CI evidence determine formal validity. Harvest every
workflow/job and distinguish formal validity, regression, research output and
completeness. Read the actual scientific disposition, not merely a green wrapper.
Keep failed, blocked, pending, skipped and interrupted results explicit.

Compare with previous proofs, failed routes, handovers and open bottlenecks.
Trace assumptions upstream and consequences downstream; look for dependency
compression, compositions, equivalences, positivity/Gram structures, rigidity,
transform interpretations, limit arguments and restrictions on counterexamples.
Revisit old failures only when their failure reason has changed. Attack clues
with boundary cases, scaling, normalization, vacuity, circularity and analogous
systems where the desired conclusion fails.

Use PROVED, DERIVED, LEAD/HYPOTHESIS, EXPERIMENTAL SIGNAL and OPEN accurately.
End substantial green reviews with: what became formally true; workflow harvest;
what changed; upstream implications; downstream implications; resurrected routes;
new RH-relevant clues; falsification checks; highest-leverage next moves.

**RH, Step 4 and the independent closing inequalities remain OPEN.**
Supporting roots, infrastructure and numerical agreement do not close them.
