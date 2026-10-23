# Riemann project: OPICA continuation

Read `research/RHRC/integration/opica_followup/README.md` and then
`research/RHRC/integration/opica_followup/continuation/2026-10-22/README.md`.
Use the current checkout and that continuation's ledger; reconcile newer work
before applying any historical overlay or patch.

For a repository-wide entry point, read root README.md and the continuation's
DOCUMENTATION_INDEX.md and MODULE_STATUS.md. The manual OPICA progress map is
`research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md`; its arrows organize work,
not compiler uses or mathematical implications. Older renderer-owned Control-v2
blocks retain their historical anchor and do not route the active PR #294.

The original follow-up requires **100 primary roots in 28 acceptance units**.
The historical exact-source subset contains 41 roots. New local candidate gates
remain separate from aggregate registration and full release acceptance.
Thirty additional roots passed narrow gates and 29 original roots still lack
complete implementations. Read the continuation STAGE10_HANDOVER.md (and the
earlier stage handovers) for exact proof and infrastructure evidence. Read each
ledger gate rather than adding root names or supporting lemmas to a completion count.

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
- Use the continuation runner for the nine repaired modules and independent
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
