# Documentation and evidence index

Use this index with [root AGENTS.md](../../../../../../AGENTS.md) and the
[continuation guide](README.md). It describes the 22 October OPICA source
checkpoint and its staged repairs; read [STAGE4_HANDOVER.md](STAGE4_HANDOVER.md)
for the latest exact sources and gates. Check the live Git head and workflow
results before editing.

## Reading order

1. Read the [current guide](README.md), [100-root ledger](ROOT_LEDGER_100.json)
   and [module status table](MODULE_STATUS.md). Separate source presence, local
   proof, consumer/axiom gates and current aggregate acceptance.
2. Read the relevant original contracts in [BUILD_SPEC.md](../../BUILD_SPEC.md),
   [PUBLIC_ROOTS.json](../../PUBLIC_ROOTS.json),
   [BUILD_MANIFEST.json](../../BUILD_MANIFEST.json),
   [PAPER_CROSSWALK.json](../../PAPER_CROSSWALK.json) and
   [PARENT_EXTENSION.json](../../PARENT_EXTENSION.json).
3. Read the matching theoretical inputs: [Round 2 PDF](inputs/OPICA_Beyond_PR_Paper_Round2_2026-10-21.pdf),
   [final audited PDF](inputs/OPICA_Followup_Final_Audited_Paper_2026-10-21.pdf)
   and [Post-Green Amendment v1.1](inputs/OPICA_Followup_PostGreen_Amendment_v1_1_2026-10-21.md).
   The amendment supplies supporting research, not extra mandatory roots.
4. Inspect the actual [Lean sources](../../../../../../Zeta23/OPICAFollowup),
   [independent consumers](consumers), [current proof review](evidence/current-codex/lean-review/REVIEW.md)
   and [source/import provenance](provenance/MODULE_IMPORT_REFINEMENTS.json).
5. Choose work from [REMAINING_WORK.md](REMAINING_WORK.md),
   [NEXT_AGENT_PROMPT.md](NEXT_AGENT_PROMPT.md) and the
   [progress map](../../../../graph/OPICA_FOLLOWUP_CURRENT_STATE.md).

## Which surface answers which question

| Surface | Role and limits |
| --- | --- |
| Live GitHub head / exact compiler and CI evidence | Determines which exact source was tested and the actual job disposition. Pending, skipped and failed gates remain visible. |
| Original Markdown/JSON specifications | Define all 100 primary contracts and 28 acceptance units. Historical PLANNED fields are preserved input metadata, not current proof receipts. |
| ROOT_LEDGER_100.json | Current per-root implementation and evidence stages. Every embedded contract equals its original PUBLIC_ROOTS object. All current aggregate/full-release gates remain OPEN. |
| MODULE_STATUS.md | Deterministic navigation table derived from the ledger and file presence. Counts and source links confer no proof authority. |
| README / next-agent task / remaining work | Current operational instructions and named unfinished obligations. Read actual definitions and full contracts before proving anything. |
| Manual OPICA map | Shows work lanes and evidence locations. Its arrows are navigation, not compiler dependencies or mathematical implications. |
| Generated RHKG and integration views | Governed producer outputs with their own exact source/compiler anchors. Follow the producer chain before claiming current freshness. |
| SOURCE_REGISTER / WORKFLOW_CONTRACT | Implementation refinements and draft/planned gate metadata. Their historical fingerprints and planned job lists are not fresh receipts. |
| Control-v2 renderer blocks | Preserved historical/control snapshot. Their PR #287 and candidate NONE labels do not route current PR #294 work. |
| provided/ and evidence/provided/ | Immutable supplied delivery and its original gate history. Current copied guides supersede its stale auxiliary-consumer status and offline setup assumptions. |
| evidence/historical-codex-review/ | Earlier-source diagnostics. A failure at an old source hash is not a failure of the repaired source. |
| evidence/current-codex/ | Independent replay, structural review and workflow observations with explicit source and environmental limits. |

## Evidence locations and open gates

- [Accepted parent intake](../../PARENT_INTAKE.json): merged PR #293 commit/tree,
  tested-tree relationship, parent scope and complete recorded workflow harvest.
- [Historical cold receipt](evidence/provided/cold41/subset/compiler-receipt.json.gz):
  exactly the original 41-root subset. It binds the earlier `9b6a9a3` source;
  it cannot accept the whole continuation.
- [Original six-root narrow receipt](evidence/current-codex/lean-review/STATUS.json):
  hashes, module saves, independent consumers and standard-only printed axioms.
  It supplies no all-100 public/type/constructor/private-DAG export.
- [Earlier documentation/gate review](evidence/current-codex/documentation-review):
  the earlier bounded CI snapshot, navigation checks and documentation-path
  mutation/regression tests. Static tests do not add mathematical roots.
- [Earlier child and parent review](evidence/current-codex/contracts/PYTHON_ADOPTION_REVIEW.md):
  structural fixes and environmental failures. The full parent local attempt
  retained two blocked tests; supplied successful Linux evidence is separate.
- [Post-Green research](POST_GREEN_RESEARCH.md): all nine required mathematical
  review conclusions. Repeat the pass when meaningful proof evidence changes.

[Stage 4](STAGE4_HANDOVER.md) restores compiling W06/W07 sources, completes the CT1
dilation family and the word/jet consumer, and records the CI cancellation gap; its
[evidence](evidence/current-codex/stage4/STATUS.json) binds every log and source.
[Stage 2](STAGE2_HANDOVER.md) adds five narrow primary results and exact proof-lane
handovers. [Stage 1](STAGE1_HANDOVER.md) adds four earlier narrow results and tested
full100 receipt infrastructure. Its [evidence](evidence/current-codex/stage1)
includes exact proof receipts, independent review, 185 tests per Python mode and
a bounded all-job scientific harvest. The independent full review seal, actual
full compiler production/replay, all missing implementations/consumers, release
companions, complete facade/registration, canonical regeneration and final
workflow harvest remain required. Full-release readiness
and parent extension correctly reject the incomplete package.

## Maintaining these documents

Update the ledger only when exact evidence justifies a stage change. Run
`refresh_navigation.py --write` here to regenerate MODULE_STATUS.md, and
`--check` to verify it. Keep frozen specifications and supplied historical
documents unchanged. The
[documentation navigation amendment](provenance/DOC_NAVIGATION_AMENDMENT.json)
lists the seven additional documentation-only paths individually. It grants no
source, registry, compiler or theorem exception.

After reviewing artifact/document changes, run `refresh_manifest.py` here to
refresh the exact artifact inventory and preparation-validator pin. Run the
preparation gate and relevant regression checks in both Python modes. The
renderer check must still pass with every generated control block unchanged.
Use the existing graph materialization pipeline for future canonical graph
regeneration; do not hand-edit generated graph products to promote local results.

**RH, Step 4 and the independent closing inequalities remain OPEN.**
