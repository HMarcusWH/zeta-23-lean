# Continue the OPICA draft directly in this repository

This checkpoint combines the existing PR #294 implementation, the supplied
22 October repair kit, and the Codex audit/provenance. It is **not a completed
100-root release**. RH, Step 4 and the independent closing inequalities are OPEN.

For a complete file/authority map, read [DOCUMENTATION_INDEX.md](DOCUMENTATION_INDEX.md).
Use [MODULE_STATUS.md](MODULE_STATUS.md) to choose a source module and the
[manual progress graph](../../../../graph/OPICA_FOLLOWUP_CURRENT_STATE.md) to
orient proof lanes. The [dated CI review](evidence/current-codex/documentation-review/CI_SNAPSHOT.md)
records actual results and pending work at the source checkpoint; refresh live
GitHub results before making current claims.

## Current source and evidence

The working source is `Zeta23/OPICAFollowup/` in this checkout. Do not restore
`provided/workspace` or reapply historical patches over it. The original base was
`9b6a9a3a2badb4cff62a56c1158d9cef8759d30d`; all 2,437 tracked files were compared
with the new kit before adopting its exact eleven source changes. Fourteen loose
uploads matched their kit members. No parent mathematical Lean file was changed.

The controlling obligations remain the unchanged `PUBLIC_ROOTS.json`,
`BUILD_SPEC.md`, `BUILD_MANIFEST.json`, `PAPER_CROSSWALK.json` and
`PARENT_EXTENSION.json` two directories above this file. `ROOT_LEDGER_100.json`
beside this guide separates each root's implementation, compilation, consumers,
axioms and aggregate acceptance. `REMAINING_WORK.md` lists the 48 absent proofs.

- 41 roots have a historical cold exact-source subset receipt at the old base.
- Six mask, complex-measure and auxiliary roots passed independent local
  module, full-type/domain consumer and standard-axiom checks. The auxiliary
  consumer rerun is now preserved. Aggregate acceptance remains pending.
- Five other supplied candidates remain failed, unchecked or dependency-blocked.
- 48 original primary implementations are still absent.

Consult `evidence/current-codex/` and the ledger for any newer replay evidence in
this checkpoint. Do not infer a current aggregate receipt from the old subset.

## Build and verify

Use a complete Git checkout with the exact pins in `lean-toolchain` and
`lake-manifest.json`. Obtain the compatible toolchain and Mathlib cache using
the repository's normal Lake/CI setup. The source-only CORE ZIP omitted its
optional Linux runtime, baseline Git pack and historical archive; the original
delivery's offline restoration commands cannot be run from this checkout alone.
Its documents remain under `provided/` as historical provenance.

From the repository root, with an output directory outside the checkout:

```sh
python -B research/RHRC/integration/opica_followup/validate_contract.py \
  --phase preflight --output /tmp/opica-preparation.json
python -B research/RHRC/integration/opica_followup/continuation/2026-10-22/run_candidate_checks.py \
  --lake lake --output-dir /tmp/opica-current-candidates
```

The second command builds the three repaired modules from current source, checks
the explicit independent consumers and their named standard-only axiom closures,
and records source/head/tree/log hashes. It neither registers roots nor accepts
the complete PR. Use an OS-appropriate external output path on Windows.

For the existing 41-root subset export, both audit prerequisites are now explicit:

```sh
lake build Zeta23.OPICAFollowup.Validation \
  Zeta23.RHRC.OpicaTypeExprExport Zeta23.RHRC.SourceCandidateResolution
```

The builder remains a partial receipt producer. Full release readiness must stay
closed until actual all-100 compiler linkage and every remaining gate exist.

## Next work

Read `NEXT_AGENT_PROMPT.md`, the exact ledger contracts and
`evidence/historical-codex-review/` before choosing a proof lane.

Repair the Laguerre, comb, first-cell sign/cost and Step 1–3 consumer candidates;
then complete the 48 absent roots without replacing them by supporting lemmas.
The auxiliary/top-moment/residual/memory/rate chain and the global complex
measure/co-Poisson/profile/sampling chain are distinct unfinished obligations.

Finish independent full types and physical/domain consumers, actual definitions,
the public facade, complete declaration/constructor/private-dependency export,
full child receipt linkage, compiler-derived mapped claim dependencies,
registration and canonical regeneration. Preserve all 100 original root IDs and
all 28 acceptance units. Record dependency/interface refinements explicitly.

The repaired parent wrapper rejects the three reported metadata bypasses before
projection. It still correctly rejects the current incomplete reviewed type table
and preserves the raw parent context. The supplied full-reader draft was not in
the delivery; no such implementation is claimed here.

## Evidence map

- `inputs/`: both foundational PDFs, original specifications, amendment and
  historical research/input texts. The original controlling files remain above.
- `consumers/`: independent expected-type/domain consumers for the three repaired
  modules. They are actual Lean sources used by the narrow replay.
- `provided/`: unchanged delivery state, documents, tools and old-base patch.
  Some tools require omitted offline-runtime material; read the CORE caveat.
- `evidence/provided/`: supplied receipts/logs and the historical cold receipt.
  Large text evidence is losslessly gzip-compressed; decompress externally.
- `evidence/historical-codex-review/`: earlier failed-source diagnostics and audit.
  Those describe earlier source hashes and are not the current repaired result.
- `evidence/current-codex/`: this checkpoint's independent source, Python, Lean
  and GitHub evidence review and explicit limitations.
- `provenance/IMPORTED_FILES.json`: original and stored hashes, including gzip
  mapping; no cache or compiled object is part of the source delivery.
- `CONTINUATION_MANIFEST.json` above: exact artifact inventory and source-scope
  preservation. Its preparation gate creates no theorem authority.
- `DOCUMENTATION_INDEX.md` and `MODULE_STATUS.md`: current navigation and the
  deterministic per-module projection of the full ledger. Regenerate the table
  with `refresh_navigation.py --write`; verify with `--check`.
- `provenance/DOC_NAVIGATION_AMENDMENT.json`: seven named documentation-only
  paths, pinned by the artifact manifest. Frozen control blocks, specifications,
  registered claims and canonical graph products retain their prior authority.

The completed local [Post-Green Research Pass](POST_GREEN_RESEARCH.md) records
all nine required conclusions and remaining mathematical obligations.

After meaningful green results, perform the Post-Green Research Pass described
in root `AGENTS.md`. After full CI, harvest every job and scientific artifact
before claiming the full review complete.
