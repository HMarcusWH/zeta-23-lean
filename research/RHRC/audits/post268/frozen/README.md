# RH post-#268 audit bundle

Read `AUDIT_REPORT.md` first, then `PROOF_NOTES.md` for the mathematical arguments.

This bundle contains an audit, not an RH proof. Existing theorem authority comes from the inspected repository/CI. The new simplicity argument and exact source-weight counterexample are DERIVED, not newly Lean-compiled. The proposed cofinal arithmetic lower bound remains OPEN.

## Frozen source

Commit: `ab545e71bfb1b11c647597bee014fad6d9ac291a`  
Tree: `0fdd3151c86989f7cf7123be322b3968e89e3263`  
Archive SHA-256: `b8cc6843ccb7788afa5e787f367df4aa96f404319234268d543b8be324ac9a54`

The source repository itself is not duplicated in the bundle. Use the user's supplied ZIP or a checkout of the exact commit. `results/file_manifest.jsonl` records every original source file hash; `results/final_integrity.json` confirms that all 1,207 stayed unchanged during the audit.

## Contents

`results/test_results.json` and `extra_test_results.json`: actual local command logs, return codes, timings and dispositions. There were 21/21 passing primary commands, including 306 distinct unit tests. The expanded batch had 12 passes, 30 missing-flint blocks, one path-portability failure and one timeout.

`results/independent_graph_audit.json`: independent graph integrity and SCC analysis. `candidate_resolution_holes.json` and `graph_semantic_scope.json` identify unresolved export identities and explicitly deferred semantic coverage.

`results/workflow_harvest.json`: extracted observations from live GitHub, including all 15 jobs/12 workflow runs, exact source identity, frozen dispositions and limitations. It is not a copy of the complete remote logs and does not assert a byte-for-byte replay of every historical artifact.

`results/source_weight_counterexample_exact.json`: symbolic/rational negative-weight certificate. `mathematical_falsifiers.json` holds generic inference counterexamples. `ground_weight_scout.json` is floating-point discovery only, not interval certification.

`results/source_anchor_index.json`: source symbols, pinned paths, line ranges, blob hashes and excerpts. `environment.json` records available packages and the unavailable local Lean/Arb toolchain.

`logs/`: complete local stdout/stderr for the executed commands, including failures. `scripts/`: the original scripts used plus the portable command-replay helper.

## Replay on another machine

Obtain the exact repository commit and the repository's required dependencies. No credentials or automatic dependency installation are included. The portable helper only writes new logs to the requested output directory:

```bash
python scripts/replay_checks.py --repo /path/to/zeta-23-lean --output /tmp/rh-primary-replay
python scripts/replay_checks.py --repo /path/to/zeta-23-lean --output /tmp/rh-expanded-replay --batch expanded
```

The helper is a portability wrapper added after the frozen tests; its syntax was checked, but it is not itself evidence that the expensive expanded batch passed. The original audit scripts preserve the exact `/mnt/data/rh_audit` layout used in this run. The exact counterexample checker requires SymPy and writes to that recorded layout. Its calculation is also fully specified in `PROOF_NOTES.md`, independent of any private service.

For a local Lean rebuild, follow the repository's pinned toolchain and workflow targets. This audit did **not** perform a new local Lean build. Do not describe the portable Python replay as a formal Lean audit.

The source ZIP has no historical Git database. The original audit created an index for tree reconstruction, not a fake historical commit. Running history-dependent operations on such an index does not recreate all prior PRs.

## Integrity and status

`BUNDLE_SHA256SUMS.txt` hashes every bundled file except itself. No private model scratchpad or raw personal-chat export is included. No remote repository changes were made.
