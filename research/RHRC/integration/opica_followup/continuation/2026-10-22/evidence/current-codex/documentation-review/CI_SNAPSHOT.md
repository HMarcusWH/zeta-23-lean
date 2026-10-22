# Bounded CI review — proof-source checkpoint a77ae604

Metadata was observed from 13:43:50 through 13:47:25 UTC on 22 October 2026.
This is a dated, non-atomic observation, not the live branch state or a final
all-workflow acceptance. See [PR294_CI_SNAPSHOT.json](PR294_CI_SNAPSHOT.json)
for all enumerated runs, jobs, classifications and evidence limits.

| Source | Exact identity |
| --- | --- |
| PR #294 head | `a77ae60427423e8b6f098596f300c8cecc6392b6` |
| Head tree | `b1ebc2edbe0c07a486fcb5cae8df742c9e4745ed` |
| Synthetic PR merge | `2735cbb15830808c5e6294c428f857d31ff09219` |
| Synthetic merge tree | Same tree as the exact head |
| Accepted parent | `d53dd70d38b0762af130b1d19b795af259f505f5` |

## What actually finished

All 22 head runs (21 pull-request, one push) and 55 then-instantiated jobs were
enumerated. Ten jobs succeeded, two failed, one skipped, 15 were running and 27
queued. Dependent jobs may materialize later. Twelve completed non-skipped job
logs were inspected; all seven then-available result artifacts were downloaded
and their provider digests and ZIP CRCs verified. Pending jobs are not passed.

| Gate or check | Actual disposition and scope |
| --- | --- |
| Push preparation | `PASS_PREPARATION_ONLY`; no theorem or release authority. |
| Push full-release readiness | `FAIL_RELEASE_INCOMPLETE`; all-100 scope and receipt gates remain closed. |
| Main `python-rhrc` check | Failed at the parent-extension validator: full child reviewed type table absent; subset cannot extend parent. This is an integration rejection, not a Lean theorem counterexample. |
| Parent OPICA regression | Passed 5,112 exact checks and 187 tests per Python mode at the synthetic merge with the same tree. This preserves parent checks; it does not accept child roots. |
| Permansson existing Theorem 31 build | Successful in its existing scope; no new OPICA proof authority. |
| Current subset exporter and narrow repaired-candidate compiler jobs | Queued at the observation cutoff; no fresh current-head compiler receipt was available. |
| `post287-full-k3` | Explicitly skipped; no successful continuous-K3 result is inferred. |

## Scientific results retained by successful jobs

- Post-190 layers 3, 4 and 5 remain `UNRESOLVED`.
- Post-192 remains `TRAJECTORY_RIGIDITY_UNRESOLVED`: 96 evaluated controls,
  97 leaves, 33 `J_UNRESOLVED` and 63 `H1_UNRESOLVED`.
- WP6 remains `EXPERIMENTAL_SIGNAL`; WP5 retains its finite/model interval
  evidence scope. Neither produces a native global exclusion or RH theorem.

The machine snapshot, [parsed artifact reports](completed-artifact-reports.json),
[log research results](completed-log-research-results.json) and
[artifact verification](downloaded-artifact-verification.json) preserve the
actual observations. The sibling raw job logs allow independent inspection.

## Continue the harvest

Read current GitHub results at the actual new head after every push. Enumerate
every workflow and job, record pending/skipped/failed results, compare scientific
dispositions with prior runs and inspect new compiler receipts before changing
any root's stage. Documentation commits do not inherit CI acceptance merely
because their Lean sources are unchanged.

**RH, Step 4 and the independent closing inequalities remain OPEN.**
