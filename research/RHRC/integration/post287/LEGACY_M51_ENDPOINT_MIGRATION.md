# Legacy M51 endpoint claim migration

Date: 2026-10-13. Terminal claim: **RH_OPEN**.

The legacy `post285_m51_k2_even_bottom_certificate.py` sets
`LOG16_UP = 2772588722239781/10^15` and clips the upper endpoint of every
covered cell to this rational. Despite its name and inline comment, that value
is strictly **below** `log 16`. Consequently the historical 1,310-interval,
128-bit receipt has finite domain `[1/400, U]`, with
`U = 2772588722239781/10^15`. Its original exact-log16 claim was overstated.

The ordering has an exact rational check: from
`log 16 = 8 sum_{k>=0} 1/((2k+1) 3^(2k+1))`, the sum for `0 <= k < 17` is
already greater than `U`, and every omitted term is positive. This check uses
no interval evaluator and makes no positivity claim about the uncovered gap.

`integration/post285/build_post285_ledgers.py` now generates the corrected
finite rational domain in `OPEN_OBLIGATIONS.json` and
`EXPERIMENT_DISPOSITIONS.json`, corrects the M51 cross-reference and Step 92 in
`STEP_STATUS_MATRIX.json`, and records `M51_K2_EXACT_LOG16_ENDPOINT` as OPEN on
`(U, log 16]`. The ledger checker requires the rational domain and this OPEN
obligation. A separate source-bound complete guarded certificate would be
needed to discharge the gap; no pending or invalidated receipt is promoted.

The historical `post285/FALSIFICATION_REPORT.md` and
`post285/POST_GREEN_RESEARCH.md` keep their original receipt paragraphs, counts,
controls and observations, with explicit corrective annotations. The legacy
1,310-row receipt is distinct from the invalidated unguarded post287 1,205-row
transcript. This migration creates no new numerical or theorem authority.

The initial migration changed only reporting files and their ledger validator;
its digest comparison confirmed all 28 manual-campaign numerical inputs were
unchanged at that stage. Regeneration, the post285 ledger check and whitespace
check passed. No numerical experiment was run.

A separately authorized second stage corrected the legacy producer's displayed
scope: its module documentation, erroneous endpoint comment and the `main`
output's `statement` string. This intentionally changes that file's whole-file
digest while preserving every evaluator/helper AST, numerical constant,
acceptance rule and schedule. The other 27 campaign inputs remain identical.
See [the source-equivalence receipt](LEGACY_M51_DISPLAY_SOURCE_EQUIVALENCE.md).
Archived 31512dbb receipts retain their exact original source identities;
their digests must not be relabelled as candidate-source receipts.
