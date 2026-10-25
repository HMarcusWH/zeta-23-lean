# Stage19 independent Python validation — 2026-10-24

The child suite passes **185/185 tests in normal and optimized modes** on Python 3.13.5. The focused parent contract suite passes **82/82 tests with no skips in both modes** on Ubuntu/WSL Python 3.14.4 using genuine Linux /tmp fixtures. No repository source was edited by these validation runs.

Frozen replay passes 5112/18862/14672/1274 exact controls per mode. Co-Poisson, round2 and final numerical checks remain CONSISTENCY_ONLY and are not interval-certified. The replay itself marks the full release runtime unaccepted because the platform-independent artifact hash lock and acceptance run are still required.

The tests ran while the Stage19 working tree was dirty, over branch head `cea7b2f62ea847c18958cc7385151c8c2b09520d`, tree `377c7f6f36375a4ac35d3f3ad17ee95b340eb9eb`. They are not a clean commit receipt. The three Python source hashes recorded for the Linux parent run are unchanged between start and finish. Exact commands, exit codes, times, source state and log hashes are in [VALIDATION_SUMMARY.json](VALIDATION_SUMMARY.json), [controlled-temp/commands.json](controlled-temp/commands.json), [linux-parent/summary.json](linux-parent/summary.json) and [frozen-controls/summary.json](frozen-controls/summary.json).

The initial sandbox Temp ACL errors and the subsequent native Windows symlink-privilege errors are retained in their original logs. They were resolved for validation by using a writable fixture directory for child tests and true Linux /tmp for the unmodified parent tests. No test was skipped or weakened to obtain the final Linux result.

Linux parent normal log SHA256: `fb4086d483dda4bc039e05575c1c888ea04bf6dbeb5860e74713e604332ed810`. Optimized: `11ea05e4212b080b495426f5889e4988298d7a0951dc73b442a34f929a076802`.

**These are infrastructure/regression results. RH, Step4, aggregate acceptance and full release remain OPEN.**
