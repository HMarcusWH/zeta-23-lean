# Second delivery: contract and receipt review

Review complete with material gaps. The current41-root checkout remains fail closed. Full100 acceptance, RH, Step4 and independent closing remain OPEN. No main-repository source, frozen input, Lean declaration or commit was changed by this review.

## Exact object and scope

Main checkout: `9b6a9a3a2badb4cff62a56c1158d9cef8759d30d`, clean. The isolated fixture starts at that exact head. Its2437 tracked files were checked from immutable Git blob bytes; the only final byte differences are the three uploaded Python candidates. `CONTRACT_REVIEW.json` records their SHA256 values. The first native checkout inherited CRLF conversion; its failed logs remain under `INITIAL_CRLF_FIXTURE`. Final evidence uses exact Git bytes, rather than rewriting frozen hashes to fit converted files.

Python3.13.5, writable task-local TEMP/TMP, normal and `-O` modes. No Lean build was run. This review covers the parent `test_contract.py` module and child `test_parent_extension.py` module, not all child or repository test modules.

## Test results

| Independently identified suite | Normal | Optimized |
|---|---|---|
| parent-full-56 | FAILED (errors=2) | FAILED (errors=2) |
| parent-supported-55 | FAILED (errors=1) | FAILED (errors=1) |
| parent-selected-30 | FAILED (errors=1) | FAILED (errors=1) |
| parent-projection-21 | FAILED (errors=1) | FAILED (errors=1) |
| child-full-26 | OK | OK |
| parent-supported-54 | OK | OK |
| parent-selected-supported-29 | OK | OK |
| parent-projection-supported-20 | OK | OK |

The full56 parent attempt is **not green**. One test cannot create a real symlink because Windows denies that privilege; another cannot finish its historical Git diff because the local object caches lack blob `bfc2944e2a864325f9d10903f23d73f49148542f`. The supported54 suite explicitly excludes these two environment-blocked cases. It passes in both modes. All26 child extension tests pass in both modes. The selected29 and projection20 suites overlap those54; they add no new test-count authority.

The uploaded logs report30 parent and26 child tests per mode, but include no command, test identities, source hashes or head. Their reported counts are preserved and hashed. The uploaded parent file actually contains56 tests, including21 new projection tests. The independent selected30 comparison is documented explicitly; the original selection cannot be reconstructed from dots alone. The native projection21 attempt has20 passing checks plus the privilege-blocked symlink check.

## Material findings

1. **Cold-export repair is incomplete.** The builder adds `Zeta23.RHRC.OpicaTypeExprExport`, but the exporter also directly imports `Zeta23.RHRC.SourceCandidateResolution`, outside both explicit build-target closures. The root review's `../INDEPENDENT_CHECKS.json` records the closure. This lane verified the direct import and one-target builder diff; it did not claim a clean Linux pass.
2. **Child route fields evade the existing route-less registration rule.** The independent synthetic probe sets both claim and binding route to `R001_exceptional_zero`; `_reviewed_child_objects` accepts it. Parent `registration_errors` checks the parent projection, after the child rows have been removed.
3. **Child statement and dependency checks are missing on that path.** The same helper accepts an empty statement and unknown/self/duplicate dependency IDs. Three concrete probes are persisted in `INDEPENDENT_PROBES.json`. These are latent structural gaps, despite the other mutation tests passing.
4. **A complete child compiler linkage remains an integration obligation.** The wrapper consumes100 source/type review rows and type digests, but neither is itself compiler evidence. The helper correctly documents that a complete child compiler gate is separately required. The parent release receipt validates the parent roots; it does not become a full100 child receipt. The current child release CLI deliberately returns `FAIL_RELEASE_INCOMPLETE`.

## Fail-closed behavior verified

The actual immutable parent capture passed verification against the accepted Git objects and fixed tree. A rewritten capture hash and a rewritten historical claim capture were rejected. The real current41-root wrapper rejects the absent full100 type table with `subset cannot extend parent`. Its fallback preserves the raw registry/configuration context, emits the error, and returns an empty allowed-delta set. The full parent static check remains environment-blocked by the historical Git object; it is not reported as passed.

## Post-Green Research Pass

**What became checked:** source-bound parent capture verification,54 runnable parent mutation tests and26 child extension tests survived both Python modes. These are infrastructure and regression results, with no new mathematical theorem authority.

**Workflow harvest:** the four supplied local test logs were inventoried and hashed. They are selected test evidence, not GitHub CI or full-release evidence. No current workflow state was inferred and no network harvest was attempted here. One historical Git object read triggered a failed automatic promisor-fetch attempt; subsequent probes disabled lazy fetching and used local read-only caches.

**What changed:** the proposed parent wrapper replaces unconditional child-path rejection with an exact structural projection only after full100 review metadata. It does not relax current41 into acceptance. The builder adds one missing codec prerequisite but leaves another direct import uncovered.

**Upstream implications:** reuse the parent's route, statement and dependency rules on the reviewed child objects before projection, while preserving immutable baseline and descriptor anchors. Add mutation tests that cross the projection boundary, rather than testing only its helper's happy path.

**Downstream implications:** a future full100 extension needs the complete child compiler/type/consumer/axiom/dependency receipt linked to exact reviewed source and checkout, in addition to the parent receipt and independent review. The selected41 receipt remains partial.

**Resurrected routes:** exact parent projection is a viable infrastructure route after these obligations and full100 coverage are met; it is not a current release unblocking result.

**New RH-relevant clues:** none. The accepted bad-metadata probes concern claim accounting, not mathematics.

**Falsification checks:** route labels, empty quantified statements and malformed dependency lists falsify the apparent completeness of the green structural mutation suites. Native symlink behavior and historical Git-dependent test execution remain unverified on this platform/cache.

**Highest-leverage next moves:** complete the cold exporter prerequisites; enforce and test all child claim firewall fields before projection; wire a genuine full100 child receipt into any eventual full-release path; rerun the real symlink test on a platform with support and the historical test with the immutable base objects available. Keep all100 obligations and the RH firewall closed meanwhile.

## Evidence

- `CONTRACT_REVIEW.json`: source hashes, complete matrix, scope and findings.
- `TEST_EXECUTIONS.json`, `SUPPORTED_TEST_EXECUTIONS.json`: exact commands, interpreter, environment, exit codes and log hashes.
- `INDEPENDENT_PROBES.json`: immutable source capture and three metadata probes, actual41 rejection/fallback.
- `ACTUAL_PARENT_CHECK.json`: explicit historical-cache environment block.
- `FIXTURE_BYTE_MATERIALIZATION.json`: exact Git-byte fixture reconstruction and candidate hashes.
