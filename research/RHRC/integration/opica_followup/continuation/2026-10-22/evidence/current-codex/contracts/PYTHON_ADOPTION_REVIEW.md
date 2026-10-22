# Core-kit Python adoption review

Recommend adopting exactly the three reviewed Python changes as draft checkpoint integration work. They close the three previously reproduced metadata bypasses and add the missing direct exporter prerequisite. No full100 release authority is added. RH, Step4 and independent closing remain OPEN.

## Provenance and permitted adoption

Base: `9b6a9a3a2badb4cff62a56c1158d9cef8759d30d`. Archive SHA256: `9c076a533291adb814f776018126330b6b2125a852548622ce196c6a0afcf88d`. Sixteen selected files were individually checked against the archive manifest. The isolated fixture contains2437 exact base files with only these three byte-identical archive overlays:

| Repository path | SHA256 | Recommendation |
|---|---|---|
| research/RHRC/integration/opica/tests/test_contract.py | `4d7523ff61b728fb575a955ce8fd52cb2b038439a03927c4762e3ad923e3cebf` | Draft adoption |
| research/RHRC/integration/opica/validate_contract.py | `cb46e19672a54db2d133be5aa3e0619b4aa194ee42535d04d763687d8740412b` | Draft adoption |
| research/RHRC/integration/opica_followup/build_receipt.py | `2d531a4e5ce5ff3c34bea01a57632e8f71b268033a067b9c7a0c9928fa275c22` | Draft adoption |

The unchanged frozen specifications and parent mathematical sources were preserved. This lane made no main-repository edit, compiler invocation or network fetch. It did not apply the whole archive. The first fixture setup failed because Windows newline conversion corrupted the Git alternates file; those setup logs are preserved under `INITIAL_SETUP_FAILURE`. Final setup uses explicit LF bytes and a byte-checked fixture.

## Independent test results

Python3.13.5, writable task-local TEMP/TMP, `-B`, and `GIT_NO_LAZY_FETCH=1`; normal and optimized Python. Exact commands, exits and log hashes are in `TEST_EXECUTIONS.json`.

| Suite | Tests per mode | Normal | Optimized |
|---|---:|---|---|
| parent-full | 68 | FAILED (errors=2) | FAILED (errors=2) |
| parent-runnable | 66 | OK | OK |
| child-extension | 26 | OK | OK |
| child-all | 131 | OK | OK |

All131 child test identities are distinct. The26 extension tests are included within those131 and must not be added again to the unique count. The66 runnable parent tests exclude two explicit environment blocks: native Windows symlink privilege and a missing historical Git blob needed by the actual static-check test. Therefore the full68 attempt is not green, even though the other66 pass both modes. The archived packaging logs report68+26 successful tests on their supplied environment; this review preserves that evidence without claiming to reproduce its two unavailable operations.

## Repairs verified

The V2 review schema rejects stale V1 records. Before projection, the repaired helper rejects claim/binding route labels, empty or whitespace-only statements even with an honestly updated digest, changed text under an old digest, and missing/unknown/self/duplicate/malformed dependency IDs. Actual wrapper callers supply immutable parent claim IDs from the source-verified baseline. The independent probes repeat the three formerly accepted bad cases and now reject each; `INDEPENDENT_FIX_PROBES.json` retains exact errors.

The current41 type table remains insufficient: the real wrapper emits an explicit rejection, preserves the raw parent registry/configuration view and returns an empty allowed-delta set. Thus the new projection does not turn partial source evidence into100-root acceptance.

The child builder now explicitly builds `Validation`, `OpicaTypeExprExport`, and `SourceCandidateResolution`, covering all three direct project imports of `OpicaFollowupBindings`. This lane checks that interface statically and runs the child Python tests. It does not claim a fresh cold Lean/CI run. The builder still requires exactly41 roots and produces `PASS_SOURCE_BOUND_SUBSET_ONLY`.

## Full receipt code and publication boundary

No active full100 receipt-reader Python file is delivered in this archive. `STATE.json` explicitly says the interrupted draft was not preserved. There is therefore no such implementation to adopt or validate. Keep this obligation OPEN and keep the existing full-release gate closed. Do not invent a successful reader receipt from the structural metadata tests.

The repair validates dependency identities, not their equality to the eventual complete child compiler-use graph. Statement hashes bind text to a review record, not mathematical equivalence to its frozen theorem contract. Both obligations still require the actual source-bound all100 receipt and independent semantic review. Registration/canonical regeneration and full CI acceptance remain unfinished.

The CORE archive contains no `baseline/source/` or `runtime/` payload members despite instructions describing the full kit. Treat those as separately required external payloads, rather than claiming this ZIP alone restores its runtime or Git history.

## Post-Green Research Pass

**What became checked:** the repaired structural firewall passes66 runnable parent tests and131 distinct child tests in both Python modes, including the12 added parent mutations. These are infrastructure/regression results; no new mathematical theorem became accepted.

**Workflow harvest:** the supplied packaging test logs were preserved and hashed. No live workflow state was inferred or fetched. The full68 native attempt retains its two failures instead of converting them into passes.

**What changed:** all three previous metadata attacks are rejected before parent projection, and the exporter build command covers its previously omitted direct project import. Frozen100 scope and41-only receipt status remain intact.

**Upstream implications:** keep review-object validation adjacent to projection, using only immutable parent IDs. The V2 schema prevents old records lacking these fields from silently surviving the upgrade.

**Downstream implications:** the future all100 receipt must verify exact source/head/tree, independently reviewed types/consumers, every public declaration/constructor, transitive axioms and complete compiler dependency channels. It must compare child registered dependencies against those actual compiler uses.

**Resurrected routes:** exact parent projection and the cold subset exporter are now better prepared for a real integration replay; neither supplies the missing59 proof obligations.

**New RH-relevant clues:** none. The progress concerns review and build integrity.

**Falsification checks:** repeated route, empty-statement, bad-dependency and stale-text probes now fail as required. Real symlink rejection and the historical static-check traversal remain unverified locally. Self-consistent review metadata still cannot substitute for a full child compiler receipt.

**Highest-leverage next moves:** publish the three exact changes as clearly marked draft work; preserve unaccepted mathematical candidates separately; implement the missing full receipt reader with adversarial tests; rerun cold CI and all unavailable native tests in a suitable environment; close each original root/consumer clause before any full-release promotion.
