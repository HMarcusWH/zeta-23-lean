# PR300 cross-runner source replay: candidate V2 repair (NOT RELEASE)

**Review status:** DRAFT, **independent human approval required**. This is a
conditional sub-PR against the PR300 branch, not a modification of accepted
PR299 or of the in-flight full replay at PR300 head
`a071894c49689b42930ae08a9eeaff380ad060f4`.

## Reproduced observations (2026-11-15)

- Failed PR300 Round4 run: `43641812084`; source producer job
  `132613437681` PASS, independent auxiliary `132656366727` FAIL.
- The traceback fails in the frozen
  `opica_round4/source_checker.py:158` with
  `InvalidRequest: Wrong runtime or precision`.
- Downloaded producer ZIP `14138689496`, unpacking the sealed source lane
  bundle, and inspected BOTH `source-producer/normal/result.json` and
  `source-producer/optimized/result.json`.
- Both producer modes claim `precision_bits=256` (allowed values 256/512).
- Producer runtime platform:
  `Linux-7.0.0-1017-azure-x86_64-with-glibc2.39`.
- Producer job ran on Azure, eastus2, runner image `20261111.370.1`;
  independent auxiliary ran on AWS, us-east-1, image `20261111.127.1`.
- V1 `runtime_identity()` embeds `platform.platform()` and demands
  equality with the verifier. Cross-cloud kernel strings therefore cannot
  be equal, even if the same Python and native-library bytes are present.
- The exact other differing runtime fields were not in the traceback;
  they must be diagnosed by a nonaccepting field-by-field receipt.
- Failure of auxiliary caused acceptance to fail correctly. Eleven producer
  lanes, independent CORE and CANONICAL all passed. RH and Step4 remain OPEN.

## Immutable historical authority

Original V1 checker Git blob:
`research/RHRC/integration/opica_round4/source_checker.py`
= `0dcfad9ebf16b342d6f31570ead0e8f69371974e`.

V1 is untouched. Its bound PR299 accepted source, request schemas, Arb
comparison and final 15-job Round4 V1 replay are immutable. No V1 result can
be relabelled V2 and no V2 candidate report is a merged theorem receipt.

## Proposed narrow V2 portability contract

`portable_runtime.py` implements a **closed nine-field runtime fingerprint**.
It requires exact equality of the Python executable path and SHA256, Python
version, optimize-mode flag, python-flint version and module SHA256, FLINT
version, and the **entire absolute-path SHA256 map for every native shared
library**. Types and key inventory are closed. No unverifiable/unexpected
runtime field or library may be silently dropped.

The ONLY possible difference is `platform`, parsed strictly as Linux
x86_64 using glibc, with the glibc version identical on both sides.
The kernel release/provider suffix may differ, but the two original
platform strings must be preserved in the audit record.

`source_checker_v2.py` is a focused copy of the original checker with:
1. the existing Round4 source backend and exact mathematical cases unchanged;
2. a cross-runner producer-report fingerprint comparison using the V2 policy;
3. every individual worker's runtime checked **exactly** against the original
   producer-report runtime (not a synthesized verifier platform);
4. each independently recomputed direct worker still bound to the actual local
   runtime and producing higher-precision Arb intervals;
5. unchanged source/tree, precision (256/512), source manifest, command,
   UUID, evidence-hash, stdout/stderr and interval containment requirements.

**Explicit claim firewall:** V2 reports
`OPICA4_SOURCE_NUMERICS_LANE_V2_CANDIDATE`,
`CANDIDATE_V2_RECOMPUTED_FINITE_SOURCE_NOT_RELEASE`,
`acceptance_eligible=false`, and
`CANDIDATE_V2_FINITE_INTERVAL_EVIDENCE_NOT_RELEASE`.

The existing V1 `ACCEPTANCE` job does not use V2 and is not bypassed.
No PR300 acceptance changes are installed by this sub-PR.

## Negative tests (required before adoption)

- Cross-provider Linux x86_64 glibc2.39: candidate identity match when all
  executable/native SHA256s and versions agree.
- Python executable / flint module / all four native library digest changes:
  reject.
- Changed interpreter path, Python version, FLINT/python-flint versions,
  `-O` mode, or native library inventory: reject.
- Changed architecture, operating system, glibc version, malformed
  platform, extra/missing fields, wrong types or invalid SHA256: reject.
- Original V1 file Git blob verified unchanged.
- Test in standard Python and Python `-O`.

## Adoption path, CONDITIONAL on Round4 full retry

1. Let PR300 full source-identical replay
   `a071894c49689b42930ae08a9eeaff380ad060f4` complete and harvest every
   job; a successful V1 retry is not proof cross-cloud reproducibility.
2. Only after independent source-policy review, create a separate **V2
   governed acceptance adapter** with complete source pins, original V1
   regression replay and additional V2 cross-host test. Maintain
   run/attempt-specific artifact binds, no stale cross-attempt reuse.
3. Publish a new exact reviewed successor policy and update source hashes
   outside this draft; require full compiler/axiom/no-sorry/RHKG/negative
   and independent recomputation gates on the resulting SHA/tree.
4. Do not change PR299 V1. Do not promote any candidate outcome to
   release acceptance merely because these unit tests pass.

**Claim ceiling:** numerical-source infrastructure candidate. No new Lean
theorem. Step4 OPEN; RH OPEN.
