# Stage-record pipeline (how Stages 4 to 18 were produced)

These are the exact scripts of Stage 18, with the session-specific paths replaced by
`OPICA_REPO` (repository root, default `/home/user/zeta-23-lean`) and `OPICA_SCRATCH` (a scratch
directory outside the repository). Copy them to your scratch directory and rename them per stage.
Then adapt the stage-specific strings: module and consumer names, the root text, the negative-control
list, the numerics summary and the expected ledger counts. They write only where stated; nothing here
grants theorem authority.

## Toolchain

- `export PATH=$HOME/.elan/bin:$PATH`. Lean v4.33.0-rc2 and Mathlib `51e6992e` are pinned by
  `lean-toolchain` and `lake-manifest.json`. Never run `lake update` or change pins.
- Scratch compile:
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false file.lean`.
  Consumers also take `-DmaxHeartbeats=800000`.
- Module plus consumer before installing:
  `(cat Module.lean; tail -n +2 Consumer.lean) > Combined.lean`. Put all imports first.
- Negative controls run from a scratch directory holding a copy of `lean-toolchain`:
  `lake --dir $OPICA_REPO env lean neg.lean`. They must fail, each for its intended reason (read
  the errors).
- Numerics: a venv with `mpmath==1.3.0`, plus `numpy==2.1.3` where FFTs are needed. Run with
  `python -I`. `replay_controls.py --include-numerical` needs mpmath.

## One stage = a code commit, then a record commit

1. **Code commit.**
   - Add `Zeta23/OPICAFollowup/<Module>.lean`. Its project imports must be exactly the
     BUILD_MANIFEST `direct_project_imports`; extra Mathlib imports are fine.
   - Add `consumers/Expected<Module>.lean`: definition audits (`rfl`), the root restated in full,
     domain consumers and `#print axioms`.
   - Add both names to the `MODULES` and `CONSUMERS` tuples in `run_candidate_checks.py`.
   - Run `lake build Zeta23.OPICAFollowup.<Module>` and the consumer.
   - Check new top-level names for clashes with every `Zeta23/**/*.lean` (Consumers imports many
     modules).
   - Run `python3 -B refresh_manifest.py`. It updates the validator pin.
   - Run `python3 -B refresh_navigation.py --write`. This is required if the code commit is pushed
     on its own; the CI preparation job checks the module table.
   - Run `validate_contract.py --phase preflight --output X`; expect exit 0.
   - Commit with `git add -A Zeta23/OPICAFollowup/<Module>.lean research/RHRC/integration/opica_followup`.
2. **Evidence on the clean committed tree.** `stageNN_evidence.sh` runs the narrow runner, the
   W04/W07 (52 receipts) and W06 (14) workflow heredoc consumers and the negative controls. Copy
   into `evidence/current-codex/stageNN/`:
   - `runner/`: `Expected*.log`, `version.log`, `CHECK_RESULT.json` and `commands.json`, plus
     `build.log.gz` and `source-before.json.gz` made with `gzip -9 -n`. Do not copy a raw build.log.
   - `consumers/opica-w0*`, `negative-controls/` and `numerical-falsification.py`/`.log`.
   - `version.log` from `lake env lean --version`.
3. **CI harvest** of the previously pushed head, complete or partial. Follow the schema of
   `stage16/ci-harvest-bd918c7c.json` (complete) or `stage17/ci-harvest-c6ce649d-partial.json`
   (partial). Record every run and job disposition. In-progress or cancelled runs are recorded as
   such, never as passes.
4. **Handover** `STAGENN_HANDOVER.md`, in the format of the Stage 16 to 18 handovers. It must end
   with the nine Post-Green Research Pass items and the Still OPEN list.
5. **Record.**
   - `update_ledger_stageNN.py`: root gates; it asserts the narrow and absent counts.
   - `docs_stageNN.py`: exact-string edits of AGENTS.md, README, REMAINING_WORK and
     DOCUMENTATION_INDEX. Each old string must occur exactly once.
   - `refresh_navigation.py --write`, then `--check`.
   - Suites in both Python modes:
     - `python3 -B [-O] -m unittest discover -s research/RHRC/integration/opica_followup/tests -p 'test_*.py'` (185 tests);
     - `... -s research/RHRC/integration/opica/tests -p test_contract.py` (82 tests).
   - `replay_controls.py --modes normal optimized --include-numerical --output-dir X`. Expect p0 5112,
     round1 18862, round2 14672 and final 1274 checks per mode, and three numerical suites
     CONSISTENCY_ONLY.
   - `stageNN_status.py '<suites text>' '<replay text>'` (writes STATUS.json), then
     `refresh_manifest.py`.
   - Gates: preflight exit 0 (PASS_PREPARATION_ONLY); release exit 1 (FAIL_RELEASE_INCOMPLETE).
   - Commit with `git add -A AGENTS.md research/RHRC/integration/opica_followup`.
6. **Push** with `git push -u origin research/opica-native-followup`.
   - Pushing while CI runs cancels those runs. Their summary jobs (`contact-calculus-complete`,
     `Complete 44-check execution harvest`) then fail; record them as superseded, not as defects.
   - The long research replays (post-284 source inertia, post287 WP2/WP4) take about two hours.

Commit messages end with the session attribution trailer required by the harness. They never name
a model.

## CI facts

The designed fail-closed red gates on every head are:
- Full release readiness (PR and push);
- opica-contract and opica-component-summary;
- python-rhrc and rhkg-compiler-receipt.

Everything else is expected green. Never disable or relabel a red full-scope gate.
