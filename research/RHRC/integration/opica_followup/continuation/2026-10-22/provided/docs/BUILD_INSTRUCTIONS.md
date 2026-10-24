# Build and continuation instructions

## 1. Exact inputs

| Object | Pin |
|---|---|
| Accepted PR293 merge | `d53dd70d38b0762af130b1d19b795af259f505f5` |
| Accepted PR293 tree | `12691099f1a155a8bfa3ad4f6689146175b233b2` |
| Original PR294 checkpoint | `9b6a9a3a2badb4cff62a56c1158d9cef8759d30d` |
| Original PR294 tree | `545ea182910db9c8d05c4c7e8ee229d119a9aa28` |
| Assembled workspace tree, not an accepted commit | `023d49708f9d55a289de0ede477116897d149efd` |
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| Compiler commit | `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| Mathlib declared revision | `51e6992efd06126df61a496bebf8f49482a4e129` |

The snapshot is intentionally pinned; it is not a fresh assertion about the current remote PR tip. Reconcile any newer published source rather than overwriting it.

## 2. Verify the complete kit

From the extracted kit root:

```bash
python -B tools/verify_kit.py
python -O -B tools/verify_kit.py
python -B tools/check_coverage.py
```

`--quick` on the integrity verifier checks file sizes and all non-runtime hashes but explicitly skips the large runtime hashes. It is not a replacement for the full verification before use.

Do not add files inside the immutable kit while validating it. Put logs, editor caches and development work outside this directory. Generated `__pycache__` files would correctly fail the exact inventory check; the supplied commands use `-B`.

## 3. Restore a writable working copy

Requirements: Python 3.10+, Git, GNU tar and zstd. The bundled compiler/cache is Linux x86_64. Use WSL2 on Windows or use the source-only mode with a separately installed exact compatible toolchain on another platform. Do not mix operating-system object caches.

```bash
python -B tools/restore_kit.py --dest /absolute/work/opica --runtime
```

The destination must be empty and outside the kit. The script verifies the payload, imports the exact original Git objects, checks out the exact base tree, rehashes its 2,437 files, then installs the eleven source changes listed in `state/WORKSPACE_CHANGES.json`. The result is a deliberately **dirty, uncommitted working tree** on the original PR294 base. The script does not create a release commit, change a remote branch or push anything.

For baseline only:

```bash
python -B tools/restore_kit.py --dest /absolute/work/opica-base --mode baseline
```

For a source-only current restoration, omit `--runtime`. Obtain the exact toolchain/dependencies before building. Do not treat the source-only operation as a compiler check.

### Git-history boundary

The original exporter preserved selected Git objects, not a complete clone. Exact pinned source and protected parent objects are present, but some intermediate histories/trees are absent. `state/GIT_ARCHIVE_BOUNDARIES.json` enumerates the gaps. The restorer imports objects and checks out the exact available tree directly. A normal `git clone` traversal of this archive is not supported. Do not invent missing objects or reinterpret a broken historical traversal as a proof failure.

For full ancestry-dependent release checks or publishing, use a complete remote checkout at the required base and apply the guarded patch. Network access is needed to obtain Git history not included here.

## 4. The exported packages need local path overrides

The source manifest preserves the exact declared Mathlib revision. The original CI export deliberately omitted dependency `.git` directories. Consequently, `git -C .lake/packages/mathlib rev-parse HEAD` can walk upward and report the PROJECT commit: **that is not package revision verification**.

The runtime's provenance is the exact original hash-bound CI export plus its declared pin. It is not an independent Git checkout of Mathlib. The reassembly record is `state/RUNTIME_PART_VERIFICATION.json`; the original chunk hashes are in `evidence/cold41/EXPORT_SHA256.txt`.

Use the supplied wrapper, which writes an external `packages-local.json` object with `version` and `packages` fields and points each package to its existing exported directory:

```bash
python -B tools/lake_pinned.py --restored /absolute/work/opica -- env lean --version
python -B tools/lake_pinned.py --restored /absolute/work/opica -- build Zeta23.OPICAFollowup.Validation
```

Never run `lake update`, casually change the manifest/toolchain, or start a language server that runs Lake without these overrides. An earlier development attempt did exactly that and removed a usable package cache while attempting an unavailable clone. That incident is not proof evidence. The wrapper refuses `update`, `clean` and replacement package flags.

Only one broad cache-writing build should own the working directory at a time. For parallel proof work, use separate fresh object directories and explicit dependencies.

## 5. Reproduce narrow repaired-source gates

```bash
python -B tools/run_checks.py --restored /absolute/work/opica \
  --out /absolute/evidence/opica-narrow-new --lane lean
python -B tools/run_checks.py --restored /absolute/work/opica \
  --out /absolute/evidence/opica-python-new --lane python
```

The output directory must be fresh and outside the kit and source checkout.

The Lean lane checks the actual compiler version, builds missing project prerequisites recursively, then compiles these three candidate module files into fresh objects:

- `ComplexLocalMeasures.lean`
- `AuxiliaryCompletions.lean`
- `MaskedNativeRate.lean`

It runs `ExpectedComplex`, `ExpectedAuxiliary` and `ExpectedMasks`, preserves all diagnostics, validates the requested axiom output against `propext`, `Classical.choice`, and `Quot.sound`, and checks source hashes before/after. A failure, timeout, missing dependency or bad axiom list fails the lane.

The runtime already contains previously compiled project dependencies from the recorded CI export. This replay is **warm pinned dependencies plus fresh candidate objects**, not a new cold all-project CI run. The runner mirrors unchanged inherited object files into its fresh project namespace root because Lean's namespace-root resolution does not safely support a sparse leading `Zeta23/` directory. It does not use old versions of the three target objects.

The preserved original cache required six additional prerequisite builds for the repaired mask consumer: `NativeCausalExponentialWitness`, `NativeDampedCompletionResidual`, `NativeAdjointResidual`, `NativeCausalLaplaceMoments`, `NativeCausalLaplaceDerivatives`, and `Zeta23.OPICA.WeightedLaplace`. Recursive import handling covers that closure.

The Python lane runs the complete repaired parent `test_contract.py` and child `test_parent_extension.py` in normal and optimized Python. The supplied historical logs report 68 plus 26 distinct tests per mode. This is not the entire test suite. Test counts must come from the actual new logs, not an expected constant.

The auxiliary consumer was edited after a preserved failed invocation. A later interrupted packaging attempt reported a successful rerun but its complete raw result did not survive. This kit does not use an unavailable receipt to promote it. Run the supplied unchanged consumer and retain fresh evidence.

## 6. Apply the unified patch to a complete external checkout

At the exact clean PR294 base:

```bash
python -B tools/apply_patch.py --repo /absolute/full-checkout
python -B tools/apply_patch.py --repo /absolute/full-checkout \
  --apply --backup /absolute/backups/opica-before-current
```

Dry-run is the default. HEAD/tree, clean tracked/staged state, old/new file hashes and new-path conflicts are checked. All original files are backed up externally before changes. Newer concurrent modifications must be reconciled explicitly. The patch includes five new modules; it is not a tracked-only diff that drops new files.

The assembled workspace has 2,442 source files. Packaging evidence compares every one after replay, not just the eleven changed paths.

## 7. Correct cold-build exporter prerequisites

The old Linux subset validation build completed successfully but its exporter failed because a prerequisite object was missing. The repaired subset builder explicitly builds all directly imported project prerequisites:

```bash
lake build Zeta23.OPICAFollowup.Validation \
  Zeta23.RHRC.OpicaTypeExprExport \
  Zeta23.RHRC.SourceCandidateResolution
```

Then run the original subset audit on its actual source:

```bash
python research/RHRC/integration/opica_followup/build_receipt.py \
  --preparation-only --requested-head EXACT_CHECKOUT_HEAD \
  --requested-base d53dd70d38b0762af130b1d19b795af259f505f5 \
  --output-dir /absolute/external/subset-evidence --lake /path/to/pinned/lake
```

That existing builder still selects **41** original roots. It cannot certify 100. A dirty current snapshot must be recorded as such; passing a requested base commit does not make its new working-tree bytes committed. In the portable path-override environment, use an executable shim around `tools/lake_pinned.py` when a subprocess expects a Lake executable. Do not quietly allow dependency cloning.

For genuinely cold Linux evidence, use a complete pinned checkout with a pinned Mathlib cache but remove/invalidate project oleans before the broad build. The original cold-41 receipt in this kit demonstrates that older source only. It is not a cold receipt for the assembled repairs.

## 8. Finish the original acceptance, without replacing it by the kit checks

Read every original root's statement contract and rejection conditions. Preserve both foundational PDFs, frozen JSON/Markdown bytes, original root identities, expected source/damping/palette conventions and the retained C3 counterexample.

The remaining work includes:

- Forty-eight complete primary implementations absent from this kit, and five unaccepted earlier candidates.
- Full expected-type and actual-domain consumers and all new aggregate type/constructor/private dependency audits.
- Complete facade/import coverage, source-reviewed route-less claims and bindings, and the exact compiler-derived mapped claim dependencies.
- Fresh all-100 child receipt linkage in the full parent-extension path. The metadata repairs alone are not sufficient.
- Full-release CLI, mutation tests, cold current-source build, canonical Linux regeneration and all workflow dispositions.

Do not register an uncompiled candidate, treat a record hash as a proof, supply the native conclusion as a premise, or count supporting declarations as original roots. Neither this archive nor any narrow replay changes `C_RH`, A-X, B-Y, C-Schur or other independent closing obligations.

The complete planned targets/lanes are preserved in `state/REQUIRED_BUILD_TARGETS.json`. After the corresponding implementation exists, the declared final build includes the follow-up facade, its Validation and RHRC audit module; the current missing facade correctly prevents full completion. Existing canonical producers remain authoritative:

```bash
python research/RHRC/tools/materialize_derived_state.py --write
python research/RHRC/tools/materialize_derived_state.py --check
```

Stage authoritative new files before canonical generation because its census uses tracked paths. Run full parent/child/integration suites in both Python modes. Frozen numerical replays require the exact dependency versions/hashes in `requirements-checks.txt` and `python-checks.lock`; wheel payloads are not supplied in this runtime. Keep those original locks unchanged and acquire the locked wheels in the build environment.

## 9. Post-Green research

After each meaningful new result, inspect its exact proof, hypotheses, imports and physical consumers. At final acceptance, harvest every inherited and new workflow/job at the actual checked source: formal validity, regression, research-producing, completeness. Report its scientific disposition, not only a green process status.

Write all nine outcomes: exact formally true state; workflow harvest; changed scope/assumptions/dependencies; upstream implications; downstream implications; resurrected routes; labelled new clues; falsification checks; highest-information next moves. Do not stop at green CI. RH, Step 4 and independent closing inequalities remain OPEN unless their own exact proof gates succeed.
