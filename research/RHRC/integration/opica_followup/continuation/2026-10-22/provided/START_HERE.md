# OPICA PR294 — single-source continuation kit

**Snapshot: 22 October 2026. This kit is complete as an archive of the available implementation and evidence. The 100-root follow-up itself is NOT complete or accepted. RH, Step 4 and the independent closing inequalities remain OPEN.**

## Start here

1. Read `STATE.json`, then `docs/BUILD_INSTRUCTIONS.md`.
2. The one current source snapshot is **`workspace/`**. It is the pinned PR294 baseline plus the explicitly listed eleven source changes. Do not apply historical candidate overlays on top of it.
3. The controlling requirements are the original **100 roots / 28 acceptance units** in `workspace/research/RHRC/integration/opica_followup/`. `state/ROOT_LEDGER_100.json` preserves every original contract and separates implementation, compilation, consumers, axioms and full-release status.
4. Both foundational PDFs, the unchanged Post-Green Amendment v1.1 and the preserved C3 evaluation are in `inputs/`. The amendment remains additional research input; no new acceptance obligations were silently promoted.
5. The complete patch is `patches/current_from_9b.patch`. Use the guarded applicator only at its exact base, or restore a fresh working copy using the instructions below.
6. `archive/` is provenance, not another working source. In particular, the **104-root alternative is NOT controlling**.

## Evidence state

| Category | Count | Meaning |
|---|---:|---|
| Original primary roots | 41 | Source-bound cold subset receipt preserved and its 2,437 source files rehashed |
| Repaired mask/measure primary roots | 3 | Recorded narrow compilation, independent consumer and standard-axiom gates; aggregate acceptance still pending |
| Auxiliary-completion primary roots | 3 | Module compilation recorded; complete successful consumer rerun receipt is not preserved here, so the conservative consumer gate remains pending |
| Other prior primary candidates | 5 | Unaccepted, failed or blocked; retained for repair, not counted as proofs |
| Missing complete primary candidates | 48 | Explicitly listed with their original contracts |

There is no fresh all-100 compiler receipt, completed registration/canonical regeneration, final CI acceptance or RH proof. A partial root count is not release authority.

## Restore and use

The ZIP includes Linux x86_64 Lean and the pinned exported Lake cache. Install Python 3.10+, Git, GNU tar and zstd. Reserve at least 20 GB of free working space in addition to the downloaded ZIP. On Windows, use WSL2 for this bundled Linux runtime; do not load Linux objects in a native Windows toolchain.

```bash
python -B tools/verify_kit.py
python -B tools/restore_kit.py --dest /absolute/path/opica-work --runtime
python -B tools/run_checks.py --restored /absolute/path/opica-work \
  --out /absolute/path/opica-checks-new --lane all
```

The checker produces narrow replay evidence only. It does not update the root inventory or assert release acceptance. Read the build guide before using Lake: **the exported dependency directories omit their `.git` metadata, so the supplied local-package override is essential.**

## Kit map

- `workspace/`: complete current source, frozen requirements, existing research machinery.
- `inputs/`: normative source PDFs, papers, amendment, instructions and historical research references.
- `baseline/source/`: exact original PR294 source archive and selected-history Git object pack.
- `runtime/`: exact reassembled compiler and Lake export; executable inputs, not new proof evidence.
- `consumers/`: independently written expected-type/domain consumers for the repaired modules.
- `patches/`: unified baseline-to-current patch, including all five new WIP files.
- `tools/`: verification, guarded restore/application, pinned Lake wrapper, narrow replay and coverage checks.
- `state/`: complete 100-root ledger, changed-file hashes, targets and explicit Git-history boundaries.
- `evidence/`: cold subset receipt; latest source-bound local receipts; regression logs; packaging/replay evidence with failed attempts retained where supplied.
- `archive/`: unchanged earlier handovers, second-kit review, candidate deliveries and historical evidence packages.
- `docs/`: build, handover, authority/precedence, remaining work and research continuation.
- `MANIFEST.json`: every payload file's byte count and SHA-256, excluding only the root manifest itself.

The outer ZIP's SHA-256 is published beside the download, not asserted inside its own bytes. Manifest and archive integrity do not certify the mathematics.
