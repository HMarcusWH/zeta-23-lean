# Direct arithmetic-window verification

This is a separate verification environment for
`Zeta23.RHReference.riemannHypothesis_direct_arithmetic_windows`.
It extracts the original arithmetic window inequality before the original
zero-exclusion consumer, then uses native literal energy, the cofinal C1
handoff, and the actual generated even/odd pair. The mathematical construction
and public contracts are explained in [the route document](../../docs/direct-arithmetic-window.md).

**Source implementation is not a verification receipt.** A complete accepted
run is identified by `DIRECT_WINDOW_ACCEPTANCE_V1` in `acceptance.json`, bound
to the exact candidate head/tree, source pins, run and attempt. Hosted source,
native-frontier, or checker-preflight success alone does not qualify the full
arithmetic supplier or the terminal. The historical strict verifier is unchanged.

## Locked source and source ownership

[`SOURCE_LOCK.json`](SOURCE_LOCK.json) records:

- Native mathematical baseline `d649f57310bb05a306d3d488ba019e4ab45b0b20`, with
  the existing CI repair `3aefdaa46a4a16c5fd9978b9cf65b251c38ca2c1` as the new base.
- Original arithmetic repository `CocoSgt/riemann-hypothesis-lean`, commit
  `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
- Source Lean `4.33.1` and Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`, including all transitive package pins.
- `lean4export` commit `15f6055e299ad5b89345e533cc2192f4cc00f659`, built with
  **4.33.1**, and the official **4.36.0** independent judge.

The original source is acquired externally at its exact commit. It is not
copied into this repository or assigned the compact edition's license. The
reported author-archive hash is provenance information; this implementation
does not claim a newly performed archive-to-mirror comparison.

[`OWNERSHIP.json`](OWNERSHIP.json) binds all 27 duplicate native analytic
modules to their authoritative original modules by both source hashes. Only
the staged native copies become import-only shims. Original files remain
unchanged. Additional compatibility edits, if required, must be individually
listed with their preimage, replacement hashes, and explanation in
[`COMPATIBILITY.json`](COMPATIBILITY.json). An unlisted duplicate or changed
preimage fails staging.

The staged configuration retains the original per-library options, including
the `GroundTheoryFields` instance-synthesis budget. Native modules keep their
own library options. The repository's default compiler and Mathlib pins are
not changed.

## Size and runner selection

The initial import-closure measurement found **175,173 original modules** in
the supplier closure, approximately 17.37 million source lines and 1.03 GB of
source. The earlier handoff has a smaller proof interface, but its source
import graph is almost the whole original archive. The native-only consumer
is a separate narrow stage.

The original archive's published build notes report a 48-core, roughly 503 GB
machine, multi-hour compilation, a 61.6 GB export, and approximately 163 GB
peak exporter memory. Those measurements are not measurements of this new
composition. See the pinned [checking procedure](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/cfabf56cd40776cf3f46d6d462f1c5e09dcfe607/verification/CHECKING.md)
and [resource/checker notes](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/cfabf56cd40776cf3f46d6d462f1c5e09dcfe607/verification/NOTES.md).

`run.py resource-pilot --full` refuses a full run below an operational guard of
192 GiB available memory and 300 GiB available disk. Container memory limits
are included. These are conservative scheduling guards, not proved minimum
requirements or a guarantee that every run will fit. Provision for the actual
pilot and retain the raw resource logs.

`cleanup_completed.py` removes only a module's `.setup.json` after its matching
successful `.trace` is newer. It preserves source, active setup files, objects,
and dependency caches. This prevents the known accumulation of enormous Lake
setup metadata without bypassing compilation.

The workflow runs source/canonical checks, the native frontier, and small
independent-checker controls on ordinary hosted Linux. Full verification is an
explicit `workflow_dispatch` choice with runner labels supplied by the operator.
Before merge, it can also be activated by the PR label
`direct-window-full-verification`, restricted to a same-repository PR in
`HMarcusWH/zeta-23-lean` whose exact head branch is
`research/direct-arithmetic-window-20261128`. This pre-merge route uses the fixed
large-runner labels and 16 build threads. Adding/removing the label triggers a
fresh workflow; it is not necessary to merge unverified code to enable the gate.
The default `rh-original` label describes a required provisioned runner;
**it does not assert that such a runner is registered**. A missing or skipped
full run never creates acceptance.

## Staging

Use a clean, committed checkout for qualifying runs. Keep outputs outside it.
The script preserves `.lake/packages`; production staging requires that no
project `.olean` files exist at entry.

```bash
set -euo pipefail
DW_REPO="$PWD"
DW_WORK="/absolute/path/to/fresh/direct-window-run"
mkdir -p "$DW_WORK"
bash verification/direct-arithmetic-window/acquire.sh "$DW_WORK/original"
python3 -B verification/direct-arithmetic-window/stage.py \
  --repo "$DW_REPO" --original "$DW_WORK/original" \
  --stage "$DW_WORK/stage" --receipt "$DW_WORK/source.json" \
  --head "$(git rev-parse HEAD)" --scope terminal
```

Available scopes are `terminal`, `supplier`, `native`, and `controls`. The
receipt records exact entry modules and import closures. The `native` scope
includes the principal-level normalization but does not compile the large
unconditional supplier. A narrow receipt cannot satisfy a full terminal gate.

`--allow-dirty` exists only for local proof development; its receipt is marked
`development_only` and is rejected by `run.py` and `evidence.py`. `--restage`
first authenticates the old staged files, replaces only those sources, and
preserves `.lake`. It does not turn an incremental development build into a
fresh-source receipt. Recreate a cold stage for qualification.

## Build, export, and judge

Install the official pinned source and judge toolchains. Fetch only the official
Mathlib cache with `lake exe mathlib/cache get`; never restore a submission cache
or run `lake update`. Set `MATHLIB_CACHE_GET_URL` to
`https://cache.mathlib.org/mathlib4` and `LAKE_ARTIFACT_CACHE=false`.

The workflow gives executable commands for all phases. The common runner API is:

```bash
export DIRECT_WINDOW_RUN_ID="unique-local-run-id"
export DIRECT_WINDOW_RUN_ATTEMPT=1
DW_SOURCE_PREFIX=$(elan run leanprover/lean4:v4.33.1 lean --print-prefix)
DW_JUDGE_PREFIX=$(elan run leanprover/lean4:v4.36.0 lean --print-prefix)
python3 -B verification/direct-arithmetic-window/run.py supplier-frontier \
  --stage "$DW_WORK/stage" --source "$DW_WORK/source.json" \
  --source-prefix "$DW_SOURCE_PREFIX" --jobs 16 \
  --out "$DW_WORK/evidence/supplier-frontier"
```

`native-frontier` and `common-terminal` use the same API. `bootstrap-tools`
builds the locked exporter. `prepare-challenge` creates a separate, Mathlib-only
challenge project, fetches its own official cache, and exports the exact stock
statement before the untrusted original build runs. `checker-preflight`
qualifies the tools and rejection behavior before the expensive build.

Builds run in bubblewrap with no network, hidden home directories, a read-only
source compiler, source and dependencies, and explicitly writable build/audit
directories. The export stage additionally makes the compiled build read-only.
The judge runs from a separate empty directory with the trusted configuration;
it receives export files and does not execute the original project's Lake code.
A blocked namespace sandbox is a failed infrastructure gate, not a reason to
turn off isolation.

The independent phase creates a **fresh** solution export and invokes:

```text
lake comparator --config comparator/config.json
  --challenge-from-export CHALLENGE_EXPORT
  --solution-from-export FRESH_SOLUTION_EXPORT
```

The command uses official Lean 4.36.0. Its configuration requires Lean default,
Lean paranoid, and Nanoda. `alternate-checker` authenticates the same three-kernel
invocation and export; it does not pretend that copying the log is another run.
Do not add blanket `--paranoid`, which enables additional checkers with known
cross-version incompatibilities. The source compiler alone is not the final
independent acceptance gate.

Large solution exports are retained outside the small evidence artifact, using
the candidate SHA, run ID and attempt in the filename. The dispatched workflow
uses the selected runner's `$HOME/direct-window-exports`. Ensure that location
has capacity and an appropriate retention policy. Hashes and the actual location
are recorded in the evidence. Earlier published exports are never reused as the
solution for this route.

## Dependency and statement checks

[`AuditCore.lean`](AuditCore.lean) traverses types, proof values, opaque values,
inductive constructors, and recursor rules, rejecting uninspectable dependencies.
It reports complete edges for every accepted root. The supplier audit excludes
native consumers and the original zero-exclusion endpoints. The terminal audit
requires arithmetic inputs, both normalizations, positive-energy integration,
the cofinal C1 closure, native comparison, and the actual generated pair. It
excludes the compact fixed-strip/Perron supplier and completed original RH/GRH
endpoints.

The exact terminal type must be the constant `RiemannHypothesis`, without extra
binders. Non-root dependencies whose types are definitionally equal to stock RH
are rejected, including aliases. This is not an algorithm for deciding every
logically equivalent RH formulation; inspect the source cut and full dependency
graph as well. Conditional native consumers and the attributed conditional
original Landau/pole analysis are permitted.

Allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
`ROOTS.json` binds the required roots and dependencies. An independent supplier
example fixes its full quantifiers and absence of residual premises.

The deliberately invalid `SmokeFixtures.lean` belongs only to an isolated
Init-only control project. It includes a mock target named `RiemannHypothesis`
solely to test definitional-alias rejection; it is never imported with Mathlib
or by any production proof or audit root. The challenge's placeholder belongs
only to the trusted statement, outside the solution closure.

## Rejection controls and acceptance

```bash
python3 -B verification/direct-arithmetic-window/controls.py
python3 -O -B verification/direct-arithmetic-window/controls.py
```

The Python controls exercise safe paths, nested comments in import parsing,
changed staged bytes, missing/mixed receipts, and proof-only NDJSON tampering.
`controls.py --audit` compiles real Lean fixtures for wrong types, missing
dependencies, custom axioms, `sorry`, hidden endpoints, type-only edges, unused
constructor edges, a definitionally aliased endpoint, and forbidden origins.
Each rejection must contain the expected diagnostic.

`controls.py --checker` builds and exports a valid Init-only proof, requires it
to pass the three configured kernels, and then requires rejection of a wrong
statement, an extra axiom, and a tampered proof with an unchanged statement.
The entire tiny Init module is exported because the judge needs core markers
such as `outParam` even when those markers are absent from the proof of `True`.

The final aggregate requires all eight phases: source lock, checker preflight,
supplier frontier, native frontier, common terminal, independent replay,
alternate checker, and canonical generated-state checking. It revalidates every
file digest, root/edge inventory, export identity, source pin, candidate head/tree,
and run/attempt. Missing, skipped, canceled, failed, stale, or mixed evidence is
rejected. Only the aggregate writes `acceptance.json`.

```bash
python3 -B verification/direct-arithmetic-window/evidence.py aggregate \
  "$DW_WORK/evidence" --output "$DW_WORK/evidence/acceptance.json"
```
