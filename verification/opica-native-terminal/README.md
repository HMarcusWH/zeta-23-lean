# Native compact arithmetic source-port Step 4 — successor to #318

**SOURCE CANDIDATE ONLY. RH_OPEN until fresh kernel and independent claim gates.**

Base is #316 2fe4a756e8576203cfb009314861616accdb6dde (tree 4571fe6cc82466115beae5bea5037071ebec3524). Reuses the corrected #318 principal adapter and native C1 consumer as source templates. One-time acquisition from the pinned Apache-2.0 compact rewrite, 72fead102f663d5c7a407964a13dc0cf9d977207, attributed to Levent Alpöge with Claude and Anthropic. Exactly 792 arithmetic modules are relocated into Zeta23Arithmetic (791 unchanged mathematical source bodies, one frozen endpoint-free arithmetic cut). No upstream RH/GRH endpoint, foreign proof package, precompiled supplier object or external source checkout is used in the validation build. The workflow commits actual source files to this branch before compiling. Original mathematical names are retained for compatibility; this is NOT independent invention of the arithmetic.

The common epoch is a **single Lake package**, with the arithmetic and native libraries in one repository under Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Standard Mathlib dependencies only. The historical default project pin is not modified; the versioned native epoch is staged from the exact committed tree. This protects the old #316 validation workflows from accidental toolchain changes. No source is regenerated in the formal build. Only the acquisition job clones the attributed source, with read-only permission; publication is limited to this new branch and the explicit source paths.

Proof chain: local eventually_primeError_le_rpow → local finite-tolerance criterion → native actual critical-line confinement → both full physical slices at error zero → exact C1 → exact Mathlib RiemannHypothesis. All-tolerance strip transport is RH-equivalent after reflection, is derived rather than assumed; this is the shorter direct-slice route, not the separate v1.0 integrated literal-ramp/energy proof. That energy formalization remains OPEN; no independent native arithmetic proof is claimed.

Targets:
- Zeta23.OPICANativeTerminal.both_parity_zero_floor_arithmetic
- Zeta23.OPICANativeTerminal.step4C1_native_arithmetic
- Zeta23.OPICANativeTerminal.riemannHypothesis_step4_native_arithmetic

Gate hierarchy: reversible source port checks; commit/tree and exact standard dependency pins; common native build and exact root type; all reachable values/types/structural dependencies, origin allowlist and allowed axioms; stock kernel module replay; fresh independent stock build and receipt comparison. No automatic promotion. Alternate checker and project canonical review remain necessary. No changes to #316, #317, #318 or main.

After materialization, build without any supplier network access:
`python verification/opica-native-terminal/epoch.py --repo "$PWD" --out /tmp/native_epoch --receipt /tmp/source.json --head "$(git rev-parse HEAD)"`
then from /tmp/native_epoch run the standard Mathlib cache setup, and the run.sh script with absolute paths. The source materialization workflow runs once on an empty port branch; subsequent repair work must use committed source and a separate compile-only lane.
