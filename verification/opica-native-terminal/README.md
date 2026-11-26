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


## Repair epoch R1 (2026-11-26)
The one-time acquisition and source publication are complete at b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736, tree ad3dc3ced9a58dbd4619f8635600791a692bce34, run 45716397974. That job compiled `Zeta23Arithmetic.New.ArithmeticOnly` but failed the principal adapter and old native Mathlib migration. The separate compact run 45713758389 built New.ArithmeticOnly and failed its auditor on an ambiguous origin binder. Neither reached the terminal validation. The 792 relocated arithmetic modules and PORT_MANIFEST.json are frozen; the new adapter is tracked separately.

The R1 repair manifest binds every changed path to the exact original and repaired Git blob. The historical default Lean epoch is not changed; this branch's compatibility edits are qualified only in the explicitly staged Lean 4.35.0 project. Older-pin requalification and canonical admission remain required; no historical receipts inherit authority from this repair. The retired additive tactic implementation is replaced by a compatibility spelling for stock linear_combination with abel, rather than inventing new mathematical axioms or global instances. All other mathematical edits target proof bodies; compiler/type comparison is pending.

The replacement workflow is read-only and compile-only. It never fetches lsernau/grh-lean or republishes source. Source custody and optimized negative controls precede audit smoke. Separate native and arithmetic frontiers must pass before the full common-pin candidate runs. Independent stock replay reconstructs the same committed source again and compares root types, permitted axioms, membership sets, and complete type/value/structural edges for arithmetic and terminal roots. A fresh stock kernel replay is not an alternate kernel. Comparator/alternate-checker and claim-validation admission remain explicitly OPEN. The direct-strip supplied route is unchanged; the independent arithmetic and literal-energy formalization are not closed by this repair. 


## R2 — versioned compiler compatibility and verification

R2 restores the ten historical native source blobs exactly to #316 / R0.
The common Lean 4.35.0 source package is reconstructed from the committed tree
by applying exactly the ten full-source compatibility replacements listed in
`compatibility/lean-4.35.0/OVERLAY_MANIFEST.json`. Seven are the R1 blobs,
three are revised proof bodies (Borel–Carathéodory denominator clearing,
four logarithmic continuity sites, adjoint kernel projection preservation).
The 792-module arithmetic port, original PORT_MANIFEST, R1 principal adapter,
and exact Terminal.lean are frozen. The R1 manifest is kept under history/.
No historical toolchain or default lake target is migrated.

R2 implements source-lock and optimized-mode rejection controls; three
independently diagnosable native leaf jobs; complete native and arithmetic
frontiers; public compiler declaration type comparison across the two epochs;
16 exact named root audits, including both parity floors and the actual
critical-line intermediates; fresh stock terminal reconstruction and full
type/value/structural edge comparison; and a separate sandboxed Mathlib-only
RH challenge using Lean 4.35's built-in `lake comparator`, its matching
`leanexport` and the bundled nanoda kernel. Deliberate negative proof fixtures
and the challenge placeholder are outside the claim-bearing source closure.
The comparator must run on a fresh source stage, without fake sandbox or
prebuilt solution. Unsupported checker/sandbox or unequal public type
expressions are blockers, not successful verification.

Each passing job emits a source-bound qualification receipt with evidence
hashes. The aggregate packet is explicitly READY_FOR_MANUAL_CANONICAL_REVIEW,
not RH_PROVED: all attached historical workflow results must still be harvested,
semantic review and explicit admission are required. The literal-energy route
and independent arithmetic invention are not claimed. The arithmetic R1 run
was still in progress at R2 implementation; newly exposed errors require an
additional explicit repair epoch, never changes to the frozen arithmetic port
by default. Full reruns (rather than failed-only reruns) regenerate the same
attempt's source-lock and other evidence artifacts. Local pinned Lean execution
was not available to the implementation agent; CI is authoritative.

R2 local execution used the R2-specific receipt schema and environment variable.
For the current epoch use the R3 instructions below. The modes were smoke,
leaf-pnt, leaf-gamma, leaf-operator, native, arithmetic, terminal, independent,
and comparator. Each mode requires a freshly reconstructed
stage, pinned Mathlib setup and no existing project .olean. The final workflow
also compares compiler public types against the restored historical epoch.

## R3 — repair the two remaining exposed native elaboration errors

R3 starts at R2 cfc0e6bc92be1db226d4a84f9542ace9c4868e16, tree 1732a82a22c6d48230a865c81249aa090b428afe, run 45794998702.
The historical proof files, eight other overlay variants, 792 arithmetic
modules, R1 principal adapter, root inventory, AuditCore and terminal theorem
are frozen. Only the IntMu private continuity helper and the final typed
subtraction in nativeAdjointResidualStep_kernelProjection_preserved change.
The Gamma repair uses the explicitly instantiated composition lemma at the
common Mathlib pin. The projection repair uses map_sub, congrArg in the
kernel submodule and sub_zero as separate steps. Neither theorem statement
nor public definition is changed.

The R2 repair manifest is archived byte-for-byte. R3 validates the historical
R1/R2 lineage and the exact R2-to-R3 changed-path inventory; the two repaired
overlay replacements have new bound blob IDs, and the other eight must match
R2 exactly. All previous scope/staging/receipt controls remain mandatory;
new controls reject an unauthorized R2 delta, overlay changes and R2 rollback.
R3-specific receipts cannot be mixed with earlier epochs.

The checker-preflight job runs a small independent scratch project in parallel
with the expensive frontiers: real stock replay, fresh kernel replay, real
bubblewrap and nanoda acceptance of a clean proof and rejection of a well-typed
forbidden-axiom solution. It does not build or use an RH solution or qualify
the RH theorem. Both preflight and the full independent stock replay are
prerequisites for the full alternate-checker job; all must pass before manual
canonical review. The historical regressions still require a complete harvest.

Local execution: stage the exact R3 checkout with epoch.py, keep the
source-lock receipt outside the stage, and set OPICA_R3_LOCKED_SOURCE_RECEIPT
to the matching receipt. Use run.sh with absolute paths and mode smoke,
checker-preflight, leaf-pnt, leaf-gamma, leaf-operator, native, arithmetic,
terminal, independent or comparator. Every mode starts from freshly
reconstructed source and pinned dependencies, without project oleans.
For checker-preflight and comparator a functioning real bubblewrap sandbox
is required; no unsandboxed fallback is admitted.

R1 and R2 arithmetic-frontier jobs were still running at the implementation
snapshot and their unfinished logs were unavailable. No speculative
arithmetic adapter repair is included. Local pinned Lean execution was
unavailable; the proposed proof bodies and verification pipeline remain
qualification-pending. RH_OPEN; no automatic claim promotion, no assertion of
independent arithmetic invention, and no closure of the separate literal-energy route.

## R4 — downstream compatibility and checker qualification

Baseline: R3 176e582916156e1df90252aeb7746dd904f24983, tree 11ebe592671e8e604d86ab851dc39dabdef7f02c, native run 45804486743.
R3 compiled all three compatibility groups; its complete native frontier
exposed eight first-cause proof sites (12 diagnostics) in four modules.
R1 arithmetic passed its four-root audit; expanded arithmetic qualification
remains independent. The R3 checker preflight passed stock and fresh replay,
but Bubblewrap could not establish its UID map; nanoda was not reached.

R4 adds exactly four common-pin replacements: UniversalSincSourceCharacteristic
(mapped probability mass), RectangleLogDeriv (two pointwise multiplication
conversions), WeilEF.Landau (finite pointwise product and two nonnegative
ordered-product lemmas), and IntMuChi (two explicit continuity repairs).
The 10 R3 replacements and all historical source, 792 relocated arithmetic
modules, principal adapter, terminal proof, original port manifest, AuditCore,
and sixteen-root inventory remain frozen. All four new replacements carry
their actual historical provenance; no invented R1 history. R3 is archived.
The type surface now covers all 13 mathematical overlay modules, excluding only
the retired tactic engine. Cross-epoch comparison is a common-terminal
prerequisite. Four explicit repair groups run before the native frontier.

The two checker jobs use Ubuntu 22.04 as a candidate isolated runner.
Both run real unprivileged namespace and Bubblewrap probes, record runner
information and hash the same checker binaries. The small comparator accepts
a clean proof and rejects a forbidden axiom before full alternate verification.
Final admission requires matching checker OS/architecture/tool digests, not
a mere executable version string. No fallback bypasses sandboxing.

Use the R4 receipt and OPICA_R4_LOCKED_SOURCE_RECEIPT. In addition to the
R3 modes, run leaf-analytic on an independent fresh stage. All required
receipt controls run in normal and optimized Python. The final packet
recomputes public type comparison and retains manual admission and historical
workflow harvest. The optional arithmetic-only endpoint is deliberately not
part of this frozen repair. Local Lean execution was unavailable; CI must
qualify these proposed proof bodies and runner configuration. RH_OPEN.


## R5 — native downstream API migration

Baseline: R4 92bfa975807f5bc22975c3f403ab79e680d64065, tree 69baeb56a6e14aef7c68ec59ceaba8576e94f01e;
native run 45814873480, native-frontier job 139907926078. R4 compiled all
four compatibility groups and exposed five primary errors in three modules.
R2 arithmetic-frontier job 139833049273 passed all six roots and both stock
kernel replays; R4 checker preflight 139901632977 passed real sandbox,
stock/fresh replay, clean nanoda acceptance and forbidden-axiom rejection.

R5 adds exactly three compatibility overlays: UniversalSincSourceTail (two
mapped mass-one proofs), XiPrime.ExplicitFormula.ZeroFree (pointwise product),
and OPICARound4.SourceDiscrepancy (toLpLin_apply and toLpLin_one).
All fourteen R4 overlays, historical sources, 792 relocated arithmetic modules,
principal adapter, original port manifest, exact terminal declaration, AuditCore
and sixteen-root inventory remain unchanged. R4 manifest archived byte-for-byte.
Public type comparison covers sixteen mathematical modules. Ubuntu 22.04 and
all independent checker and source-lock gates remain mandatory.

A deterministic lexical migration-family scan of the staged terminal import
closure is produced in source-lock; normal and optimized Python must agree.
It is advisory only: occurrences require review or compilation, and do not
establish API breakage or theorem authority. No speculative additional Lean
changes. Full compiler qualification, historical workflow harvest, semantic
review and manual canonical admission remain required.

Use OPICA_R5_LOCKED_SOURCE_RECEIPT and existing run.sh modes on fresh stages.
Local Lean was unavailable at implementation; CI qualification is pending.
No automatic claim promotion or closure of the separate literal-energy route.
RH_OPEN.
