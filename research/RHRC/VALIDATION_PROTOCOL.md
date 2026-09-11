# RHRC validation protocol

> **Claim firewall: RH remains OPEN.**

This document defines what "green", "proved", "validated" and "promoted" mean in this repository.

## Exact object first

For every theorem-bearing PR record the base, PR head, exact object checked by GitHub Actions, theorem tree, eventual merged-main commit/tree, and Lean version where relevant.

For control-only PRs record the exact control head/merge tree separately from the last theorem-bearing anchor. A control-only green must not advance theorem authority.

Compiler validity attaches only to the exact object actually checked.

## Authoritative repository gates

Current theorem/claim gates include:

```text
python research/RHRC/tools/run_suite.py
R003 normalization audit / dictionary guards / source-normalization firewall
R004 scalar-shift invariant audit
external-reference dependency firewall
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden sorry / project axiom scan
Permansson independent formal verification
```

A skipped downstream step is not a passed gate.

`run_suite.py` also executes FFBBP and Control-v2 regression tests. These tests guard research-control semantics; they do not grant theorem authority to FFBBP or Control v2.

## Current theorem/control validation anchors

```text
theorem-state anchor = PR #148 merge fcd301ae4c1b58196ff7fca18128243f1d35a87b
validated theorem head = 77c2d14511004ba380b080e08b4943b267ebd863
validated theorem tree = 91d537ee64b8f613bebdcf12110deba486276d35
RHRC #930 / run 34619665717 = SUCCESS
Permansson #703 / run 34619665725 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
```

The #148 validated theorem head and merged main have the same tree `91d537ee...`. PR #117 remains the latest Control-v2 semantic authority because #148 changes mathematical state, not the controller capability/authority model.

## Exact #148 gate evidence

At validated theorem head `77c2d14511004ba380b080e08b4943b267ebd863`, RHRC workflow run #930 (`34619665717`) completed successfully.

Its jobs completed successfully, including:

```text
python-rhrc
r003-normalization-audit
lean
```

The `lean` job successfully ran:

```text
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
forbidden placeholder/project-axiom scan
```

Permansson workflow run #703 (`34619665725`) also completed successfully on the same theorem head.

## What #144-#148 validate

### PR #144

The exact frozen production source/predecessor and logarithmic-cover infrastructure is in the validated `Zeta23.CCM` build closure. Headline theorem objects include:

```text
frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell
frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
frozenIntrinsicPredecessorBlock_eq_actual_fixedCell
frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder
intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
complexFrozenIntrinsicPredecessorRemainder_ofReal
liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell
```

These validate exact algebraic continuation objects, real/complex production bridges and deck identities. They do **not** validate complex differentiability/analyticity of the full parameter-dependent frozen remainder.

### PR #145-#146

`CanonicalApertureHolomorphy.lean` validates the removable scalar factor/remainder at zero and exact equality with the production complex scalar/remainder away from zero, plus positive-real production provenance.

The proof explicitly handles nonzero periodic zeros of the divided exponential slope rather than assuming a global-entire quotient.

### PR #148

The #148 modules are imported through `Zeta23.CCM` and therefore lie in the validated aggregate build closure.

Validated theorem authority includes:

```text
complexArchSafeStrip
isOpen_complexArchSafeStrip
convex_complexArchSafeStrip
isPreconnected_complexArchSafeStrip
isConnected_complexArchSafeStrip
ofReal_mem_complexArchSafeStrip
mul_Icc_mem_complexArchSafeStrip
complexArchSinhSlope_ne_zero_of_mem_strip
differentiableOn_complexRegularizedArchScale_strip
analyticOnNhd_complexRegularizedArchScale_strip
differentiableAt_complexAlphaCore_of_mem_strip
differentiableOn_complexAlphaCore_strip
analyticOnNhd_complexAlphaCore_strip
differentiableAt_complexBetaCore_of_mem_strip
differentiableOn_complexBetaCore_strip
analyticOnNhd_complexBetaCore_strip
differentiableAt_complexGammaCore_of_mem_strip
differentiableOn_complexGammaCore_strip
analyticOnNhd_complexGammaCore_strip
```

The parameter-core theorems are genuine differentiation-under-the-integral results on a fixed interval with local compact domination.

The current theorem surface does **not** validate:

```text
holomorphy of the full production scalar branch on the common source domain
pole-channel denominator zero-freeness / holomorphy on the common source domain
holomorphy of complexFrozenCanonicalSourceRemainder
holomorphy of complexFrozenIntrinsicPredecessorRemainder
holomorphy of the lifted predecessor on a connected cover domain
holomorphy/nonidentity of the relevant determinant
dense regular apertures on the physical cutoff cell
production cell-minimal regular first-bad selection
regular canonical Schur-energy nonnegativity
negative-root exclusion
outside-strip/trivial-zero terminal seam
RH
```

## Import/build closure law

A `.lean` file existing in the repository, appearing in a PR, passing the no-placeholder scan, or being merged does **not** establish that its declarations elaborate.

A declaration is compiler-validated project theorem authority only if its module lies in the transitive import closure of an exact successful authoritative build, or the module itself was explicitly built by an authoritative successful gate.

PR #103 remains the canonical historical example: `ConstrainedParityGeometry.lean` was imported by `Zeta23.CCM` and compiled; `ParityBadness.lean` was merged but not imported and remained staged source until a later build closure consumed it.

Current example: the #148 `CanonicalApertureArchDomain` and `CanonicalApertureParameterHolomorphy` modules are imported through `Zeta23.CCM` and therefore lie in the validated #148 build closure.

## Axiom inspection

For production-promoted R003 bindings, `ClaimBindings.lean` must contain exact

```lean
#check <theorem>
#print axioms <theorem>
```

The accepted production foundation is `[propext, Classical.choice, Quot.sound]`. No production theorem may depend on `sorryAx` or a promoted project axiom.

Supporting theorem modules may also carry module-local `#print axioms` checks without thereby becoming machine-promoted claims. The #148 modules print axioms for their headline analytic declarations; this does not itself promote them into `CLAIM_REGISTRY.json`.

## Proof versus promotion

For R003 `PROVED_UNCONDITIONAL`, exact theorem names must agree across:

```text
CLAIM_REGISTRY.json
R003_PROMOTED_BINDINGS.json
Zeta23/CCM/ClaimBindings.lean
```

`promoted_binding_lint.py` enforces set equality, theorem-name equality, and exact #check/#print-axioms presence.

Compiler-PROVED theorem authority beyond the current machine-promoted claim list must not be silently upgraded to `PROVED_UNCONDITIONAL` registry status. PR #148 is another example of theorem authority advancing without automatic machine-claim promotion.

## Control-v2 validation law

`research/RHRC/control_v2/` is diagnostic research infrastructure only. Its CI gates enforce:

- no theorem/claim/terminal-answer authority;
- separate theorem and control-plane anchors;
- deterministic route certificates and score diagnostics;
- deterministic retro receipt hashes;
- fail-closed missing retro-search / first-break requirements;
- dead-route revival records when explicitly required;
- `as_of` Git replay that cannot see future commits;
- external time-travel replay that requires availability metadata;
- retro receipts bound to their declared Git search paths;
- exact sorted contiguous finite-prefix coverage for deformation budgets;
- no `PRUNE` from a numeric tail without a passed horizon certificate targeting the remaining deformation budget;
- no decision-bearing reduced-model `PRUNE` without decision commutation when that gate is required;
- no promotion from diagnostic commutation to decision commutation;
- no horizon certificate from a small local residual alone.

A Control-v2 recommendation is **not** a theorem, claim promotion, RH evidence, or a substitute for Lean.

## Vocabulary

- **source present** — file exists.
- **module compiles** — Lean elaborated that module.
- **umbrella build green** — named target and transitive imports compiled.
- **PR green** — all required gates for the exact PR object succeeded.
- **PROVED** — exact statement compiler-validated with acceptable axiom surface.
- **PROVED_UNCONDITIONAL** — proved theorem additionally registered on the production claim surface.
- **DERIVED** — mathematical consequence not separately theorem-locked.
- **LOCAL LEAN CHECK** — standalone/local compilation evidence outside merged theorem authority.
- **LEAD / HYPOTHESIS** — motivated research route.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — not established.

## Post-green synchronization

After every meaningful green result: verify exact evidence; read the proof/control result; compare history; analyze upstream/downstream implications; revisit dead routes; falsify clues; then synchronize registries, active route README, research-lead deltas, `CURRENT_RESEARCH_PLAN`, `VALIDATION_PROTOCOL` and public summaries.

Historical settlements and provenance snapshots remain historical.

A post-green sync must not rewrite a large historical ledger merely to manufacture currentness when the documentation law permits a new dated delta to supersede it. In that case, the living README/plan/route/control documents must point to the new delta explicitly.

## Claim firewall

Green supporting mathematics, aperture freedom, fixed-cell continuity, witness persistence, frozen/log-cover continuation objects, local scalar analyticity, scalar production bridges, fixed-unit parameter holomorphy, regularity interfaces, source normalization, finite nesting, parity geometry, determinant reductions, research-control recommendations, budget diagnostics and numerical agreement are not RH.

**RH remains OPEN unless the exact terminal RH theorem passes the complete proof and claim-validation gates.**
