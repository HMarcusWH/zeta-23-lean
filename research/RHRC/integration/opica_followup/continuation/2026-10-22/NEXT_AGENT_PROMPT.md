> Current checkpoint: [Stage21](STAGE21_HANDOVER.md), checked code `139c1a0d88cc0fb2d8a0d8ea71e152b25b14c36e`, tree `3e63b0c72fc04da7bab45388d6096e82e95c4acb`. Ledger:41 historical +59 narrow +0 absent bodies; this is not original-contract/aggregate acceptance. Fresh physical/interface findings and all release obligations remain OPEN. Earlier stage statements below retain their historical scope.

# Task: finish the original 100-root OPICA follow-up

Continue the PR #294 checkout on branch `research/opica-native-followup`. Do not merge the PR,
create another PR or rewrite protected parent sources. Read root AGENTS.md, this directory's README,
ROOT_LEDGER_100.json, the latest [STAGE21_HANDOVER.md](STAGE21_HANDOVER.md) and the unchanged
controlling specifications: PUBLIC_ROOTS.json, BUILD_SPEC.md, BUILD_MANIFEST.json and
PAPER_CROSSWALK.json two directories up, and the paper under `paper/`.

The requested outcome is all 100 original roots and 28 acceptance units. Do not narrow a theorem,
invent an assumption, substitute an optional lemma or omit a physical/domain acceptance requirement.
RH, Step 4 and the independent closing inequalities remain OPEN.

## State at handoff (2026-10-24)

- **Checked code checkpoint.** `9a8b2a4baee49f2056c7945b1544a7bc2893735b`, tree `6aa53d22d50d2aa24046d73b128c64a1d262f7f3` (Stage 20).
  Reconcile the live head before editing; later record commits do not inherit a new compiler receipt.
  Lean v4.33.0-rc2 and Mathlib `51e6992e` remain pinned; never run `lake update`.
- **Ledger.** 41 historical, 56 narrow (`PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`) and 3 absent
  roots. Narrow gates are not aggregate acceptance. The full-release gate correctly reports
  FAIL_RELEASE_INCOMPLETE.
- **Stage 19.** The original `actual_force_sampling_consumer` is verified at narrow gates, with
  ExpectedForceSampling and its actual-domain audits. ExpectedWordJet revalidates the existing
  primary at the changed Consumers source hash. ExpectedSampleSign proves supporting sign
  restrictions and does not add a primary root. Read the Stage 19 handover and STATUS.
- **Retained previous sessions (Stages 15 to 18).**
  - NativeResolvent (F2, three roots).
  - SquareDefect (R2-S3, four roots).
  - BoundaryAmplitude (F3, two roots).
  - CoPoissonJets (R2-H1, `copoisson_zero_jets_measures`). This module also holds reusable
    infrastructure: holomorphic parametric integrals (`iteratedDeriv_integral_entire`,
    `hasDerivAt_integral_of_closedBall`), the local inverse ρ(κ), multiplicity and order lemmas,
    the entire κ-family density and the jet measures.
- **CI and source authority.** The Stage 19 STATUS records the checked code commit/tree and
  narrow gates, and links the bounded workflow harvest. Inspect every exact run/job disposition.
  Companion PR evidence cannot pass a queued push job; pending, skipped, cancelled and failed
  work remains explicit. Earlier source-head replays confer no new code-commit CI authority.
  - **First action:** reconcile every run and job on the newest pushed head before changing proofs.
  - The designed red gates remain Full release readiness (PR and push), opica-contract,
    opica-component-summary, python-rhrc and rhkg-compiler-receipt.
- **How to produce a stage.** Follow [tools/stage_record/README.md](tools/stage_record/README.md),
  which documents the exact pipeline and includes the Stage 18 scripts.

## The 3 absent roots, in a workable order

1. `FiniteSpanSeparation.finite_zero_span_positive_only_zero`: every actual finite real combination nonnegative off the integer lattice is zero, and coordinates vanish on every specified independent actual real basis. Derive all measure/growth/selfdual/gap premises internally.
2. `FiniteSpanSeparation.fixed_basis_negative_mass_budget`: for each fixed independent actual real basis, prove a strictly positive constant times the coefficient Euclidean norm is bounded by global sinc-weighted negative mass. No uniform collision/growing-set constant.
3. `Consumers.actual_zero_measure_span_consumer`: instantiate actual zero profiles and all separator premises; do not assume measure status or the desired conclusion in a packet.

Stage 20 closes full H2a actual jet independence, J5.2/MS1 continuous actual-source window rates and both physical rate/conditional quietness consumers. The quiet antecedent remains OPEN; its independent audit proves it equivalent to Θ=0 for these complete observations.

Then complete the release:
- aggregate current-source export;
- full100 receipt production, replay and review seal;
- facade and registration;
- parent-extension wrapper;
- canonical regeneration (`rhkg-compiler-receipt`);
- every required exact-head workflow.

## Lessons that cost time

- Do not `open scoped Nat`: it makes `φ` a token (totient). Use `.factorial`.
- Inside `namespace Zeta23.OPICAFollowup`, `riemannZeta_conj` resolves to the project lemma that needs
  s ≠ 1. Mathlib's hypothesis-free version is `_root_.riemannZeta_conj`.
- Check every new top-level name for clashes before installing. Several obvious names already exist,
  for example `analyticAt_riemannZeta` and `zetaReflectionFactor`.
- `rw` fails on terms with dependent proof fields; use `simp only`.
- For `iteratedDeriv` of `fun` forms use the `iteratedDeriv_fun_add`/`_sub`/`_mul` lemmas.
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` takes a neighbourhood `s ∈ 𝓝 x₀`.
- Useful analytic-order lemmas: `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`,
  `analyticOrderAt_comp_of_deriv_ne_zero` and `analyticOrderAt_mul`.
- `validate_contract.py` requires `--output`.
- A stray, harmless `/pre14.json` exists outside the repository (an earlier preflight output; a
  safety check blocked deleting it).

## Standing rules

- Record exact head, tree, source hashes, compiler, commands, exit codes, logs and transitive axioms.
- Never count a stale object as compilation of modified source. Keep preparation,
  narrow/subset evidence and full-release readiness separate. Never disable or relabel a red
  full-scope gate, and never report pending, skipped or cancelled results as passes.
- Preserve frozen originals; record refinements explicitly in handovers and the ledger. Do not count
  helper declarations as primary roots.
- After each meaningful green result, perform the Post-Green Research Pass and deliver all nine items
  required by AGENTS.md. Use PROVED, DERIVED, LEAD/HYPOTHESIS, EXPERIMENTAL SIGNAL and OPEN
  accurately.
- The Post-Green Amendment remains supporting research, with the C3 unrestricted-inequality issue
  preserved, unless an explicit versioned promotion says otherwise.
