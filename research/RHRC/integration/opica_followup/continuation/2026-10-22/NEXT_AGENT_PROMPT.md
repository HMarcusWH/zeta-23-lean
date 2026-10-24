# Task: finish the original 100-root OPICA follow-up

Continue the PR #294 checkout on branch `research/opica-native-followup`. Do not merge the PR,
create another PR or rewrite protected parent sources. Read root AGENTS.md, this directory's README,
ROOT_LEDGER_100.json, the latest [STAGE18_HANDOVER.md](STAGE18_HANDOVER.md) and the unchanged
controlling specifications: PUBLIC_ROOTS.json, BUILD_SPEC.md, BUILD_MANIFEST.json and
PAPER_CROSSWALK.json two directories up, and the paper under `paper/`.

The requested outcome is all 100 original roots and 28 acceptance units. Do not narrow a theorem,
invent an assumption, substitute an optional lemma or omit a physical/domain acceptance requirement.
RH, Step 4 and the independent closing inequalities remain OPEN.

## State at handoff (2026-10-24)

- **Head.** `7360d44a` (Stage 18 record). Lean v4.33.0-rc2 and Mathlib `51e6992e` are pinned; never
  run `lake update`.
- **Ledger.** 41 historical, 49 narrow (`PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`) and 10 absent
  roots. Narrow gates are not aggregate acceptance. The full-release gate correctly reports
  FAIL_RELEASE_INCOMPLETE.
- **Done this session (Stages 15 to 18).**
  - NativeResolvent (F2, three roots).
  - SquareDefect (R2-S3, four roots).
  - BoundaryAmplitude (F3, two roots).
  - CoPoissonJets (R2-H1, `copoisson_zero_jets_measures`). This module also holds reusable
    infrastructure: holomorphic parametric integrals (`iteratedDeriv_integral_entire`,
    `hasDerivAt_integral_of_closedBall`), the local inverse ρ(κ), multiplicity and order lemmas,
    the entire κ-family density and the jet measures.
- **CI.** On `c6ce649d`, 19 of 22 runs were green apart from the designed fail-closed gates (Stage 17
  partial harvest). CI on `02c0ce8f` and `ff7b7c70` was superseded by later pushes. CI on `7360d44a`
  was in progress at handoff.
  - **First action:** harvest every run and job on the newest pushed head into the next stage record.
  - The designed red gates are: Full release readiness (PR and push), opica-contract,
    opica-component-summary, python-rhrc and rhkg-compiler-receipt.
- **How to produce a stage.** Follow [tools/stage_record/README.md](tools/stage_record/README.md),
  which documents the exact pipeline and includes the Stage 18 scripts.

## The 10 absent roots, in a workable order

1. **`Consumers.actual_force_sampling_consumer`** (F1-F3). A compiled draft is in
   [drafts/](drafts/README.md). Install it into `Zeta23/OPICAFollowup/Consumers.lean` with
   `import Zeta23.OPICAFollowup.BoundaryAmplitude` and re-verify the W01 word/jet consumer there.
2. **`ConfluentProfiles`** (R2-H2a): `profile_jet_confluent_determinant` and
   `finite_zero_jet_independent`. Required definitions: `profileJetMatrix`, `distinctSpectralNodes`.
   Imports only CoPoissonJets.
   - On the first cell 1 < x < 2, with u = log x, the jet density is
     e^(-u/2) (1/k!) ∂_κ^k [κ Sh(1/4 - κ, u)]. Its odd Taylor coefficients are
     (1/k!) ∂_κ^k [κ (1/4 - κ)ⁿ] at the nodes, for 0 ≤ n < M.
   - Paper (H2.3): det = (-1)^(M(M-1)/2) ∏ κ_j^(m_j) ∏_(i<j) (κ_j - κ_i)^(m_i m_j), with columns
     (j,0..m_j-1).
   - Proof route:
     - a triangular change between monomials and (1/4 - κ)ⁿ gives the sign;
     - the normalized confluent Vandermonde determinant needs a proof (Mathlib has only
       `Matrix.det_vandermonde`);
     - multiplication by κ on each jet block contributes κ_j^(m_j).
   - Nodes are κ values: ρ and 1 - ρ are one node (Stage 18 proves equal jets). κ ≠ 0 in the strip.
   - For independence, a vanishing combination has vanishing first-cell density. Its Taylor data
     then vanish, so the coefficients vanish.
3. **`FiniteSpanSeparation`** (R2-H2b): `finite_zero_span_positive_only_zero` and
   `fixed_basis_negative_mass_budget`. Required definition: `zeroJetRealSpan`. Imports
   ConfluentProfiles and `Zeta23.OPICA.SignedHeatSeparator`.
   - Use `signed_sharp_gap_separator` (needs HasLinearGrowth, FourierSelfdual, HasUnitGap and
     OffLatticeNonnegative of a `LocallyFiniteSignedMeasure`).
   - Use `signed_gap_negative_weighted_mass_budget` for the sinc² weight.
   - Real combinations pair conjugate nodes. Stage 18 gives the conjugate relation and real-part
     self-duality.
   - The budget constant comes from compactness of the unit sphere for a fixed basis; there is no
     uniform constant.
4. **`NativeWindowRate.native_fixed_source_window_rate`** (J5.2). The file contains supporting
   definitions only (`nativeWindowEnergy` and boundary lemmas). The multiplicity-tail lower bound
   must be combined with uniform source costs, the old-memory estimate and the matching upper rate,
   for every fixed d ≥ 0 and C > 1, including Θ = 0 and arbitrary multiplicity. See the J5 lane in the
   earlier handovers.
5. **`MovingSourceWindowRate.native_slow_source_window_rate`** (MS1), after item 4.
6. **The remaining `Consumers` roots.**
   - `fixed_two_factor_mask_rate_theta` needs J5.2.
   - `quiet_balanced_observation_implies_native_cut` is explicitly conditional. Keep the zero-rate
     upper bound as an open antecedent; it is never an unconditional RH root.
   - `actual_zero_measure_span_consumer` needs H1 and H2b.

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
