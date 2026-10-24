# Stage 4: compiling W06/W07 sources, CT1 family and word/jet consumer

This stage starts from PR #294 head `40fd51b541f9be19fa0ffd56441c8217a36ddabf`
(tree `90091089ec0e6fe6a221cc2c27f1d95d675a7ab1`). The source commit checked here is
`f8f5f427ec94598984a9d0910cb5db60fc92b9ea` (tree `0692af9a960bfa26e67202f6b61c04a394e17ea3`);
exact hashes, commands and logs are in [stage4 STATUS.json](evidence/current-codex/stage4/STATUS.json).
All 100 original roots and 28 acceptance units remain required. RH, Step 4 and the
independent closing inequalities remain OPEN. No frozen specification, PDF, parent
mathematical source or optional-amendment status changed.

## What was wrong at `40fd51b`

- `DilatedComb.lean` did not compile with the pinned Lean/Mathlib (4 errors from
  `d1777dab`). With that repaired, `NearGapLimits.lean` had 22 errors and
  `WeightedMixing.lean` 6. A missing `open scoped ENNReal` caused parse errors that left
  four proof bodies unelaborated. Three Stage 1/2 narrow roots in those files
  (`dilated_comb_fourier`, `near_gap_mass_bound`, `weighted_mixture_exists_fourier`) were
  therefore not compilable at the head, although their declaration text was unchanged.
- The CT1 workflow consumer named `Zeta23.OPICA.localSignedCompactRestriction`,
  `localJordanAdd` and `localJordanScale`; these are declared in `Zeta23.OPICAFollowup`.
- No OPICA Lean CI job completed after `9ccea78e`: runs #10–#157 were cancelled by the
  workflow's `cancel-in-progress` concurrency group as new commits arrived.
- `MODULE_STATUS.md` was stale (NativeWindowRate became present), so the preparation job
  failed and skipped the subset and frozen-regression jobs.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `dilation_near_gap_family` (R1-CT1) | For every 0 < L < log 2, the genuine canonical Jordan pair of D_L + D_(-L) - 2cosh(L/2) D_0 has: the compact signed three-comb identity, linear growth with common constant 18, canonical Fourier self-duality, Schwartz **and measure-level** evenness, the exact gap (-e^-L, e^-L) with 1/2 < e^-L < 1, negative part on the integers, zero origin atoms, nonzero positive part, and the paper's gap-edge atom of exact mass e^(-L/2) at e^-L. Twelve clauses; premises only restrict L. | 52 standard-only receipts in the W04/W07 consumer |
| `step123_word_jet_consumer` (R1-NB1, R2-J1) | The `e21cf553` multiplicity normalization compiles after the genuine parent `NativeJetAdapter` build (4,513 jobs). An independent 22-clause restatement (every `let` expanded) and an actual-domain consumer on outputs from `exists_eachPhase_cofinal_generatedStep123CompleteOutput` pass. | [ExpectedWordJet.lean](consumers/ExpectedWordJet.lean); 5 standard-only receipts |

The three Stage 1/2 roots above are re-verified on the committed source. The narrow
runner reports `PASS_NARROW_ONLY` with a clean tree for all nine modules and eight
consumer files. Negative controls (wrong atom mass, wider gap, wrong pole order) are
rejected. The ledger now records 41 historical, 17 narrow and 42 absent roots. This is
not aggregate acceptance of 58 roots.

New general supporting result: `jordan_even_of_selfdual`. Every linearly growing,
Fourier-self-dual Jordan pair has reflection-invariant Jordan parts (𝓕² is reflection,
and the parent `parts_eq_of_distribution_eq` is faithful). Evenness therefore never has
to be assumed separately for self-dual measures in this class, as Amendment v1.1 §C
remarks.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above, with the exact
   premises stated; `jordan_even_of_selfdual`; `nearGapCombFamily_gap_edge_atom`.
2. **Workflow harvest.** At `40fd51b`: preparation FAIL (stale table); release readiness
   FAIL (expected); subset and frozen regression SKIPPED; narrow candidates queued and
   bound to fail at DilatedComb; `python-rhrc` FAIL because the parent OPICA validator
   rejects the incomplete child extension (fail-closed by design); the inherited Lean and
   research replays that completed were green and create no new theorem authority.
   Locally at `f8f5f42`: child suite 185/185 and parent contract tests 82/82 in both
   Python modes; frozen replay 39,920 exact controls per mode; three numerical suites
   CONSISTENCY_ONLY.
3. **What changed.** CT1 gained measure-level evenness and the paper's exact e^-L witness.
   The e^L witness used earlier is not robust: its atom gains mass at L = ½log 2 and
   ½log 3 and cancels to 0 at L = log 2. The e^-L atom is exactly e^(-L/2) on all of
   0 < L ≤ log 2.
4. **Upstream.** The H1/HT2 "even" hypotheses are implied by self-duality. The evenness
   clauses of `zero_measure_exact_properties` and `copoisson_zero_jets_measures` can reuse
   `jordan_even_of_selfdual` once those measures have linear growth and self-duality.
5. **Downstream.** `near_gap_mass_bound` now has an actual nonzero instance
   (`nearGapCombFamily_offinteger_mass_budget`), and its off-integer budget vanishes like
   1 - e^-L. HT2 and the CT1 normalized limit are next in this module.
6. **Revived route (LEAD, not formal).** A compactness-free HT2 proof. Translating the
   regularized triangle in the parent Gaussian argument should give, for every integer j,
   ∫Δ(ξ-j)dν = ∫e^(2πijx)s(x)dν(x), hence |∫Δ(·-j)dν| ≤ (1-a)|ν|([-1,1]) uniformly in j.
   Piecewise-linear interpolation at the integers plus the mass bound and uniform
   Schwartz tails then give ν(φ) = O_φ(C(1-a)^(1/5)). The contract text prescribes
   compact-limit extraction, so adopting this route needs an explicit recorded refinement.
7. **Clue (HYPOTHESIS).** For any self-dual linear-growth ν, the tent-localized lattice
   masses (Δ*ν)(j) equal the integer Fourier coefficients of the periodized finite measure
   s·ν, without positivity. This may give a countable test family for the C3 duality
   defect. The decisive risk is that it repackages the original high-mask observation.
8. **Falsification so far.** The modulated bound is consistent with CT1 at j = 0
   (2(r-1)/r^(3/2) ≈ 2L) and j = 1 (2sinh(L/2) - 2sinh(3L/2) ≈ -2L) against a bound of
   ≈ 6L. CT1 caps the possible Schwartz-test exponent at 2, so the true worst case lies in
   [1/5, 2].
9. **Highest-leverage next moves.** One uncancelled CI run on this head; then the HT2
   controlled limit and the CT1 normalized limit; then `ProfileEulerMaclaurin`,
   `LogFourierSobolev` and the three CP1 roots, which gate 31 of the 42 absent roots;
   J5.2/MS1 and the W06 inverse in parallel.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration, the full
workflow harvest on an exact head, the 42 absent roots, RH, Step 4 and the independent
closing inequalities.
