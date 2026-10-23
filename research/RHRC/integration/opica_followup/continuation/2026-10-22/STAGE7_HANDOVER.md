# Stage 7: the renormalized co-Poisson construction (R1-CP1)

This stage starts from PR #294 head `3a9dd319107e662ccb825c49949081806610bb9c` (Stage 6).
The source commit checked here is `0d7158a3fcc8560cc3ae486fb255ed6763cf8c2a` (tree `306ff84b596926fd2573205c639ac7934dd5a77e`); exact hashes, commands and logs
are in [stage7 STATUS.json](evidence/current-codex/stage7/STATUS.json). All 100 original roots
and 28 acceptance units remain required. RH, Step 4 and the independent closing inequalities
remain OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment
status changed. The parent part of `RenormalizedCoPoisson.lean` (finite sums, first-cell sign
root) is byte-identical apart from two docstring lines; the file keeps its CRLF line endings.
The only import change is `import Zeta23.OPICAFollowup.DilatedComb`, which is exactly the
`direct_project_imports` entry of this module in BUILD_MANIFEST. No Mathlib import changed.
All six definitions BUILD_MANIFEST requires of the module now exist: `renormalizedCombKernel`,
`coPoissonFamily`, `coPoissonCutoff`, `finiteSumSrho`, `normalizationBrho`, `zeroMeasure`.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `renormalized_copoisson_tempered_family` (R1-CP1) | K_t = A_t + F A_t = D_t + D_(-t) - e^(t/2)(delta_0 + dx) on Schwartz tests; \|<A_t, phi>\| <= 2 zeta(k) p_k(phi) e^((1/2-k)t) for every real t and k >= 2; V_lam = int_0^oo e^(-lam t) K_t dt is a tempered distribution for every complex lam, lam -> V_lam(phi) is entire for every test, and every K_t and V_lam is Fourier self-dual and even. | [ExpectedCoPoissonFamily.lean](consumers/ExpectedCoPoissonFamily.lean) (7 receipts) |
| `renormalized_copoisson_order_zero` (R1-CP1) | On 0 < Re rho < 1 the actual cutoffs int_0^T e^(-(rho-1/2)t) K_t dt are the locally finite complex measures r_T dx + ((1 - e^(-rho T))/rho) delta_0 on every Schwartz test; they converge in local total variation (genuine complex variation on every compact window, origin atom included) to rho^-1 delta_0 + [S_rho(\|x\|) + zeta(rho)\|x\|^(rho-1) + (1-rho)^-1] dx, both as T -> oo and in the parent `LocalVariationConvergence`; V_(rho-1/2) equals that measure on every Schwartz test. | [ExpectedCoPoissonOrderZero.lean](consumers/ExpectedCoPoissonOrderZero.lean) (10 receipts) |
| `zero_measure_exact_properties` (R1-CP1) | For every actual zero zeta(rho) = 0, 0 < Re rho < 1, rho != 1/2: the normalized measure (S_rho(\|x\|)/b_rho) dx - sum_(n!=0) delta_n is (CP1.7)/b_rho on every Schwartz test, has linear variation growth, canonical Fourier self-duality, even Jordan parts, the exact open unit gap, zero origin atom and atom -1 at 1; its real part eta_rho has the corresponding real properties and is nonzero. | [ExpectedZeroMeasure.lean](consumers/ExpectedZeroMeasure.lean) (7 receipts) |

With the Stage 1 first-cell sign root, all four R1-CP1 roots in BUILD_SPEC now have narrow
gates. Aggregate acceptance of the unit remains OPEN.

**Recorded formalization choices (no premise added, no domain narrowed).**

- "Entire tempered-distribution-valued family": every V_lam is a tempered distribution and
  lam -> V_lam(phi) is entire for every Schwartz test (testwise holomorphy, the standard weak
  notion). The family is defined for all complex lam with no premise.
- The cutoff is the interval integral int_0^T (T >= 0). Local TV convergence is stated for the
  real cutoff parameter and, as a consequence, in the parent sequential notion. The limit
  measure takes the hypothesis 0 < Re rho as an argument (it is needed for local
  integrability of \|x\|^(rho-1)). The identification of V_(rho-1/2) with the limit measure on
  all Schwartz tests goes beyond the contract and is what makes the zero-measure root bind to
  the actual family.
- zeta(rho) enters only through the Euler-Maclaurin form of the partial sums (CP1.6) from the
  parent PNT+ port (`Zeta0EqZeta`, `ZetaBnd_aux1b`). No divergent Dirichlet series and no
  functional equation is used.
- The normalized measure is (CP1.7) divided by b_rho = (1-2rho)/kappa = 1/rho - 1/(1-rho),
  kappa = rho(1-rho). It is built with explicit canonical Jordan pairs (positive/negative parts
  of Re and Im of the parent `coPoissonComplexDensity`; the punctured lattice is the comb D_0
  restricted to the complement of 0), so the paper's f_rho is the parent `coPoissonRealDensity`.
- Exact unit gap: `variationControl (Ioo (-1) 1) = 0` (all four Jordan parts vanish), with the
  atoms at +-1 showing that the gap cannot be enlarged. Evenness: `Measure.map neg` fixes every
  Jordan part. Real-part self-duality is proved from evenness and conj(F phi) = F(conj phi o (-.)),
  as in the paper.

New supporting results (generic, reusable): `densityAtomMeasure` with its compact-restriction
value, variation bound and Schwartz pairing; `family_pairing`, the lattice-ray change of
variables with both term-by-term integrations; `partialZeta_error` (CP1.6 with an explicit
constant, real X >= 1); the uniform bound S_rho = O_rho(1); `puncturedLattice` with evenness,
gap, atom and growth; `map_neg_withDensity_even`; `complexSchwartzConj_fourier`;
`rePart_fourierSelfdual_of_complex` (an even self-dual complex measure has a self-dual real
part).

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for all nine modules and
fourteen consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged.
Seventeen negative controls are rejected for their intended reasons:

- tempered family (5): kernel sign; missing origin atom; decay rate e^(-kt); anti-self-duality;
  constant zeta(k);
- order zero (6): origin coefficient 1/(1-rho); missing zeta(rho)\|x\|^(rho-1) term; closed strip
  Re rho <= 1; cutoff atom (1+e^(-rho T))/rho; A_t-only synthetic cutoff; parameter lam = rho;
- zero measure (6): self-duality without zeta(rho) = 0; atom +1 at 1; b_rho = 1/rho + 1/(1-rho);
  rho = 1/2 allowed; gap (-2, 2); missing b_rho D_0 correction.

The ledger now records 41 historical, 25 narrow and 34 absent roots. This is not aggregate
acceptance of 66 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The three roots above with their exact premises
   and the supporting results listed. All receipts are standard-only. The consumer
   `expected_real_part_H1_hypotheses` checks eta_rho against the parent H1 predicates
   `HasUnitGap`, `FourierSelfdual` and `HasLinearGrowth`. `expected_not_offlattice_nonnegative`
   proves that for every rho = 1/2 + delta + i gamma with \|gamma\| > 3 pi/(2 log 2) the negative
   part of eta_rho has positive mass on an open subinterval of (1, 2). It needs no zero
   hypothesis.
2. **Workflow harvest at `3a9dd319`** ([ci-harvest-3a9dd319.json](evidence/current-codex/stage7/ci-harvest-3a9dd319.json)).
   - **OPICA follow-up** (PR run 39943419462 and push run 39943410491): preparation,
     exact-source subset, narrow candidates (including the new ExpectedWeightedInverse) and
     frozen regression PASS. Full release readiness FAIL, as designed.
   - **Parent and RHRC checks:** parent `opica-contract` and `opica-component-summary` FAIL,
     the same as at earlier heads; `opica-formal` and `opica-dependency-delta` are skipped.
     `python-rhrc` FAIL, and `rhkg-compiler-receipt` FAIL at the canonical-state validation, both
     pre-existing. `lean` and `r003-normalization-audit` PASS.
   - **Inherited research replays:** all PASS, including the post-284 campaign (completed
     12:42Z). They create no OPICA theorem authority.
3. **What changed.** R1-CP1 is complete at narrow level. The construction is now an actual
   measure, not only a distribution:
   - the cutoff identification is a change of variables x = (n+1) e^(+-t) along every lattice
     ray, with term-by-term integration justified on both sides;
   - local TV convergence uses the genuine complex variation through the Stage 6 tools
     (`variation_le_of_forall_enorm_le`);
   - the identification of V_lam on all Schwartz tests needs an explicit majorant
     C(\|x\|^(sigma-1) + 1 + x^2) valid uniformly in T.
4. **Upstream.**
   - DERIVED (informal): CP1.6 applied to both finite sums gives
     R_rho(y) = 1/rho + zeta(1-rho) y^(-rho) + O_rho(1/y) as y -> oo, while near 0 the density
     is zeta(rho)\|x\|^(rho-1) + 1/(1-rho) (formal: `expected_limit_density_near_origin`).
     V_lam is self-dual by Poisson summation alone. Fourier duality between the singular
     profile at 0 and the tail at oo is the classical functional-equation mechanism.
   - PROVED: at a zero the singular term vanishes and R_rho = S_rho + 1/(1-rho) is bounded on
     compacts.
   - DERIVED: since S_rho = 0 on (-1, 1) and sigma < 1, zeta(rho) = 0 iff the order-zero
     measure V_(rho-1/2) has a bounded density near the origin.
5. **Downstream.**
   - The normalized zero measure now exists as an actual object with all its exact properties.
     It is what `copoisson_zero_jets_measures` (R2-H1) differentiates in rho and what
     `actual_zero_measure_span_consumer` combines.
   - DERIVED (informal; also uses zeta(1-rho) = 0 at a nontrivial zero, from the functional
     equation): S_rho - b_rho = O(1/y) at zeros. This is the first-order form of the
     `zero_profile_tail_and_jumps` statement h = kappa B2({x})/(2x^2) + O(x^-3).
   - `partialZeta_error` is the first-order step of `finite_sum_euler_maclaurin_uniform`.
6. **Resurrected routes.**
   - Stage 6 recorded that below the HT1 threshold a < 1/2 any statement needs a renormalized
     mixture. CP1 is exactly that regime: V_lam mixes the renormalized combs K_t with the
     weight e^(-lam t) 1_(t>0), and \|Re lam\| < 1/2 violates the HT1 moment condition.
   - The Stage 6 complex-variation tools carried over unchanged.
7. **New RH-relevant clue (LEAD/HYPOTHESIS, not formal).**
   - DERIVED (formal modulo the existence of a zero, not formalized in Mathlib): eta_rho is
     linearly growing, Fourier self-dual and has the exact unit gap and zero origin atom, but it
     is not a multiple of the comb, since its first-cell density is nonzero. So the HT1
     sharp-gap rigidity "self-dual + gap => c Sha" genuinely fails below the a > 1/2 moment
     threshold. The threshold in `weighted_mixture_sharp_gap` cannot be removed, and
     zero-generated measures sit exactly in the excluded regime.
   - LEAD: H1 needs off-lattice nonnegativity in addition to the gap. For
     \|gamma\| > 3 pi/(2 log 2) approx 6.8 that fails (formal, consumer). Every known zero has
     \|gamma\| > 14 (numerical fact, not formalized), so this positivity target fails for all
     known zeros on and off the line and cannot separate them, as the paper states.
8. **Falsification checks.**
   - Vacuity: the construction-level clauses (growth, gap, atom) are exercised at rho = 3/4,
     where zeta(rho) != 0. Order zero is exercised at rho = 1/2. Only self-duality of the
     normalized measure uses zeta(rho) = 0, and a negative control shows that clause cannot be
     applied without it.
   - Boundary T = 0 (by inspection of the definitions): the cutoff density and atom vanish
     almost everywhere, consistent with int_0^0 = 0.
   - Parameter: lam = rho is rejected; the strip cannot be closed at Re rho = 1.
   - Circularity: zeta enters only through the parent Euler-Maclaurin identity, self-duality
     only through Poisson summation (`dilated_comb_fourier`), and the zero hypothesis only in
     the (CP1.7) cancellation of the zeta(rho)\|x\|^(rho-1) term.
9. **Highest-leverage next moves.**
   - `ProfileEulerMaclaurin.finite_sum_euler_maclaurin_uniform`: the second-order upgrade of
     `partialZeta_error`. It then feeds `ZeroProfiles` (regular self-dual profile, tail and
     jumps) and `ForcedEuler`.
   - `CoPoissonJets.copoisson_zero_jets_measures`: rho-derivatives of the now explicit densities
     and atoms.
   - In parallel: `LogFourierSobolev`, J5.2/MS1 and R2-S3, where the complex-variation and
     density-plus-atom tools transfer.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 7 and carries older counts; README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 7 head, the 34 absent roots, RH, Step 4 and the
independent closing inequalities.
