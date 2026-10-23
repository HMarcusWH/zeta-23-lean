# Stage 6: weighted Mobius inverse, noncompact sharp gap and exact gap leakage

This stage starts from PR #294 head `c0ab8aa2909381487e44bbc7df94016d0743612e` (Stage 5).
The source commit checked here is `068933fdd647d12395e99743866035e6c6f3e42a`
(tree `45a1815a51c57eea80852f90f15558165a9ec78d`); exact hashes, commands and logs are in
[stage6 STATUS.json](evidence/current-codex/stage6/STATUS.json). All 100 original roots and
28 acceptance units remain required. RH, Step 4 and the independent closing inequalities
remain OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment
status changed. The only import changes are Mathlib helpers in `WeightedMixing.lean`
(frozen revision, recorded in the source receipt as BUILD_SPEC requires):
`Mathlib.MeasureTheory.Group.Convolution`, `Mathlib.NumberTheory.ArithmeticFunction.Moebius`,
`Mathlib.NumberTheory.TsumDivisorsAntidiagonal`,
`Mathlib.NumberTheory.EulerProduct.DirichletLSeries` and
`Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `weighted_mobius_inverse` (R1-HT1) | For every complex mixer with exponential moment a > 1/2: eta = N * sigma for each Jordan coordinate of the actual mixture and in positive Jordan form; M+ * N = delta_0 + M- * N (the finite divisor identity); sigma = M_mu * eta for the real and imaginary parts in positive Jordan form; finiteness of every weighted norm; exact multiplicativity of the norm int e^(-a y) for the genuine product-measure convolution; norm of N = zeta(a+1/2); M+ and M- mutually singular, so M+ + M- is the variation of M_mu, with norm sum mu(n)^2 n^(-a-1/2) = zeta(a+1/2)/zeta(2a+1). | [ExpectedWeightedInverse.lean](consumers/ExpectedWeightedInverse.lean) |
| `weighted_mixture_sharp_gap` (R1-HT1) | Canonical Fourier self-duality of the actual mixture distribution and an empty punctured gap on (-1,1) force every mixing coordinate to be a multiple of delta_0, sigma to vanish off the origin and nu = c Sha with c the origin atom; a zero origin atom forces all coordinates, the distribution and the variation of nu to vanish. No positivity premise; strict a > 1/2. | same consumer; the actual delta_0 mixer satisfies both hypotheses |
| `weighted_gap_leakage` (R1-HT1) | (1) HT1.7 with the genuine complex variations: zeta(2a+1)/zeta(a+1/2) int_(-oo,0) e^(-a t) d\|sigma\| <= int_(0,1) x^(-a-1/2) d\|nu\|, plus the same bound per real Jordan part and for the coordinate control; (2) HT1.9 supremum form at the endpoint b with no b-moment; (3) finite a-moments for a < b; (4) an endpoint witness with infinite b-moment; (5) the paper's r_h is the actual positive-axis density of the mixture of h(t) dt. | same consumer; 17 standard-only receipts in total |

**Recorded formalization choices (no premise added, no domain narrowed).**

- Signed identities of the weighted algebra are stated in positive Jordan form. Every term
  has a finite weighted norm (proved), so the forms are equivalent to the signed identities.
  M_mu * N = delta_0 is written M+ * N = delta_0 + M- * N.
- The gap hypothesis nu|(-1,1)\{0} = 0 is `nu.variationControl (Ioo (-1) 1 \ {0}) = 0`, i.e.
  all four Jordan parts vanish there. This is equivalent to the vanishing of the restriction.
- HT1.9 is stated for the pointwise representative r_h, as in the paper. Clause (5) identifies
  r_h with the density of the actual coordinate mixtures (r_h = (D_0 - D_1) + i(D_2 - D_3)).
  The paper's further remarks r_h = O(x^(b-1/2)) and the affine-correction corollary are not
  part of the root contract and remain OPEN supporting work.

The first W06 commit (`4ab158b9`) proved the leakage bound only per Jordan part, a weaker
statement for complex mixers. It also proved r_h only as a formula and left the variation of
M_mu implicit. The paper's HT1.7, HT1.8 and HT1.5 require all three. `068933fd` therefore adds:

- the genuine complex-variation bound, by a new route (below);
- the actual-density identification, by the change of variables x = e^t n along each lattice
  ray;
- mutual singularity of M+ and M-.

Only after these were the three roots moved to narrow status.

New supporting results: `complexMeasure_rotation_variation_le` (a real rotation alpha Re + beta
Im with alpha^2 + beta^2 <= 1 has no larger variation), `complexIntegral_real_norm_le` (exact
\|int g dnu\| <= int g d\|nu\| for nonnegative bounded compactly supported g),
`positiveLogMeasure_complex_bound`, `moebius_complex_value_bound`, `complex_gap_leakage`,
`positiveDilationMixture_withDensity_apply`, `densityMixer`, `densityMixer_moment`,
`densityMixer_mixture_density`, `moebiusComb_mutuallySingular`, the lattice measure algebra
(`latticeMeasure_conv_latticeMeasure`, `tsum_lattice_pairs`) and
`tsum_abs_moebius_rpow` (sum mu(n)^2 n^(-s) = zeta(s)/zeta(2s)).

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for all nine modules and eleven
consumer files. The unchanged W04/W07 (52) and W06 (14) workflow consumers pass against the
new source. No other module imports `WeightedMixing`, so W01 and the exact-source subset are
unaffected. Eight negative controls are rejected for their intended reasons:

- inverted zeta ratio;
- missing M- * N term;
- missing self-duality;
- endpoint a = 1/2;
- zeta(a) in place of zeta(a+1/2);
- one-sided gap;
- density identification with decay b <= 1/2;
- M+ = M- claimed.

The ledger now records 41 historical, 22 narrow and 37 absent roots. This is not aggregate
acceptance of 63 roots. All five R1-HT1 roots in BUILD_SPEC now have narrow gates, but
aggregate acceptance of that unit remains OPEN.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The three roots above with their exact
   premises and all supporting results listed. All receipts are standard-only.
2. **Workflow harvest at `c0ab8aa2`** ([ci-harvest-c0ab8aa2.json](evidence/current-codex/stage6/ci-harvest-c0ab8aa2.json)).
   - **OPICA follow-up** (PR run 39909711474 and push run 39909706765): preparation,
     exact-source subset, narrow candidates and frozen regression PASS. In the narrow job the
     runner ran the two new Stage 5 consumers. Full release readiness FAIL, as designed.
   - **Parent and RHRC checks:** parent `opica-contract` and `opica-component-summary` FAIL,
     the same as at the two earlier heads; `opica-formal` and `opica-dependency-delta` are
     skipped. `python-rhrc` FAIL. `rhkg-compiler-receipt` FAIL at "Validate committed RHKG
     state BEFORE any generator writes", the same canonical-graph drift for unregistered child
     modules. `lean` and `r003-normalization-audit` PASS.
   - **Inherited research replays:** all PASS. They create no OPICA theorem authority.
   - The harvest file records the final disposition of every run, including the long post-284
     campaign.
3. **What changed.** R1-HT1 is complete at narrow level. The leakage is now the paper's
   statement with genuine complex variations. The new route avoids polar decompositions and
   complex convolution theory:
   - the variation of a compact restriction dominates every real rotation;
   - this gives the exact complex integral bound for positive weights;
   - the causal Mobius expansion then holds pointwise on bounded negative-axis sets.
4. **Upstream.** The weighted log norm is the Laplace transform at a. On lattice measures it
   is the Dirichlet series at s = a + 1/2. N corresponds to zeta(s), M_mu to 1/zeta(s) and
   the variation of M_mu to zeta(s)/zeta(2s). Exact multiplicativity is the Laplace
   homomorphism, and the noncompact inverse is the absolutely convergent Dirichlet inverse.
   The parent compact sharp gap (M0043) is extended to exactly the class where both sides
   converge absolutely. The variation tools are generic and apply to any
   `LocallyFiniteComplexMeasure`.
5. **Downstream.**
   - DERIVED: the leakage constant zeta(2s)/zeta(s), s = a + 1/2, equals the Liouville series
     sum lambda(n) n^(-s). As a -> 1/2+, it behaves like (pi^2/6)(a - 1/2), from the simple
     pole of zeta at 1. Leakage per unit of negative-axis mass therefore degenerates linearly
     at the threshold.
   - PROVED (consumer): the restriction to negative logarithmic support is necessary. The
     delta_0 mixer violates the unrestricted inequality.
   - The genuine-variation tools apply directly to the remaining complex-measure roots (CP1
     heat measures, R2-S3 duality defects).
6. **Resurrected routes.** The Stage 2 note "compact-support proof is not enough" is now met by
   a fully noncompact inverse; no compact support is used. The per-part leakage of `4ab158b9`
   is retained as additional clauses.
7. **New RH-relevant clue (LEAD/HYPOTHESIS, not formal).** The HT1 domain boundary a = 1/2 maps
   to s = 1 under s = a + 1/2, where two things fail at once. The mixture loses its e^(t/2)
   moment, and the Mobius inverse leaves the absolutely convergent algebra (sum mu(n)^2 n^(-s)
   has a pole at s = 1). For a in (0, 1/2], a causal inverse of the same form would need
   sum mu(n) n^(-s), or sum lambda(n) n^(-s), to converge for s in (1/2, 1]. Convergence of
   either for all Re s > 1/2 is equivalent to RH (Littlewood).
   - So the paper's scope limit ("critical or slowly decaying, conditionally defined, or
     renormalized distributions are not covered") is sharp: below the threshold, the noncompact
     sharp gap through this inverse is RH-strength.
   - Vacuity check: for a < 1/2 the mixture need not be locally finite, so a statement there
     needs a renormalized mixture. No such statement is formalized.
8. **Falsification checks.**
   - Non-vacuity: the delta_0 mixer meets both sharp-gap hypotheses (formal). The delta_(-1)
     mixer gives a strictly positive leakage bound (formal). The endpoint witness e^(-b\|t\|) dt
     is an admissible actual mixer with explicit density (formal).
   - Necessity: the unrestricted leakage fails (formal).
   - Scaling and threshold: the constant tends to 0 at a = 1/2, consistent with the pole.
   - Circularity: the inverse uses only the finite divisor identity, Mathlib's Euler product
     and Tonelli/Fubini on genuine product measures.
   - Complex versus real: the genuine-variation clause and the per-part clauses are logically
     independent; both are proved.
9. **Highest-leverage next moves.**
   - `ProfileEulerMaclaurin`, `LogFourierSobolev` and the three CP1 roots, which gate most
     absent roots, with J5.2/MS1 in parallel; then R2-S3, where the complex-variation tools
     transfer.
   - Optional supporting work: r_h = O(x^(b-1/2)) and the affine-correction corollary; a
     renormalized statement probing the a <= 1/2 boundary; the HT2 rate (1-a)^(1/5).

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 6 and carries older counts; README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 6 head, the 37 absent roots, RH, Step 4 and the
independent closing inequalities.
