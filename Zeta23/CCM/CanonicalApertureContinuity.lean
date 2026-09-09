import Zeta23.CCM.CanonicalApertureRegularityScaffold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace Zeta23.CCM

open Matrix MeasureTheory Set
open scoped ArithmeticFunction BigOperators ComplexConjugate Interval Topology

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1a: fixed-cell canonical aperture continuity

This module proves the real continuity input needed by the post-#140
fixed-cutoff-cell regularization route.

The main analytic step removes the apparent origin singularity of the
archimedean density before invoking parameter-dependent interval-integral
continuity. The continuous extension of `x * archDensity x` is expressed
through the divided slope of `Real.sinh`; `Real.sinc` and divided slopes of
`cos` and `exp` then regularize the production archimedean integrands.

On a physical cutoff cell `(log Q, log (Q+1))`, the finite prime-power set is
frozen. Combining the continuous pole, direct equation-(4.4) archimedean, and
frozen prime channels gives entrywise continuity of the actual production
`canonicalSourceMatrix`, hence continuity and local strict-sign persistence of
one fixed finite quadratic witness.

No determinant nonidentity, dense regular-aperture theorem, predecessor
holomorphy, positivity theorem, or RH claim is asserted here.
-/

private theorem continuous_dslope_zero_of_continuous_differentiableAt
    {f : ℝ → ℝ}
    (hf : Continuous f)
    (hfd : DifferentiableAt ℝ f 0) :
    Continuous (dslope f 0) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr hfd
  · exact (continuousAt_dslope_of_ne hx).2 hf.continuousAt

/-- Continuous divided slope `sinh(x)/x`, with value `1` at the origin. -/
def archSinhSlope (x : ℝ) : ℝ :=
  dslope Real.sinh 0 x

@[fun_prop] theorem continuous_archSinhSlope :
    Continuous archSinhSlope := by
  unfold archSinhSlope
  exact continuous_dslope_zero_of_continuous_differentiableAt
    Real.continuous_sinh (Real.hasDerivAt_sinh 0).differentiableAt

/-- The regularized hyperbolic divided slope never vanishes. -/
theorem archSinhSlope_ne_zero (x : ℝ) :
    archSinhSlope x ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    rw [archSinhSlope, dslope_same, (Real.hasDerivAt_sinh 0).deriv]
    norm_num
  · rw [archSinhSlope, dslope_of_ne _ hx]
    unfold slope
    have hs : Real.sinh x ≠ 0 := (Real.sinh_ne_zero).2 hx
    simp [hx, hs]

/-- Continuous extension of `x * archDensity x` through the origin. -/
def regularizedArchScale (x : ℝ) : ℝ :=
  Real.exp (x / 2) / (2 * archSinhSlope x)

@[simp] theorem regularizedArchScale_zero :
    regularizedArchScale 0 = 1 / 2 := by
  rw [regularizedArchScale, archSinhSlope, dslope_same,
    (Real.hasDerivAt_sinh 0).deriv]
  norm_num

@[fun_prop] theorem continuous_regularizedArchScale :
    Continuous regularizedArchScale := by
  unfold regularizedArchScale
  refine (Real.continuous_exp.comp (continuous_id.div_const 2)).div
    (continuous_const.mul continuous_archSinhSlope) ?_
  intro x
  exact mul_ne_zero (by norm_num) (archSinhSlope_ne_zero x)

/-- Away from the origin the regularized scale is exactly
`x * archDensity x`. -/
theorem regularizedArchScale_eq_mul_archDensity
    {x : ℝ} (hx : x ≠ 0) :
    regularizedArchScale x = x * archDensity x := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_ne_zero).2 hx
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    apply hs
    rw [Real.sinh_eq, h]
    norm_num
  rw [regularizedArchScale, archSinhSlope, dslope_of_ne _ hx]
  unfold slope archDensity
  simp only [Real.sinh_zero, sub_zero]
  rw [Real.sinh_eq]
  field_simp [hx, hden]
  ring

/-- Continuous divided slope of cosine at zero. -/
def archCosSlope (x : ℝ) : ℝ :=
  dslope Real.cos 0 x

@[fun_prop] theorem continuous_archCosSlope :
    Continuous archCosSlope := by
  unfold archCosSlope
  exact continuous_dslope_zero_of_continuous_differentiableAt
    Real.continuous_cos (Real.hasDerivAt_cos 0).differentiableAt

/-- Continuous divided slope of the real exponential at zero. -/
def archExpSlope (x : ℝ) : ℝ :=
  dslope Real.exp 0 x

@[fun_prop] theorem continuous_archExpSlope :
    Continuous archExpSlope := by
  unfold archExpSlope
  exact continuous_dslope_zero_of_continuous_differentiableAt
    Real.continuous_exp (Real.hasDerivAt_exp 0).differentiableAt

/-- Origin-regularized integrand for `alphaL`. -/
def regularizedAlphaIntegrand (n : ℤ) (L x : ℝ) : ℝ :=
  (2 * Real.pi * (n : ℝ) / L) *
    Real.sinc (2 * Real.pi * (n : ℝ) * x / L) *
      regularizedArchScale x

@[simp] theorem regularizedAlphaIntegrand_zero
    (n : ℤ) (L : ℝ) :
    regularizedAlphaIntegrand n L 0 = Real.pi * (n : ℝ) / L := by
  simp [regularizedAlphaIntegrand, regularizedArchScale_zero]
  ring

/-- Away from the physical origin, the regularized alpha integrand is the
literal production integrand. -/
theorem regularizedAlphaIntegrand_eq_of_ne
    (n : ℤ) {L x : ℝ}
    (hL : L ≠ 0) (hx : x ≠ 0) :
    regularizedAlphaIntegrand n L x =
      Real.sin (2 * Real.pi * (n : ℝ) * x / L) * archDensity x := by
  by_cases hn : n = 0
  · subst n
    simp [regularizedAlphaIntegrand]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have harg : 2 * Real.pi * (n : ℝ) * x / L ≠ 0 := by
      exact div_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by positivity : (2 : ℝ) * Real.pi ≠ 0) hnR) hx)
        hL
    rw [regularizedAlphaIntegrand, Real.sinc_of_ne_zero harg,
      regularizedArchScale_eq_mul_archDensity hx]
    field_simp [hL, hx, hnR, Real.pi_ne_zero]
    ring

/-- Exact rewrite of `alphaL` by the continuous origin-regularized integrand. -/
theorem alphaL_eq_regularized_integral
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    alphaL n L =
      (1 / Real.pi) *
        ∫ x in (0 : ℝ)..L, regularizedAlphaIntegrand n L x := by
  unfold alphaL
  congr 1
  apply intervalIntegral.integral_congr
  intro x hxint
  by_cases hx : x = 0
  · subst x
    by_cases hn : n = 0
    · simp [hn, regularizedAlphaIntegrand_zero]
    · simp [hn, regularizedAlphaIntegrand_zero]
  · change
      Real.sin (2 * Real.pi * (n : ℝ) * x / L) * archDensity x =
        regularizedAlphaIntegrand n L x
    exact (regularizedAlphaIntegrand_eq_of_ne n hL.ne' hx).symm

private theorem continuous_regularizedAlphaIntegrand_pos_uncurry
    (n : ℤ) :
    Continuous
      (Function.uncurry
        (fun L : Ioi (0 : ℝ) =>
          fun x : ℝ => regularizedAlphaIntegrand n (L : ℝ) x)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨L, x⟩
  have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
  unfold Function.uncurry regularizedAlphaIntegrand
  fun_prop (disch := assumption)

/-- `alphaL n` is continuous on the positive aperture axis. -/
theorem continuous_alphaL_pos (n : ℤ) :
    Continuous (fun L : Ioi (0 : ℝ) => alphaL n (L : ℝ)) := by
  have hInt :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          ∫ x in (0 : ℝ)..(L : ℝ),
            regularizedAlphaIntegrand n (L : ℝ) x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume)
      (f := fun L : Ioi (0 : ℝ) =>
        fun x : ℝ => regularizedAlphaIntegrand n (L : ℝ) x)
      (a₀ := 0)
      (continuous_regularizedAlphaIntegrand_pos_uncurry n)
      continuous_subtype_val
  have hscaled :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          (1 / Real.pi) *
            ∫ x in (0 : ℝ)..(L : ℝ),
              regularizedAlphaIntegrand n (L : ℝ) x) :=
    continuous_const.mul hInt
  convert hscaled using 1
  funext L
  exact alphaL_eq_regularized_integral n L.property

/-- Real-axis packaging of positive-aperture alpha continuity. -/
theorem continuousOn_alphaL_Ioi (n : ℤ) :
    ContinuousOn (alphaL n) (Ioi (0 : ℝ)) := by
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_alphaL_pos n)

/-- Origin-regularized integrand for `betaL`. -/
def regularizedBetaIntegrand (n : ℤ) (L x : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (n : ℝ) * x / L) *
    regularizedArchScale x

@[simp] theorem regularizedBetaIntegrand_zero
    (n : ℤ) (L : ℝ) :
    regularizedBetaIntegrand n L 0 = 1 / 2 := by
  simp [regularizedBetaIntegrand, regularizedArchScale_zero]

/-- Away from the origin the beta regularization is exact. -/
theorem regularizedBetaIntegrand_eq_of_ne
    (n : ℤ) (L : ℝ) {x : ℝ} (hx : x ≠ 0) :
    regularizedBetaIntegrand n L x =
      x * Real.cos (2 * Real.pi * (n : ℝ) * x / L) * archDensity x := by
  rw [regularizedBetaIntegrand,
    regularizedArchScale_eq_mul_archDensity hx]
  ring

/-- Exact rewrite of `betaL` by the continuous origin-regularized integrand. -/
theorem betaL_eq_regularized_integral
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    betaL n L =
      (1 / L) *
        ∫ x in (0 : ℝ)..L, regularizedBetaIntegrand n L x := by
  unfold betaL
  congr 1
  apply intervalIntegral.integral_congr
  intro x hxint
  by_cases hx : x = 0
  · subst x
    simp [regularizedBetaIntegrand_zero]
  · change
      x * Real.cos (2 * Real.pi * (n : ℝ) * x / L) * archDensity x =
        regularizedBetaIntegrand n L x
    exact (regularizedBetaIntegrand_eq_of_ne n L hx).symm

private theorem continuous_regularizedBetaIntegrand_pos_uncurry
    (n : ℤ) :
    Continuous
      (Function.uncurry
        (fun L : Ioi (0 : ℝ) =>
          fun x : ℝ => regularizedBetaIntegrand n (L : ℝ) x)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨L, x⟩
  have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
  unfold Function.uncurry regularizedBetaIntegrand
  fun_prop (disch := assumption)

/-- `betaL n` is continuous on the positive aperture axis. -/
theorem continuous_betaL_pos (n : ℤ) :
    Continuous (fun L : Ioi (0 : ℝ) => betaL n (L : ℝ)) := by
  have hInt :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          ∫ x in (0 : ℝ)..(L : ℝ),
            regularizedBetaIntegrand n (L : ℝ) x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume)
      (f := fun L : Ioi (0 : ℝ) =>
        fun x : ℝ => regularizedBetaIntegrand n (L : ℝ) x)
      (a₀ := 0)
      (continuous_regularizedBetaIntegrand_pos_uncurry n)
      continuous_subtype_val
  have hinv : Continuous (fun L : Ioi (0 : ℝ) => (1 / (L : ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro L
    have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
    fun_prop (disch := assumption)
  have hscaled := hinv.mul hInt
  convert hscaled using 1
  funext L
  exact betaL_eq_regularized_integral n L.property

/-- Real-axis packaging of positive-aperture beta continuity. -/
theorem continuousOn_betaL_Ioi (n : ℤ) :
    ContinuousOn (betaL n) (Ioi (0 : ℝ)) := by
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_betaL_pos n)

/-- Origin-regularized direct equation-(4.11)-left-hand gamma integrand. -/
def regularizedSourceEq411LhsIntegrand (n : ℤ) (L x : ℝ) : ℝ :=
  ((2 * Real.pi * (n : ℝ) / L) *
      archCosSlope (2 * Real.pi * (n : ℝ) * x / L) +
    (1 / 2 : ℝ) * archExpSlope (-x / 2)) *
      regularizedArchScale x

@[simp] theorem regularizedSourceEq411LhsIntegrand_zero
    (n : ℤ) (L : ℝ) :
    regularizedSourceEq411LhsIntegrand n L 0 = 1 / 4 := by
  rw [regularizedSourceEq411LhsIntegrand, archCosSlope, archExpSlope,
    dslope_same, dslope_same, (Real.hasDerivAt_cos 0).deriv,
    (Real.hasDerivAt_exp 0).deriv, regularizedArchScale_zero]
  norm_num

/-- Away from the origin the gamma regularization is exactly the production
left-hand integrand. -/
theorem regularizedSourceEq411LhsIntegrand_eq_of_ne
    (n : ℤ) (L : ℝ) {x : ℝ} (hx : x ≠ 0) :
    regularizedSourceEq411LhsIntegrand n L x =
      (Real.cos (2 * Real.pi * (n : ℝ) * x / L) -
        Real.exp (-x / 2)) * archDensity x := by
  let a : ℝ := 2 * Real.pi * (n : ℝ) / L
  have harg : 2 * Real.pi * (n : ℝ) * x / L = a * x := by
    dsimp [a]
    ring
  have hcos := sub_smul_dslope Real.cos 0 (a * x)
  have hexp := sub_smul_dslope Real.exp 0 (-x / 2)
  simp only [sub_zero, Real.cos_zero, Real.exp_zero, smul_eq_mul] at hcos hexp
  have hexp' :
      (x / 2) * dslope Real.exp 0 (-x / 2) =
        1 - Real.exp (-x / 2) := by
    linarith
  have hnum :
      x *
          (a * dslope Real.cos 0 (a * x) +
            (1 / 2 : ℝ) * dslope Real.exp 0 (-x / 2)) =
        Real.cos (a * x) - Real.exp (-x / 2) := by
    calc
      x *
          (a * dslope Real.cos 0 (a * x) +
            (1 / 2 : ℝ) * dslope Real.exp 0 (-x / 2)) =
          (a * x) * dslope Real.cos 0 (a * x) +
            (x / 2) * dslope Real.exp 0 (-x / 2) := by ring
      _ = Real.cos (a * x) - Real.exp (-x / 2) := by
        rw [hcos, hexp']
        ring
  unfold regularizedSourceEq411LhsIntegrand
  rw [harg, regularizedArchScale_eq_mul_archDensity hx]
  unfold archCosSlope archExpSlope
  change
    (a * dslope Real.cos 0 (a * x) +
        (1 / 2 : ℝ) * dslope Real.exp 0 (-x / 2)) *
        (x * archDensity x) =
      (Real.cos (a * x) - Real.exp (-x / 2)) * archDensity x
  calc
    (a * dslope Real.cos 0 (a * x) +
        (1 / 2 : ℝ) * dslope Real.exp 0 (-x / 2)) *
        (x * archDensity x) =
      (x *
          (a * dslope Real.cos 0 (a * x) +
            (1 / 2 : ℝ) * dslope Real.exp 0 (-x / 2))) *
        archDensity x := by ring
    _ = (Real.cos (a * x) - Real.exp (-x / 2)) * archDensity x := by
      rw [hnum]

/-- The regularized gamma integrand equals the exact source equation-(4.11)
left-hand integrand everywhere. -/
theorem regularizedSourceEq411LhsIntegrand_eq
    (n : ℤ) (L x : ℝ) :
    regularizedSourceEq411LhsIntegrand n L x =
      sourceEq411LhsIntegrand n L x := by
  by_cases hx : x = 0
  · subst x
    simp [sourceEq411LhsIntegrand]
  · simpa [sourceEq411LhsIntegrand, hx] using
      regularizedSourceEq411LhsIntegrand_eq_of_ne n L hx

private theorem continuous_regularizedSourceEq411LhsIntegrand_pos_uncurry
    (n : ℤ) :
    Continuous
      (Function.uncurry
        (fun L : Ioi (0 : ℝ) =>
          fun x : ℝ => regularizedSourceEq411LhsIntegrand n (L : ℝ) x)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨L, x⟩
  have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
  unfold Function.uncurry regularizedSourceEq411LhsIntegrand
  fun_prop (disch := assumption)

private theorem continuous_wCorrection_pos :
    Continuous (fun L : Ioi (0 : ℝ) => wCorrection (L : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro L
  have hExp : 1 < Real.exp (L : ℝ) := Real.one_lt_exp_iff.mpr L.property
  have hnum : Real.exp (L : ℝ) + 1 ≠ 0 := by positivity
  have hden : Real.exp (L : ℝ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hExp)
  have hratio :
      (Real.exp (L : ℝ) + 1) / (Real.exp (L : ℝ) - 1) ≠ 0 :=
    div_ne_zero hnum hden
  unfold wCorrection
  fun_prop (disch := assumption)

/-- The direct equation-(4.4) gamma primitive is continuous on positive
apertures. -/
theorem continuous_sourceEq44GammaL_pos (n : ℤ) :
    Continuous (fun L : Ioi (0 : ℝ) => sourceEq44GammaL n (L : ℝ)) := by
  have hInt :
      Continuous
        (fun L : Ioi (0 : ℝ) =>
          ∫ x in (0 : ℝ)..(L : ℝ),
            regularizedSourceEq411LhsIntegrand n (L : ℝ) x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume)
      (f := fun L : Ioi (0 : ℝ) =>
        fun x : ℝ => regularizedSourceEq411LhsIntegrand n (L : ℝ) x)
      (a₀ := 0)
      (continuous_regularizedSourceEq411LhsIntegrand_pos_uncurry n)
      continuous_subtype_val
  have hsum := hInt.add continuous_wCorrection_pos
  convert hsum using 1
  funext L
  unfold sourceEq44GammaL
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact (regularizedSourceEq411LhsIntegrand_eq n (L : ℝ) x).symm

/-- The full direct equation-(4.4) archimedean entry is continuous on positive
apertures. -/
theorem continuous_sourceEq44ArchComponent_pos
    (n m : ℤ) :
    Continuous
      (fun L : Ioi (0 : ℝ) =>
        sourceEq44ArchComponent n m (L : ℝ)) := by
  by_cases hnm : n = m
  · subst m
    simp only [sourceEq44ArchComponent, if_pos]
    exact (continuous_sourceEq44GammaL_pos n).const_mul 2 |>.sub
      ((continuous_betaL_pos n).const_mul 2)
  · simp only [sourceEq44ArchComponent, if_neg hnm]
    exact ((continuous_alphaL_pos m).sub (continuous_alphaL_pos n)).div_const
      (((n - m : ℤ) : ℝ))

/-- The production pole entry is continuous on positive apertures. -/
theorem continuous_poleComponent_pos
    (n m : ℤ) :
    Continuous (fun L : Ioi (0 : ℝ) => poleComponent n m (L : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro L
  have hm :
      (L : ℝ) ^ 2 + 16 * Real.pi ^ 2 * (m : ℝ) ^ 2 ≠ 0 := by
    have hLsq : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos L.property
    positivity
  have hn :
      (L : ℝ) ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by
    have hLsq : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos L.property
    positivity
  unfold poleComponent
  dsimp only
  fun_prop (disch := assumption)

/-- The physical source coordinate of one frozen prime-power atom varies
continuously with positive aperture. -/
@[fun_prop] theorem continuous_primeSourceCoordinate_pos (q : ℕ) :
    Continuous
      (fun L : Ioi (0 : ℝ) => primeSourceCoordinate q (L : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro L
  have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
  unfold primeSourceCoordinate
  fun_prop (disch := assumption)

/-- Each entry of the frozen finite prime-power channel is continuous on the
positive aperture axis. -/
theorem continuous_frozenCanonicalPrimeMatrix_apply_pos
    (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    Continuous
      (fun L : Ioi (0 : ℝ) =>
        frozenCanonicalPrimeMatrix Q (L : ℝ) K i j) := by
  classical
  unfold frozenCanonicalPrimeMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply continuous_finsetSum (Finset.Icc 2 Q)
  intro q hq
  exact continuous_const.mul
    ((continuous_sourceMatrix_apply K i j).comp
      (continuous_primeSourceCoordinate_pos q))

/-- Physical open cutoff cell on which the finite prime-power horizon is fixed. -/
def fixedCanonicalCutoffCell (Q : ℕ) : Set ℝ :=
  Ioo (Real.log (Q : ℝ)) (Real.log ((Q + 1 : ℕ) : ℝ))

/-- Every physical cutoff cell with `Q >= 1` lies on the positive aperture
axis. -/
theorem fixedCanonicalCutoffCell_subset_Ioi
    {Q : ℕ} (hQ : 1 ≤ Q) :
    fixedCanonicalCutoffCell Q ⊆ Ioi (0 : ℝ) := by
  intro L hL
  have hlogQ : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hQ)
  exact lt_of_le_of_lt hlogQ hL.1

/-- On the physical cell `(log Q, log(Q+1))`, the natural floor of `exp L` is
exactly `Q`. -/
theorem natFloor_exp_eq_on_fixedCanonicalCutoffCell
    {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hL : L ∈ fixedCanonicalCutoffCell Q) :
    ⌊Real.exp L⌋₊ = Q := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hQ1pos : (0 : ℝ) < ((Q + 1 : ℕ) : ℝ) := by positivity
  rw [Nat.floor_eq_iff (Real.exp_pos L).le]
  constructor
  · have hexp : Real.exp (Real.log (Q : ℝ)) < Real.exp L :=
      Real.exp_lt_exp.mpr hL.1
    rw [Real.exp_log hQpos] at hexp
    exact hexp.le
  · have hexp : Real.exp L < Real.exp (Real.log ((Q + 1 : ℕ) : ℝ)) :=
      Real.exp_lt_exp.mpr hL.2
    rw [Real.exp_log hQ1pos] at hexp
    simpa using hexp

/-- The physical cutoff cell is open. -/
theorem isOpen_fixedCanonicalCutoffCell (Q : ℕ) :
    IsOpen (fixedCanonicalCutoffCell Q) := by
  exact isOpen_Ioo

/-- Positive-axis continuity of one pole entry, packaged as `ContinuousOn`. -/
private theorem continuousOn_poleComponent_Ioi (n m : ℤ) :
    ContinuousOn (fun L : ℝ => poleComponent n m L) (Ioi (0 : ℝ)) := by
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_poleComponent_pos n m)

/-- Positive-axis continuity of one direct equation-(4.4) archimedean entry. -/
private theorem continuousOn_sourceEq44ArchComponent_Ioi (n m : ℤ) :
    ContinuousOn (fun L : ℝ => sourceEq44ArchComponent n m L) (Ioi (0 : ℝ)) := by
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_sourceEq44ArchComponent_pos n m)

/-- Positive-axis continuity of one frozen prime entry. -/
private theorem continuousOn_frozenCanonicalPrimeMatrix_apply_Ioi
    (Q K : ℕ) (i j : Fin (2 * K + 1)) :
    ContinuousOn
      (fun L : ℝ => frozenCanonicalPrimeMatrix Q L K i j)
      (Ioi (0 : ℝ)) := by
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_frozenCanonicalPrimeMatrix_apply_pos Q K i j)

/-- On one physical cutoff cell, each entry of the actual production canonical
source matrix is continuous. -/
theorem continuousOn_canonicalSourceMatrix_apply_fixedCell
    (Q K : ℕ) (hQ : 1 ≤ Q)
    (i j : Fin (2 * K + 1)) :
    ContinuousOn
      (fun L : ℝ => canonicalSourceMatrix L K i j)
      (fixedCanonicalCutoffCell Q) := by
  have hsub := fixedCanonicalCutoffCell_subset_Ioi hQ
  let n : ℤ := centeredIndex K i
  let m : ℤ := centeredIndex K j
  have hpoleReal :
      ContinuousOn (fun L : ℝ => poleComponent n m L)
        (fixedCanonicalCutoffCell Q) :=
    (continuousOn_poleComponent_Ioi n m).mono hsub
  have harchReal :
      ContinuousOn (fun L : ℝ => sourceEq44ArchComponent n m L)
        (fixedCanonicalCutoffCell Q) :=
    (continuousOn_sourceEq44ArchComponent_Ioi n m).mono hsub
  have hpole :
      ContinuousOn (fun L : ℝ => (poleComponent n m L : ℂ))
        (fixedCanonicalCutoffCell Q) := by
    simpa using Complex.continuous_ofReal.comp_continuousOn hpoleReal
  have harch :
      ContinuousOn (fun L : ℝ => (sourceEq44ArchComponent n m L : ℂ))
        (fixedCanonicalCutoffCell Q) := by
    simpa using Complex.continuous_ofReal.comp_continuousOn harchReal
  have hfrozen :
      ContinuousOn
        (fun L : ℝ => frozenCanonicalPrimeMatrix Q L K i j)
        (fixedCanonicalCutoffCell Q) :=
    (continuousOn_frozenCanonicalPrimeMatrix_apply_Ioi Q K i j).mono hsub
  have hsum :
      ContinuousOn
        (fun L : ℝ =>
          (poleComponent n m L : ℂ) -
            (sourceEq44ArchComponent n m L : ℂ) -
              frozenCanonicalPrimeMatrix Q L K i j)
        (fixedCanonicalCutoffCell Q) :=
    (hpole.sub harch).sub hfrozen
  refine hsum.congr ?_
  intro L hL
  have hprime :=
    frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix
      (Q := Q) L K (natFloor_exp_eq_on_fixedCanonicalCutoffCell hQ hL)
  have hprimeEntry :
      frozenCanonicalPrimeMatrix Q L K i j =
        (primeComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) := by
    calc
      frozenCanonicalPrimeMatrix Q L K i j =
          canonicalPrimeMatrix L K i j := by
        exact congrArg (fun M => M i j) hprime
      _ = (primeComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) := rfl
  calc
    canonicalSourceMatrix L K i j = sourceEq44Matrix L K i j := by
      exact congrArg (fun M => M i j)
        (canonicalSourceMatrix_eq_sourceEq44Matrix L K)
    _ = (sourceEq44Entry (centeredIndex K i) (centeredIndex K j) L : ℂ) := rfl
    _ = (poleComponent n m L : ℂ) -
          (sourceEq44ArchComponent n m L : ℂ) -
            frozenCanonicalPrimeMatrix Q L K i j := by
      dsimp [n, m]
      unfold sourceEq44Entry
      push_cast
      rw [hprimeEntry]

/-- Fixed-vector canonical quadratic energy is continuous on one physical
cutoff cell. -/
theorem continuousOn_re_canonicalSourceQuadraticForm_fixedCell
    (Q N : ℕ) (hQ : 1 ≤ Q)
    (u : Fin (2 * N + 1) → ℂ) :
    ContinuousOn
      (fun L : ℝ =>
        (quadraticForm (canonicalSourceMatrix L N) u).re)
      (fixedCanonicalCutoffCell Q) := by
  have hcomplex :
      ContinuousOn
        (fun L : ℝ => quadraticForm (canonicalSourceMatrix L N) u)
        (fixedCanonicalCutoffCell Q) := by
    unfold quadraticForm
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro j hj
    exact
      ((continuousOn_const.mul
        (continuousOn_canonicalSourceMatrix_apply_fixedCell Q N hQ i j)).mul
          continuousOn_const)
  exact Complex.continuous_re.comp_continuousOn hcomplex

/-- Headline fixed-cell persistence theorem: a strict negative canonical
quadratic witness at an interior aperture remains the same strict negative
witness on some open neighborhood contained in the same physical cutoff cell. -/
theorem exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
    (Q N : ℕ) (hQ : 1 ≤ Q)
    (u : Fin (2 * N + 1) → ℂ)
    {L₁ : ℝ}
    (hcell : L₁ ∈ fixedCanonicalCutoffCell Q)
    (hneg :
      (quadraticForm (canonicalSourceMatrix L₁ N) u).re < 0) :
    ∃ J : Set ℝ,
      IsOpen J ∧
      L₁ ∈ J ∧
      J ⊆ fixedCanonicalCutoffCell Q ∧
      ∀ L ∈ J,
        (quadraticForm (canonicalSourceMatrix L N) u).re < 0 := by
  let energy : ℝ → ℝ := fun L =>
    (quadraticForm (canonicalSourceMatrix L N) u).re
  have hcontWithin :
      ContinuousWithinAt energy (fixedCanonicalCutoffCell Q) L₁ :=
    (continuousOn_re_canonicalSourceQuadraticForm_fixedCell Q N hQ u)
      L₁ hcell
  have hcont : ContinuousAt energy L₁ :=
    hcontWithin.continuousAt
      ((isOpen_fixedCanonicalCutoffCell Q).mem_nhds hcell)
  have hnegNhds : {L : ℝ | energy L < 0} ∈ 𝓝 L₁ :=
    hcont (isOpen_Iio.mem_nhds hneg)
  obtain ⟨U, hUsub, hUopen, hL₁U⟩ := mem_nhds_iff.mp hnegNhds
  let J : Set ℝ := U ∩ fixedCanonicalCutoffCell Q
  refine ⟨J, hUopen.inter (isOpen_fixedCanonicalCutoffCell Q),
    ⟨hL₁U, hcell⟩, inter_subset_right, ?_⟩
  intro L hL
  exact hUsub hL.1

end Zeta23.CCM

#print axioms Zeta23.CCM.regularizedArchScale_eq_mul_archDensity
#print axioms Zeta23.CCM.alphaL_eq_regularized_integral
#print axioms Zeta23.CCM.betaL_eq_regularized_integral
#print axioms Zeta23.CCM.regularizedSourceEq411LhsIntegrand_eq
#print axioms Zeta23.CCM.continuousOn_canonicalSourceMatrix_apply_fixedCell
#print axioms Zeta23.CCM.continuousOn_re_canonicalSourceQuadraticForm_fixedCell
#print axioms Zeta23.CCM.exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
