import Zeta23.ExceptionalZero.UniversalSincCorrelationReal
import Zeta23.ExceptionalZero.ZetaRealStripNonvanishing
import Zeta23.ExceptionalZero.FilteredLaplaceSubexp
import Zeta23.ExceptionalZero.PositiveLaplaceBoundary
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Actual fixed-source inputs for the signed Laplace route

The family is the literal fixed-source correlation at translation t=2a.
Its squared-Weil coefficient summability, realness, strip envelope, safe
Laplace identity and real-axis resolvent regularity are consumed internally.
The resolvent poles retain their factor two, 2(rho-1/2).

The signed tail is an actual cutoff function. A one-sided tail bound makes
it nonnegative, as needed in a contradiction to a missing signed excursion;
that bound is not claimed to hold. Its genuine Laplace domain is nonempty
without a supplied summability or transform bridge. For an excursion rate
beta the threshold parameter in this file is theta=2*beta.

The visible-pole lower bound on the signed tail's abscissa and its local
continuation identity remain separate obligations. No signed excursion or
M04 producer is asserted here.
-/

noncomputable section

open Set MeasureTheory Complex ProbabilityTheory Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

def fixedOriginalSincSquaredFilter : ZeroFilter :=
  squaredWeilZeroFilter (originalSincTest CCM.UniversalSinc.fixedScale)

def fixedOriginalSincCorrelation (a : ℝ) : ℂ :=
  weilRelativeCorrelation zetaZeroConfig
    (originalSincTest CCM.UniversalSinc.fixedScale) (2 * a)

def fixedOriginalSincCorrelationReal (a : ℝ) : ℝ :=
  (fixedOriginalSincCorrelation a).re

def fixedOriginalSincCoeffMass : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff fixedOriginalSincSquaredFilter ρ‖

private theorem fixedOriginalSincSquaredFilter_summable :
    AbsolutelySummableZeroFilter fixedOriginalSincSquaredFilter :=
  absolutelySummable_originalSincSquaredFilter CCM.UniversalSinc.fixedScale_pos

theorem fixedOriginalSincCorrelation_eq_filteredFamily (a : ℝ) :
    fixedOriginalSincCorrelation a =
      filteredZeroFamily fixedOriginalSincSquaredFilter (1 / 2 : ℂ) a :=
  originalSincCorrelation_eq_filteredSquaredFamily CCM.UniversalSinc.fixedScale_pos a

theorem fixedOriginalSincCorrelationReal_ofReal (a : ℝ) :
    (fixedOriginalSincCorrelationReal a : ℂ) = fixedOriginalSincCorrelation a := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, fixedOriginalSincCorrelation,
      fixed_originalSincCorrelation_im_eq_zero]

theorem measurable_fixedOriginalSincCorrelation : Measurable fixedOriginalSincCorrelation := by
  letI : Countable zetaZeroConfig.carrier := zetaZeroCarrier_countable.to_subtype
  have heq : fixedOriginalSincCorrelation =
      filteredZeroFamily fixedOriginalSincSquaredFilter (1 / 2 : ℂ) :=
    funext fixedOriginalSincCorrelation_eq_filteredFamily
  rw [heq]
  unfold filteredZeroFamily
  apply Measurable.tsum
  intro ρ
  unfold filteredZeroTerm
  fun_prop

theorem measurable_fixedOriginalSincCorrelationReal : Measurable fixedOriginalSincCorrelationReal :=
  Complex.continuous_re.measurable.comp measurable_fixedOriginalSincCorrelation

theorem abs_fixedOriginalSincCorrelationReal_le {a : ℝ} (ha : 0 ≤ a) :
    |fixedOriginalSincCorrelationReal a| ≤ fixedOriginalSincCoeffMass * Real.exp a := by
  calc
    _ ≤ ‖fixedOriginalSincCorrelation a‖ := Complex.abs_re_le_norm _
    _ ≤ _ := by
      rw [fixedOriginalSincCorrelation_eq_filteredFamily]
      exact norm_filteredZeroFamily_le_coeffMass_mul_exp
        fixedOriginalSincSquaredFilter_summable (by norm_num) ha

private theorem positiveLaplaceHalfLine_eq_restrict_Ioi :
    positiveLaplaceHalfLine = volume.restrict (Ioi (0 : ℝ)) :=
  (Measure.restrict_congr_set
    (Ioi_ae_eq_Ici : Ioi (0 : ℝ) =ᵐ[volume] Ici 0)).symm

private theorem integrable_exp_decay_halfLine {p : ℝ} (hp : 0 < p) :
    Integrable (fun a : ℝ => Real.exp (-p * a)) positiveLaplaceHalfLine := by
  rw [positiveLaplaceHalfLine_eq_restrict_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith : -p < 0) 0

/-- The actual correlation's real Laplace weights are genuinely integrable
throughout the safe strip half-plane, using its actual coefficient mass. -/
theorem integrable_fixedOriginalSincCorrelation_weight {p : ℝ} (hp : 1 < p) :
    Integrable (positiveLaplaceWeight fixedOriginalSincCorrelationReal p)
      positiveLaplaceHalfLine := by
  have hmajor : Integrable (fun a : ℝ =>
      fixedOriginalSincCoeffMass * Real.exp (-(p - 1) * a)) positiveLaplaceHalfLine :=
    (integrable_exp_decay_halfLine (by linarith : 0 < p - 1)).const_mul _
  have hmeas : AEStronglyMeasurable
      (positiveLaplaceWeight fixedOriginalSincCorrelationReal p) positiveLaplaceHalfLine :=
    (measurable_fixedOriginalSincCorrelationReal.mul
      ((measurable_const.mul measurable_id).exp)).aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with a ha
  unfold positiveLaplaceWeight
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |fixedOriginalSincCorrelationReal a| * Real.exp (-p * a) ≤
        (fixedOriginalSincCoeffMass * Real.exp a) * Real.exp (-p * a) :=
      mul_le_mul_of_nonneg_right (abs_fixedOriginalSincCorrelationReal_le ha)
        (Real.exp_pos _).le
    _ = fixedOriginalSincCoeffMass * Real.exp (-(p - 1) * a) := by
      rw [mul_assoc, ← Real.exp_add,
        show a + -p * a = -(p - 1) * a by ring]

/-- Safe Laplace transport for the literal real correlation. The transform
is the complete actual squared-Weil resolvent, with no supplied bridge. -/
theorem positiveLaplaceTransform_fixedOriginalSincCorrelation_safe {z : ℂ} (hz : 1 < z.re) :
    positiveLaplaceTransform fixedOriginalSincCorrelationReal z =
      filteredResolvent fixedOriginalSincSquaredFilter (1 / 2 : ℂ) z := by
  unfold positiveLaplaceTransform
  rw [positiveLaplaceHalfLine_eq_restrict_Ioi]
  have hfun : ∀ a : ℝ,
      (fixedOriginalSincCorrelationReal a : ℂ) * Complex.exp (-z * (a : ℂ)) =
        Complex.exp (-z * (a : ℂ)) *
          filteredZeroFamily fixedOriginalSincSquaredFilter (1 / 2 : ℂ) a := by
    intro a
    rw [fixedOriginalSincCorrelationReal_ofReal, fixedOriginalSincCorrelation_eq_filteredFamily]
    ring
  simp_rw [hfun]
  exact integral_laplace_filteredZeroFamily fixedOriginalSincSquaredFilter_summable
    (by norm_num) hz

/-- The actual fixed squared-Weil resolvent is regular at every real point. -/
theorem analyticAt_fixedOriginalSincResolvent_ofReal (p : ℝ) :
    AnalyticAt ℂ (filteredResolvent fixedOriginalSincSquaredFilter (1 / 2 : ℂ)) (p : ℂ) :=
  analyticAt_filteredResolvent_ofReal fixedOriginalSincSquaredFilter_summable p

/-- Every actual off-line zero has a nonzero actual squared-Weil coefficient. -/
theorem fixedOriginalSincSquaredCoeff_ne_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    zeroFilterCoeff fixedOriginalSincSquaredFilter ρ ≠ 0 := by
  rw [zeroFilterCoeff_squaredWeilZeroFilter]
  apply mul_ne_zero
  · have hm : 1 ≤ zeroMult (ρ : ℂ) := zetaZeroConfig.one_le_mult _ ρ.2
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  · exact fixed_originalSincTest_square_ne_zero_at_off_line_zero ρ hoff

/-- Literal signed tail; its sign coefficient is chosen as +1 or -1 in
the two respective excursion contradictions. -/
def fixedOriginalSincSignedTail (T θ M ε : ℝ) : ℝ → ℝ :=
  (Ici T).indicator (fun a => ε * fixedOriginalSincCorrelationReal a + M * Real.exp (θ * a))

theorem measurable_fixedOriginalSincSignedTail (T θ M ε : ℝ) :
    Measurable (fixedOriginalSincSignedTail T θ M ε) :=
  ((measurable_fixedOriginalSincCorrelationReal.const_mul ε).add
    (((measurable_const.mul measurable_id).exp).const_mul M)).indicator measurableSet_Ici

/-- A one-sided tail bound gives actual nonnegativity of the cutoff density.
This hypothesis is the bound obtained when the corresponding excursion fails. -/
theorem fixedOriginalSincSignedTail_nonneg {T θ M ε : ℝ}
    (hbound : ∀ a : ℝ, T ≤ a →
      -(M * Real.exp (θ * a)) ≤ ε * fixedOriginalSincCorrelationReal a) (a : ℝ) :
    0 ≤ fixedOriginalSincSignedTail T θ M ε a := by
  by_cases ha : a ∈ Ici T
  · rw [fixedOriginalSincSignedTail, Set.indicator_of_mem ha]
    have h := hbound a ha
    linarith
  · simp only [fixedOriginalSincSignedTail, Set.indicator_of_notMem ha, le_refl]

/-- Genuine signed-tail Laplace integrability follows from the actual
source envelope and elementary exponential decay. -/
theorem integrable_fixedOriginalSincSignedTail_weight (T θ M ε : ℝ) {p : ℝ}
    (hp : 1 < p) (hθ : θ < p) :
    Integrable (positiveLaplaceWeight (fixedOriginalSincSignedTail T θ M ε) p)
      positiveLaplaceHalfLine := by
  have hmain := (integrable_fixedOriginalSincCorrelation_weight hp).const_mul ε
  have herror := (integrable_exp_decay_halfLine (by linarith : 0 < p - θ)).const_mul M
  have hsum := (hmain.add herror).indicator
    (show MeasurableSet (Ici T) from measurableSet_Ici)
  have hfun : positiveLaplaceWeight (fixedOriginalSincSignedTail T θ M ε) p =
      (Ici T).indicator (fun a : ℝ =>
        ε * positiveLaplaceWeight fixedOriginalSincCorrelationReal p a +
          M * Real.exp (-(p - θ) * a)) := by
    funext a
    by_cases ha : a ∈ Ici T
    · simp only [positiveLaplaceWeight, fixedOriginalSincSignedTail,
        Set.indicator_of_mem ha]
      rw [add_mul]
      simp only [mul_assoc, ← Real.exp_add,
        show θ * a + -p * a = -(p - θ) * a by ring]
    · simp only [positiveLaplaceWeight, fixedOriginalSincSignedTail,
        Set.indicator_of_notMem ha, zero_mul]
  rw [hfun]
  exact hsum

theorem positiveLaplaceDomain_fixedOriginalSincSignedTail_nonempty (T θ M ε : ℝ) :
    (positiveLaplaceDomain (fixedOriginalSincSignedTail T θ M ε)).Nonempty := by
  refine ⟨max 1 θ + 1, integrable_fixedOriginalSincSignedTail_weight T θ M ε ?_ ?_⟩
  · linarith [le_max_left (1 : ℝ) θ]
  · linarith [le_max_right (1 : ℝ) θ]

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.fixedOriginalSincCorrelationReal_ofReal
#print axioms Zeta23.ExceptionalZero.measurable_fixedOriginalSincCorrelation
#print axioms Zeta23.ExceptionalZero.abs_fixedOriginalSincCorrelationReal_le
#print axioms Zeta23.ExceptionalZero.integrable_fixedOriginalSincCorrelation_weight
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTransform_fixedOriginalSincCorrelation_safe
#print axioms Zeta23.ExceptionalZero.analyticAt_fixedOriginalSincResolvent_ofReal
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincSquaredCoeff_ne_zero
#print axioms Zeta23.ExceptionalZero.measurable_fixedOriginalSincSignedTail
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincSignedTail_nonneg
#print axioms Zeta23.ExceptionalZero.integrable_fixedOriginalSincSignedTail_weight
#print axioms Zeta23.ExceptionalZero.positiveLaplaceDomain_fixedOriginalSincSignedTail_nonempty
