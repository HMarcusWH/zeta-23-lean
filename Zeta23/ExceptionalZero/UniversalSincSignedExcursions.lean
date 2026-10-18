import Zeta23.ExceptionalZero.UniversalSincSignedPoleBound
import Mathlib.Tactic.Push

/-!
# Actual signed late excursions of the fixed physical source

A failed signed excursion makes the literal cutoff tail nonnegative.
Its genuine Laplace domain is nonempty, and the actual visible pole
forces its abscissa to lie above theta. The actual resolvent and compact
initial correction are analytic at that real abscissa. Meromorphic
identity propagation from the safe half-plane supplies the required
local continuation agreement, contradicting the positive Laplace
boundary theorem.

No rightmost zero, attained supremum, moment-series summability,
visibility certificate, or pole-domain premise is used. The original
coefficient remains a complex square, the pole is 2*(rho-1/2), the rate
is theta=2*beta, and the physical translation remains t=2a. These are
signed correlation excursions; converting them into the complete
original phase-depth producer is a further obligation.
-/

noncomputable section

open Set MeasureTheory Complex Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

/-- A one-sided late bound is impossible for the actual fixed source
when its exponential rate lies below one actual visible pole. -/
theorem not_fixedOriginalSincCorrelation_oneSidedTailBound
    {T θ M ε : ℝ} (hT : 0 ≤ T) (hε : ε ≠ 0)
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re)
    (hθ : θ < 2 * ((ρ : ℂ).re - 1 / 2)) :
    ¬ ∀ a : ℝ, T ≤ a →
      -(M * Real.exp (θ * a)) ≤ ε * fixedOriginalSincCorrelationReal a := by
  intro hbound
  let u : ℝ → ℝ := fixedOriginalSincSignedTail T θ M ε
  let σ : ℝ := positiveLaplaceAbscissa u
  let U : ℂ → ℂ := positiveLaplaceTransform u
  let H : ℂ → ℂ := fixedOriginalSincTailContinuation T θ M ε
  let D : Set ℂ := {z : ℂ | σ < z.re}
  let b : ℝ := max (max 1 θ) σ + 2
  have hu : Measurable u := measurable_fixedOriginalSincSignedTail T θ M ε
  have hnonneg : ∀ a : ℝ, 0 ≤ a → 0 ≤ u a :=
    fun a _ => fixedOriginalSincSignedTail_nonneg hbound a
  have hne : (positiveLaplaceDomain u).Nonempty :=
    positiveLaplaceDomain_fixedOriginalSincSignedTail_nonempty T θ M ε
  have hbelow : BddBelow (positiveLaplaceDomain u) :=
    fixedOriginalSincSignedTail_domain_bddBelow hT hε hbound ρ hright hθ
  have hσ : 2 * ((ρ : ℂ).re - 1 / 2) ≤ σ :=
    fixedOriginalSincSignedTail_abscissa_lower_bound hT hε hbound ρ hright hθ
  have hθσ : θ < σ := hθ.trans_le hσ
  have hHA : AnalyticAt ℂ H (σ : ℂ) :=
    (analyticAt_const.mul (analyticAt_fixedOriginalSincResolvent_ofReal σ)).add
      (analyticAt_fixedOriginalSincTailRegularPart hT
        (by simpa only [Complex.ofReal_re] using hθσ))
  have hUmero : MeromorphicOn U D :=
    meromorphicOn_positiveLaplaceTransform_abscissa_halfPlane hu hnonneg hne
  have hHmero : MeromorphicOn H D := fun z _ =>
    meromorphicAt_fixedOriginalSincTailContinuation hT z
  have hD : IsPreconnected D := (convex_halfSpace_re_gt σ).isPreconnected
  have hb : σ < b := by
    dsimp [b]
    linarith [le_max_right (max (1 : ℝ) θ) σ]
  have hbSafe : max 1 θ < (b : ℂ).re := by
    rw [Complex.ofReal_re]
    dsimp [b]
    linarith [le_max_left (max (1 : ℝ) θ) σ]
  have hseed : U =ᶠ[𝓝 (b : ℂ)] H := by
    have hopen : IsOpen {z : ℂ | max 1 θ < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hbSafe] with z hz
    exact positiveLaplaceTransform_fixedOriginalSincSignedTail_eq_continuation_safe hT
      (lt_of_le_of_lt (le_max_left 1 θ) hz) (lt_of_le_of_lt (le_max_right 1 θ) hz)
  have hprop : ∀ z ∈ D, U =ᶠ[𝓝[≠] z] H :=
    meromorphic_eventuallyEq_nhdsNE_of_isPreconnected hUmero hHmero hD
      (by exact hb : (b : ℂ) ∈ D) hseed
  have hagree : ∀ᶠ z in 𝓝 (σ : ℂ), σ < z.re → H z = U z := by
    filter_upwards [hHA.eventually_analyticAt] with z hz hrightz
    have hUA : AnalyticAt ℂ U z :=
      analyticAt_positiveLaplaceTransform_of_abscissa_lt hu hnonneg hne hrightz
    have hULim : Tendsto U (𝓝[≠] z) (𝓝 (U z)) :=
      hUA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hHLimU : Tendsto H (𝓝[≠] z) (𝓝 (U z)) :=
      (tendsto_congr' (hprop z hrightz)).mp hULim
    have hHLimH : Tendsto H (𝓝[≠] z) (𝓝 (H z)) :=
      hz.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hHLimH hHLimU
  exact not_analyticAt_positiveLaplace_continuation_at_abscissa
    hu hnonneg hne hbelow hagree hHA

/-- The sign parameter will be -1 for positive excursions and +1 for
negative excursions. The cutoff is strictly later than max(A,0). -/
theorem fixedOriginalSincCorrelation_signed_late_excursion_of_right_zero
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re)
    {θ ε : ℝ} (hθ : θ < 2 * ((ρ : ℂ).re - 1 / 2)) (hε : ε ≠ 0)
    (A M : ℝ) :
    ∃ a : ℝ, A < a ∧
      ε * fixedOriginalSincCorrelationReal a < -(M * Real.exp (θ * a)) := by
  by_contra hfail
  push_neg at hfail
  let T : ℝ := max A 0 + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [le_max_right A (0 : ℝ)]
  have hAT : A < T := by dsimp [T]; linarith [le_max_left A (0 : ℝ)]
  apply not_fixedOriginalSincCorrelation_oneSidedTailBound hT hε ρ hright hθ
  intro a hTa
  exact hfail a (hAT.trans_le hTa)

/-- Actual positive and negative correlation excursions at every rate
beta below the displacement of an actual right-hand zero. -/
theorem fixedOriginalSincCorrelation_two_signed_late_excursions_of_right_zero
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re)
    {β : ℝ} (hβ : β < (ρ : ℂ).re - 1 / 2) (A M : ℝ) :
    (∃ a : ℝ, A < a ∧ M * Real.exp (2 * β * a) < fixedOriginalSincCorrelationReal a) ∧
    (∃ a : ℝ, A < a ∧ fixedOriginalSincCorrelationReal a < -(M * Real.exp (2 * β * a))) := by
  have hθ : 2 * β < 2 * ((ρ : ℂ).re - 1 / 2) := by linarith
  constructor
  · obtain ⟨a, ha, hvalue⟩ :=
      fixedOriginalSincCorrelation_signed_late_excursion_of_right_zero
        ρ hright hθ (by norm_num : (-1 : ℝ) ≠ 0) A M
    refine ⟨a, ha, ?_⟩
    nlinarith
  · simpa only [one_mul] using
      fixedOriginalSincCorrelation_signed_late_excursion_of_right_zero
        ρ hright hθ (by norm_num : (1 : ℝ) ≠ 0) A M

/-- The actual one-sub zeta involution handles left-hand zeros. No
rightmost-zero or attained-supremum premise is introduced. -/
theorem fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2)
    {β : ℝ} (hβ : β < |(ρ : ℂ).re - 1 / 2|) (A M : ℝ) :
    (∃ a : ℝ, A < a ∧ M * Real.exp (2 * β * a) < fixedOriginalSincCorrelationReal a) ∧
    (∃ a : ℝ, A < a ∧ fixedOriginalSincCorrelationReal a < -(M * Real.exp (2 * β * a))) := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · let ρ' : zetaZeroConfig.carrier := zetaOneSubEquiv ρ
    have hre : (ρ' : ℂ).re = 1 - (ρ : ℂ).re := by
      simp only [ρ', zetaOneSubEquiv_coe, Complex.sub_re, Complex.one_re]
    have hright' : 1 / 2 < (ρ' : ℂ).re := by rw [hre]; linarith
    have hβ' : β < (ρ' : ℂ).re - 1 / 2 := by
      rw [abs_of_neg (sub_neg.mpr hleft)] at hβ
      rw [hre]
      linarith
    exact fixedOriginalSincCorrelation_two_signed_late_excursions_of_right_zero
      ρ' hright' hβ' A M
  · have hβ' : β < (ρ : ℂ).re - 1 / 2 := by
      simpa only [abs_of_pos (sub_pos.mpr hright)] using hβ
    exact fixedOriginalSincCorrelation_two_signed_late_excursions_of_right_zero
      ρ hright hβ' A M

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.not_fixedOriginalSincCorrelation_oneSidedTailBound
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincCorrelation_signed_late_excursion_of_right_zero
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincCorrelation_two_signed_late_excursions_of_right_zero
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
