import Zeta23.ExceptionalZero.UniversalSincInitialLaplace
import Zeta23.ExceptionalZero.MeromorphicIdentity
import Mathlib.Analysis.Complex.Convex

/-!
# Actual visible poles bound the signed tail's Laplace domain

The cutoff correction is entire. Its elementary error term is regular
strictly to the right of theta. The actual squared-Weil resolvent is
meromorphic and has the nonzero coefficient of every actual off-line
zero as its principal part. Thus a genuinely integrable signed-tail
parameter cannot lie below q=2*(Re rho-1/2) when theta<q.

Coefficient summability, pole visibility and principal-part persistence
are filled by the actual fixed source. No pole-domain or abscissa lower
bound is supplied as a caller premise. The one-sided tail inequality is
the contradiction hypothesis from a missing signed excursion.
-/

noncomputable section

open Set MeasureTheory Complex Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

def fixedOriginalSincTailRegularPart (T θ M ε : ℝ) (z : ℂ) : ℂ :=
  -(ε : ℂ) * fixedOriginalSincInitialLaplace T z +
    (M : ℂ) * Complex.exp (-(z - (θ : ℂ)) * (T : ℂ)) / (z - (θ : ℂ))

def fixedOriginalSincTailContinuation (T θ M ε : ℝ) (z : ℂ) : ℂ :=
  (ε : ℂ) * filteredResolvent fixedOriginalSincSquaredFilter (1 / 2 : ℂ) z +
    fixedOriginalSincTailRegularPart T θ M ε z

private theorem fixedOriginalSincSquaredFilter_actual_summable :
    AbsolutelySummableZeroFilter fixedOriginalSincSquaredFilter :=
  absolutelySummable_originalSincSquaredFilter CCM.UniversalSinc.fixedScale_pos

theorem meromorphicAt_fixedOriginalSincTailRegularPart {T θ M ε : ℝ}
    (hT : 0 ≤ T) (z : ℂ) :
    MeromorphicAt (fixedOriginalSincTailRegularPart T θ M ε) z := by
  have hhead : MeromorphicAt (fun w : ℂ => -(ε : ℂ) * fixedOriginalSincInitialLaplace T w) z :=
    analyticAt_const.meromorphicAt.mul (analyticAt_fixedOriginalSincInitialLaplace hT z).meromorphicAt
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => (M : ℂ) * Complex.exp (-(w - (θ : ℂ)) * (T : ℂ))) z := by fun_prop
  have hden : AnalyticAt ℂ (fun w : ℂ => w - (θ : ℂ)) z :=
    analyticAt_id.sub analyticAt_const
  exact hhead.add (hnum.meromorphicAt.div hden.meromorphicAt)

theorem analyticAt_fixedOriginalSincTailRegularPart {T θ M ε : ℝ}
    (hT : 0 ≤ T) {z : ℂ} (hθ : θ < z.re) :
    AnalyticAt ℂ (fixedOriginalSincTailRegularPart T θ M ε) z := by
  have hhead : AnalyticAt ℂ (fun w : ℂ => -(ε : ℂ) * fixedOriginalSincInitialLaplace T w) z :=
    analyticAt_const.mul (analyticAt_fixedOriginalSincInitialLaplace hT z)
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => (M : ℂ) * Complex.exp (-(w - (θ : ℂ)) * (T : ℂ))) z := by fun_prop
  have hden : AnalyticAt ℂ (fun w : ℂ => w - (θ : ℂ)) z :=
    analyticAt_id.sub analyticAt_const
  have hne : z - (θ : ℂ) ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  exact hhead.add (hnum.div hden hne)

theorem meromorphicAt_fixedOriginalSincTailContinuation {T θ M ε : ℝ}
    (hT : 0 ≤ T) (z : ℂ) :
    MeromorphicAt (fixedOriginalSincTailContinuation T θ M ε) z :=
  (analyticAt_const.meromorphicAt.mul
    (meromorphicAt_filteredResolvent fixedOriginalSincSquaredFilter_actual_summable (1 / 2 : ℂ) z)).add
      (meromorphicAt_fixedOriginalSincTailRegularPart hT z)

theorem positiveLaplaceTransform_fixedOriginalSincSignedTail_eq_continuation_safe
    {T θ M ε : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 1 < z.re) (hθ : θ < z.re) :
    positiveLaplaceTransform (fixedOriginalSincSignedTail T θ M ε) z =
      fixedOriginalSincTailContinuation T θ M ε z := by
  rw [positiveLaplaceTransform_fixedOriginalSincSignedTail_safe hT hz hθ]
  unfold fixedOriginalSincTailContinuation fixedOriginalSincTailRegularPart
  ring

/-- Genuine integrability at p makes the actual positive tail's Laplace
transform analytic at every complex point to the right of p. -/
theorem analyticAt_fixedOriginalSincSignedTailLaplace_of_integrable
    {T θ M ε p : ℝ}
    (hbound : ∀ a : ℝ, T ≤ a →
      -(M * Real.exp (θ * a)) ≤ ε * fixedOriginalSincCorrelationReal a)
    (hp : Integrable (positiveLaplaceWeight (fixedOriginalSincSignedTail T θ M ε) p)
      positiveLaplaceHalfLine) {z : ℂ} (hpz : p < z.re) :
    AnalyticAt ℂ (positiveLaplaceTransform (fixedOriginalSincSignedTail T θ M ε)) z := by
  have hnonneg : ∀ a : ℝ, 0 ≤ a → 0 ≤ fixedOriginalSincSignedTail T θ M ε a :=
    fun a _ => fixedOriginalSincSignedTail_nonneg hbound a
  apply analyticAt_positiveLaplaceTransform_of_integrable_nhds
    (measurable_fixedOriginalSincSignedTail T θ M ε) hnonneg
  filter_upwards [isOpen_Ioi.eventually_mem hpz] with q hq
  exact integrable_positiveLaplaceWeight_mono
    (measurable_fixedOriginalSincSignedTail T θ M ε) hnonneg hp hq.le

private theorem fixedOriginalSincTailContinuation_principalPart_limit
    {T θ M ε : ℝ} (hT : 0 ≤ T) (ρ : zetaZeroConfig.carrier)
    (hθ : θ < 2 * ((ρ : ℂ).re - 1 / 2)) :
    Tendsto (fun z : ℂ => (z - filteredPolePoint (1 / 2 : ℂ) ρ) *
      fixedOriginalSincTailContinuation T θ M ε z)
      (𝓝[≠] filteredPolePoint (1 / 2 : ℂ) ρ)
      (𝓝 ((ε : ℂ) * zeroFilterCoeff fixedOriginalSincSquaredFilter ρ)) := by
  let z1 : ℂ := filteredPolePoint (1 / 2 : ℂ) ρ
  have hz1re : z1.re = 2 * ((ρ : ℂ).re - 1 / 2) := by
    norm_num [z1, filteredPolePoint, Complex.mul_re]
  obtain ⟨r, hr, hiso⟩ := exists_zero_isolation_radius ρ
  have hRlim := filteredResolvent_principalPart_limit
    fixedOriginalSincSquaredFilter_actual_summable (c := (1 / 2 : ℂ)) (ρ₀ := ρ) hr hiso
  have hEcont : ContinuousAt (fixedOriginalSincTailRegularPart T θ M ε) z1 :=
    (analyticAt_fixedOriginalSincTailRegularPart hT (by rw [hz1re]; exact hθ)).continuousAt
  have hsub : Tendsto (fun z : ℂ => z - z1) (𝓝 z1) (𝓝 0) := by
    simpa only [sub_self] using
      (continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => z1) z1)).tendsto
  have hElim : Tendsto (fun z : ℂ => (z - z1) * fixedOriginalSincTailRegularPart T θ M ε z)
      (𝓝[≠] z1) (𝓝 0) := by
    simpa only [zero_mul] using (hsub.mul hEcont.tendsto).mono_left nhdsWithin_le_nhds
  have hscaled := (tendsto_const_nhds (x := (ε : ℂ))).mul hRlim
  simpa only [fixedOriginalSincTailContinuation, Pi.add_apply, Pi.mul_apply,
    mul_add, mul_assoc, mul_left_comm, mul_comm, add_zero] using hscaled.add hElim

/-- The actual visible pole bounds every genuinely integrable signed-tail
parameter. No pole-domain condition is assumed. -/
theorem fixedOriginalSincSignedTail_domain_lower_bound
    {T θ M ε p : ℝ} (hT : 0 ≤ T) (hε : ε ≠ 0)
    (hbound : ∀ a : ℝ, T ≤ a →
      -(M * Real.exp (θ * a)) ≤ ε * fixedOriginalSincCorrelationReal a)
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re)
    (hθ : θ < 2 * ((ρ : ℂ).re - 1 / 2))
    (hp : p ∈ positiveLaplaceDomain (fixedOriginalSincSignedTail T θ M ε)) :
    2 * ((ρ : ℂ).re - 1 / 2) ≤ p := by
  by_contra hle
  have hpq : p < 2 * ((ρ : ℂ).re - 1 / 2) := lt_of_not_ge hle
  let U : ℂ → ℂ := positiveLaplaceTransform (fixedOriginalSincSignedTail T θ M ε)
  let H : ℂ → ℂ := fixedOriginalSincTailContinuation T θ M ε
  let D : Set ℂ := {z : ℂ | p < z.re}
  let z1 : ℂ := filteredPolePoint (1 / 2 : ℂ) ρ
  let b : ℝ := max (max 1 θ) p + 2
  have hUmero : MeromorphicOn U D := fun z hz =>
    (analyticAt_fixedOriginalSincSignedTailLaplace_of_integrable hbound hp hz).meromorphicAt
  have hHmero : MeromorphicOn H D := fun z _ => meromorphicAt_fixedOriginalSincTailContinuation hT z
  have hD : IsPreconnected D := (convex_halfSpace_re_gt p).isPreconnected
  have hb : p < b := by dsimp [b]; linarith [le_max_right (max (1 : ℝ) θ) p]
  have hbSafe : max 1 θ < (b : ℂ).re := by
    rw [Complex.ofReal_re]
    dsimp [b]
    linarith [le_max_left (max (1 : ℝ) θ) p]
  have hseed : U =ᶠ[𝓝 (b : ℂ)] H := by
    have hopen : IsOpen {z : ℂ | max 1 θ < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hbSafe] with z hz
    exact positiveLaplaceTransform_fixedOriginalSincSignedTail_eq_continuation_safe hT
      (lt_of_le_of_lt (le_max_left 1 θ) hz) (lt_of_le_of_lt (le_max_right 1 θ) hz)
  have hz1re : z1.re = 2 * ((ρ : ℂ).re - 1 / 2) := by
    norm_num [z1, filteredPolePoint, Complex.mul_re]
  have hprop := meromorphic_eventuallyEq_nhdsNE_of_isPreconnected hUmero hHmero hD
    (by exact hb : (b : ℂ) ∈ D) hseed z1 (by rw [hz1re]; exact hpq)
  have hHlim := fixedOriginalSincTailContinuation_principalPart_limit hT ρ hθ
  have hUcont : ContinuousAt U z1 :=
    (analyticAt_fixedOriginalSincSignedTailLaplace_of_integrable hbound hp
      (by rw [hz1re]; exact hpq)).continuousAt
  have hsub : Tendsto (fun z : ℂ => z - z1) (𝓝 z1) (𝓝 0) := by
    simpa only [sub_self] using
      (continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => z1) z1)).tendsto
  have hUlim : Tendsto (fun z : ℂ => (z - z1) * U z) (𝓝[≠] z1) (𝓝 0) := by
    simpa only [zero_mul] using (hsub.mul hUcont.tendsto).mono_left nhdsWithin_le_nhds
  have hprodEq : (fun z : ℂ => (z - z1) * U z) =ᶠ[𝓝[≠] z1]
      (fun z : ℂ => (z - z1) * H z) := by
    filter_upwards [hprop] with z hz
    rw [hz]
  have hHlim0 : Tendsto (fun z : ℂ => (z - z1) * H z) (𝓝[≠] z1) (𝓝 0) :=
    (tendsto_congr' hprodEq).mp hUlim
  have hzero : (ε : ℂ) * zeroFilterCoeff fixedOriginalSincSquaredFilter ρ = 0 :=
    tendsto_nhds_unique hHlim hHlim0
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hε)
    (fixedOriginalSincSquaredCoeff_ne_zero ρ (ne_of_gt hright))) hzero

theorem fixedOriginalSincSignedTail_domain_bddBelow
    {T θ M ε : ℝ} (hT : 0 ≤ T) (hε : ε ≠ 0)
    (hbound : ∀ a : ℝ, T ≤ a →
      -(M * Real.exp (θ * a)) ≤ ε * fixedOriginalSincCorrelationReal a)
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re)
    (hθ : θ < 2 * ((ρ : ℂ).re - 1 / 2)) :
    BddBelow (positiveLaplaceDomain (fixedOriginalSincSignedTail T θ M ε)) :=
  ⟨2 * ((ρ : ℂ).re - 1 / 2), fun _ hp =>
    fixedOriginalSincSignedTail_domain_lower_bound hT hε hbound ρ hright hθ hp⟩

theorem fixedOriginalSincSignedTail_abscissa_lower_bound
    {T θ M ε : ℝ} (hT : 0 ≤ T) (hε : ε ≠ 0)
    (hbound : ∀ a : ℝ, T ≤ a →
      -(M * Real.exp (θ * a)) ≤ ε * fixedOriginalSincCorrelationReal a)
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re)
    (hθ : θ < 2 * ((ρ : ℂ).re - 1 / 2)) :
    2 * ((ρ : ℂ).re - 1 / 2) ≤
      positiveLaplaceAbscissa (fixedOriginalSincSignedTail T θ M ε) :=
  le_csInf (positiveLaplaceDomain_fixedOriginalSincSignedTail_nonempty T θ M ε)
    (fun _ hp => fixedOriginalSincSignedTail_domain_lower_bound hT hε hbound ρ hright hθ hp)

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.meromorphicAt_fixedOriginalSincTailRegularPart
#print axioms Zeta23.ExceptionalZero.analyticAt_fixedOriginalSincTailRegularPart
#print axioms Zeta23.ExceptionalZero.meromorphicAt_fixedOriginalSincTailContinuation
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTransform_fixedOriginalSincSignedTail_eq_continuation_safe
#print axioms Zeta23.ExceptionalZero.analyticAt_fixedOriginalSincSignedTailLaplace_of_integrable
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincSignedTail_domain_lower_bound
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincSignedTail_domain_bddBelow
#print axioms Zeta23.ExceptionalZero.fixedOriginalSincSignedTail_abscissa_lower_bound
