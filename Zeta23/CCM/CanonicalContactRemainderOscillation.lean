import Zeta23.CCM.WeightedRemainderIdentity
import Zeta23.CCM.CanonicalRecentPrimeSecondVariation

noncomputable section

namespace Zeta23.CCM

open MeasureTheory Set
open scoped BigOperators ArithmeticFunction Interval

/-!
# POST285 M33/M34: contact source sign reversal and remainder oscillation (Steps 68, 70, 71)

**Step 68 (M33).**  Let `v` be a normalized even ground eigenvector of the actual
even compression with positive parity gap `δ = λ_odd - λ_even` (in particular the
kernel vector of a strict-even contact), and `x = Dz` its legal odd index image.
Then `H(v) ≠ 0`, there is `θ > 0` with `e_x(ω) < 0` on `(0, θ]` (M45/M49 inside
the contact angle), `e_x(1) = 2‖x‖² > 0`, and so `e_x(ω₀) = 0` for some
`ω₀ ∈ (θ, 1)`.  This is the sign pattern of the contact-generated source only;
it says nothing about the canonical operator.

**Step 70 (M34).**  The exact remainder representation
`A_L[h] = ∫₀ᴸ R(e^t) h' + ∫₀ᴸ (e^{-t/2} - ρ) h` is M09
(`productionArithmeticRealValue_eq_weightedRemainder`).  Here: `R(e^t)` is
interval integrable against every continuous `h'`.

**Step 71 (M34).**  For any bounds `m ≤ R(e^t) ≤ M` on `[0, L]` and any `h` with
`∫ h' = 0`, `|∫ R(e^t) h'| ≤ (M - m)/2 · ∫ |h'|`.  At a stationary generated
strict-even contact, with `h(t) = t² e_{Dz}(1 - t/L*)`, the M09 balance turns
this into the necessary oscillation budget

`|∫₀^{L*} (e^{-t/2} - ρ) h + 2 L*⁴ C/(2π)²| ≤ (M - m)/2 · ∫₀^{L*} |h'|`

(the plan's (71.2), with `κ = ρ - e^{-t/2}` and `Ω = M - m`).  It is satisfied by
every such contact; nothing is excluded, no size of `R` is assumed or proved,
and a bound `R = O(x^ε)` would be RH-strength.
-/

/-! ## Step 70: integrability of the remainder channel -/

theorem weightedVonMangoldtSqrtSum_mono : Monotone weightedVonMangoldtSqrtSum := by
  intro x y hxy
  unfold weightedVonMangoldtSqrtSum
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy)) fun n _ _ => ?_
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

theorem intervalIntegrable_weightedRemainder_exp (a b : ℝ) :
    IntervalIntegrable (fun t => weightedVonMangoldtSqrtRemainder (Real.exp t)) volume a b := by
  unfold weightedVonMangoldtSqrtRemainder
  refine IntervalIntegrable.sub ?_ ?_
  · exact (weightedVonMangoldtSqrtSum_mono.comp Real.exp_monotone).intervalIntegrable
  · exact (by fun_prop : Continuous fun t => 2 * Real.sqrt (Real.exp t)).intervalIntegrable a b

theorem intervalIntegrable_weightedRemainder_exp_mul {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f [[a, b]]) :
    IntervalIntegrable (fun t => weightedVonMangoldtSqrtRemainder (Real.exp t) * f t)
      volume a b :=
  (intervalIntegrable_weightedRemainder_exp a b).mul_continuousOn hf

/-! ## Step 71: the oscillation bound -/

/-- **Oscillation bound.**  If `∫₀ᴸ f' = 0` and `m ≤ R ≤ M` on `[0, L]`, then
`|∫₀ᴸ R f'| ≤ (M - m)/2 · ∫₀ᴸ |f'|`. -/
theorem abs_integral_mul_le_half_oscillation {R f' : ℝ → ℝ} {L m M : ℝ} (hL : 0 ≤ L)
    (hRf : IntervalIntegrable (fun t => R t * f' t) volume 0 L)
    (hf' : IntervalIntegrable f' volume 0 L)
    (hzero : ∫ t in (0 : ℝ)..L, f' t = 0)
    (hm : ∀ t ∈ Icc 0 L, m ≤ R t) (hM : ∀ t ∈ Icc 0 L, R t ≤ M) :
    |∫ t in (0 : ℝ)..L, R t * f' t| ≤ (M - m) / 2 * ∫ t in (0 : ℝ)..L, |f' t| := by
  set c := (M + m) / 2 with hc
  have hshift : (∫ t in (0 : ℝ)..L, R t * f' t) = ∫ t in (0 : ℝ)..L, (R t - c) * f' t := by
    have : (∫ t in (0 : ℝ)..L, (R t - c) * f' t) =
        (∫ t in (0 : ℝ)..L, R t * f' t) - ∫ t in (0 : ℝ)..L, c * f' t := by
      rw [← intervalIntegral.integral_sub hRf (hf'.const_mul c)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [this, intervalIntegral.integral_const_mul, hzero, mul_zero, sub_zero]
  rw [hshift, ← intervalIntegral.integral_const_mul]
  have hb : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) L → ‖(R t - c) * f' t‖ ≤ (M - m) / 2 * |f' t| := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have h1 := hm t ⟨ht.1.le, ht.2⟩
    have h2 := hM t ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    have : |R t - c| ≤ (M - m) / 2 := by
      rw [abs_le, hc]
      constructor <;> linarith
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le hL hb (hf'.abs.const_mul _)
  rwa [Real.norm_eq_abs] at h

/-- The derivative of the contact test `h(t) = t² e_{Dz}(1 - t/L)`. -/
def productionContactTestDeriv (L : ℝ) (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K)
    (t : ℝ) : ℝ :=
  2 * t * productionContactIndexEnergy L K v t -
    t ^ 2 / L * sourceAtomRealEnergyDerivative K
      (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) (1 - t / L)

theorem hasDerivAt_productionContactTest (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) (t : ℝ) :
    HasDerivAt (fun s => s ^ 2 * productionContactIndexEnergy L K v s)
      (productionContactTestDeriv L K v t) t := by
  set x := sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have he : HasDerivAt (fun s => productionContactIndexEnergy L K v s)
      (sourceAtomRealEnergyDerivative K x (1 - t / L) * (-(1 / L))) t := by
    have := (hasDerivAt_sourceAtomRealEnergy_transport K x (1 - t / L)).comp t
      (((hasDerivAt_id t).div_const L).const_sub 1)
    simpa [productionContactIndexEnergy, x, Function.comp_def] using this
  have := (hasDerivAt_pow 2 t).mul he
  refine this.congr_deriv ?_
  simp only [productionContactTestDeriv]
  push_cast
  ring

theorem continuous_productionContactTestDeriv (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    Continuous (productionContactTestDeriv L K v) := by
  set x := sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have h1 : Continuous fun t : ℝ => sourceAtomRealEnergy K x (1 - t / L) :=
    (continuous_sourceAtomRealEnergy K x).comp (by fun_prop)
  have h2 : Continuous fun t : ℝ => sourceAtomRealEnergyDerivative K x (1 - t / L) :=
    (continuous_sourceAtomRealEnergyDerivative K x).comp (by fun_prop)
  unfold productionContactTestDeriv productionContactIndexEnergy
  fun_prop

/-- `∫₀ᴸ h' = h(L) - h(0) = 0` for the contact test. -/
theorem integral_productionContactTestDeriv {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    ∫ t in (0 : ℝ)..L, productionContactTestDeriv L K v t = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_productionContactTest L K v t)
    ((continuous_productionContactTestDeriv L K v).intervalIntegrable 0 L)]
  simp [productionContactIndexEnergy, div_self hL.ne']

/-- **(71.2), oscillation budget at a stationary contact.**  If the weighted
remainder satisfies `m ≤ R(e^t) ≤ M` on `[0, L*]`, then
`|∫ (e^{-t/2} - ρ) h + 2 L*⁴ C/(2π)²| ≤ (M - m)/2 · ∫ |h'|` for
`h(t) = t² e_{Dz}(1 - t/L*)`.  A necessary condition, not an exclusion. -/
theorem GeneratedStrictEvenContact.remainderOscillation_budget
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0)
    {m M : ℝ}
    (hm : ∀ t ∈ Icc 0 c.generated.shell.Lstar, m ≤ weightedVonMangoldtSqrtRemainder (Real.exp t))
    (hM : ∀ t ∈ Icc 0 c.generated.shell.Lstar, weightedVonMangoldtSqrtRemainder (Real.exp t) ≤ M) :
    |(∫ t in (0 : ℝ)..c.generated.shell.Lstar, (Real.exp (-t / 2) - archDensity t) *
          (t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
            (c.generated.shell.k + 1) c.z t)) +
        2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2 *
          productionContactResponseCost c.generated.shell.Lstar (c.generated.shell.k + 1)
            (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
              c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary)| ≤
      (M - m) / 2 * ∫ t in (0 : ℝ)..c.generated.shell.Lstar,
        |productionContactTestDeriv c.generated.shell.Lstar (c.generated.shell.k + 1) c.z t| := by
  set L := c.generated.shell.Lstar
  set K := c.generated.shell.k + 1
  have hL : 0 < L := c.Lstar_pos
  have hbal := (c.weightedRemainder_balance hstationary).1
  have hcont := continuous_productionContactTestDeriv L K c.z
  have hosc := abs_integral_mul_le_half_oscillation (R := fun t =>
      weightedVonMangoldtSqrtRemainder (Real.exp t)) hL.le
    (intervalIntegrable_weightedRemainder_exp_mul hcont.continuousOn)
    (hcont.intervalIntegrable 0 L) (integral_productionContactTestDeriv hL K c.z) hm hM
  have hfold : (∫ t in (0 : ℝ)..L, weightedVonMangoldtSqrtRemainder (Real.exp t) *
      productionContactTestDeriv L K c.z t) =
      -((∫ t in (0 : ℝ)..L, (Real.exp (-t / 2) - archDensity t) *
          (t ^ 2 * productionContactIndexEnergy L K c.z t)) +
        2 * L ^ 4 / (2 * Real.pi) ^ 2 *
          productionContactResponseCost L K
            (canonicalStationaryEvenResponse c.Lstar_pos K c.two_le_K
              c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary)) := by
    unfold productionContactTestDeriv
    linarith
  rw [hfold, abs_neg] at hosc
  exact hosc

/-! ## Step 68: contact source sign reversal -/

/-- At an even ground eigenvector with positive parity gap, the source moment
`H(v)` is nonzero. -/
theorem explicitCanonicalSourceMoment_ne_zero_of_parityGap
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig : parityCompressedCanonical .even L K v = (parityRayleighBottom .even L K : ℂ) • v)
    (hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K)
    (hv1 : ‖v‖ = 1) :
    explicitCanonicalSourceMoment L K v ≠ 0 := by
  intro h0
  have hgap := parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour hL K hK v hveig
  rw [h0, star_zero, zero_mul, Complex.zero_re] at hgap
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have hc := norm_sq_le_four_mul_norm_index_sq K (v : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat.1
  have hv1' : ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ = 1 := hv1
  rw [hv1', one_pow] at hc
  have hD : ‖euclideanEvenToOddIndexLinearMap K v‖ =
      ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ := rfl
  rw [hD] at hgap
  nlinarith [sq_nonneg ‖euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖]

/-- **Step 68.**  At a normalized even ground eigenvector with positive parity
gap, the contact source energy `e_{Dz}` is strictly negative on `(0, θ]` for
some `θ ∈ (0, 1)`, equals `2‖Dz‖² > 0` at `ω = 1`, and vanishes somewhere in
`(θ, 1)`. -/
theorem sourceAtomRealEnergy_index_signReversal
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig : parityCompressedCanonical .even L K v = (parityRayleighBottom .even L K : ℂ) • v)
    (hδ : 0 < parityRayleighBottom .odd L K - parityRayleighBottom .even L K)
    (hv1 : ‖v‖ = 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (∀ ω ∈ Ioc 0 θ,
        sourceAtomRealEnergy K (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) ω
          < 0) ∧
      0 < sourceAtomRealEnergy K
        (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) 1 ∧
      ∃ ω₀ ∈ Ioo θ 1,
        sourceAtomRealEnergy K
          (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) ω₀ = 0 := by
  set x := sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
  set δ := parityRayleighBottom .odd L K - parityRayleighBottom .even L K
  set X := sourceOddTaylorConstant K * ‖explicitCanonicalSourceMoment L K v‖ * 2
  have hX : 0 ≤ X := by
    have := sourceOddTaylorConstant_nonneg K
    positivity
  have hH := explicitCanonicalSourceMoment_ne_zero_of_parityGap hL K hK v hveig hδ hv1
  have hpi := Real.pi_pos
  set θ := min (1 / 2) (5 * δ / (4 * Real.pi ^ 2 * (X + 1))) with hθdef
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hneg : ∀ ω ∈ Ioc 0 θ, sourceAtomRealEnergy K x ω < 0 := by
    intro ω hω
    have hωθ : ω ≤ 5 * δ / (4 * Real.pi ^ 2 * (X + 1)) := hω.2.trans (min_le_right _ _)
    have hω1 : ω ≤ 1 := hω.2.trans hθ1.le
    have hangle : (2 * Real.pi * ω) ^ 2 * X ≤ 5 * δ := by
      have h1 : (2 * Real.pi * ω) ^ 2 * X ≤ 4 * Real.pi ^ 2 * ω * (X + 1) := by
        have : ω ^ 2 ≤ ω := by nlinarith [hω.1]
        have : (2 * Real.pi * ω) ^ 2 * X = 4 * Real.pi ^ 2 * ω ^ 2 * X := by ring
        rw [this]
        have hpi2 : 0 ≤ 4 * Real.pi ^ 2 := by positivity
        calc 4 * Real.pi ^ 2 * ω ^ 2 * X ≤ 4 * Real.pi ^ 2 * ω * X := by gcongr
          _ ≤ 4 * Real.pi ^ 2 * ω * (X + 1) := by
              have := hω.1.le
              nlinarith
      have h2 : 4 * Real.pi ^ 2 * ω * (X + 1) ≤ 5 * δ := by
        have hpos : 0 < 4 * Real.pi ^ 2 * (X + 1) := by positivity
        rw [le_div_iff₀ hpos] at hωθ
        linarith
      linarith
    have h := sourceAtomRealEnergy_index_le_of_contactAngle_four hL K hK v hveig hδ hv1
      hω.1.le hangle
    have hb : 0 < Real.pi ^ 6 / 90 * (δ / (4 * ‖explicitCanonicalSourceMoment L K v‖)) ^ 2 *
        ω ^ 7 := by
      have : 0 < ‖explicitCanonicalSourceMoment L K v‖ := norm_pos_iff.mpr hH
      have := hω.1
      positivity
    linarith
  have hone : 0 < sourceAtomRealEnergy K x 1 := by
    have hx : x ≠ 0 := by
      intro h0
      have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
      have hc := norm_sq_le_four_mul_norm_index_sq K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1))) hflat.1
      have hxe : x = euclideanIndexLinearMap K (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :=
        sourceIndexAction_eq_euclideanIndexLinearMap K _
      rw [← hxe, h0, norm_zero] at hc
      have hv1' : ‖(v : EuclideanSpace ℂ (Fin (2 * K + 1)))‖ = 1 := hv1
      rw [hv1'] at hc
      norm_num at hc
    unfold sourceAtomRealEnergy
    rw [matrixRealEnergy_sourceMatrix_one]
    have := norm_pos_iff.mpr hx
    positivity
  refine ⟨θ, hθ0, hθ1, hneg, hone, ?_⟩
  have hθneg := hneg θ ⟨hθ0, le_rfl⟩
  have hcont := (continuous_sourceAtomRealEnergy K x).continuousOn (s := Icc θ 1)
  obtain ⟨ω₀, hω₀, hz⟩ := intermediate_value_Ioo hθ1.le hcont ⟨hθneg, hone⟩
  exact ⟨ω₀, hω₀, hz⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.weightedVonMangoldtSqrtSum_mono
#print axioms Zeta23.CCM.intervalIntegrable_weightedRemainder_exp
#print axioms Zeta23.CCM.intervalIntegrable_weightedRemainder_exp_mul
#print axioms Zeta23.CCM.abs_integral_mul_le_half_oscillation
#print axioms Zeta23.CCM.hasDerivAt_productionContactTest
#print axioms Zeta23.CCM.continuous_productionContactTestDeriv
#print axioms Zeta23.CCM.integral_productionContactTestDeriv
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.remainderOscillation_budget
#print axioms Zeta23.CCM.explicitCanonicalSourceMoment_ne_zero_of_parityGap
#print axioms Zeta23.CCM.sourceAtomRealEnergy_index_signReversal
