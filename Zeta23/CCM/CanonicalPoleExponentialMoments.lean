import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Zeta23.CCM

open Complex Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Physical elementary-pole moments of the unchanged localized finite vector.

The spatial support is the existing `[0,L]` interval and the mode has its
existing `L^(-1/2)` normalization. No centered translation, change of phase,
or replacement profile is made. The scalar factors below are kept explicit.
-/

def canonicalPoleExponentialMoment (σ L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) : ℂ :=
  ∫ x : ℝ, (Real.exp (σ * x / 2) : ℂ) * localizedFiniteVector L K u x

def canonicalPoleExponentialMomentScale (σ L : ℝ) : ℂ :=
  ((2 * L / Real.sqrt L : ℝ) : ℂ) * ((Real.exp (σ * L / 2) - 1 : ℝ) : ℂ)

private def poleExponentialRate (σ L : ℝ) (n : ℤ) : ℂ :=
  ((σ / 2 : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ)

private theorem poleExponentialRate_ne_zero (σ L : ℝ) (n : ℤ)
    (hσ : σ = 1 ∨ σ = -1) : poleExponentialRate σ L n ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  rcases hσ with rfl | rfl <;> norm_num [poleExponentialRate] at hr

private theorem poleExponentialRate_endpoint {L : ℝ} (hL : 0 < L)
    (σ : ℝ) (n : ℤ) :
    poleExponentialRate σ L n * L =
      ((σ * L / 2 : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
  unfold poleExponentialRate
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne'] <;> ring

private theorem poleExponentialRate_inv {L : ℝ} (hL : 0 < L)
    (σ : ℝ) (n : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (poleExponentialRate σ L n)⁻¹ =
      ((2 * L : ℝ) : ℂ) *
        ((σ : ℂ) * (poleEvenProfileReal n L : ℂ) -
          Complex.I * (poleOddProfileReal n L : ℂ)) := by
  have hd := ne_of_gt (poleProfileDenominator_pos hL n)
  apply inv_eq_of_mul_eq_one_right
  rcases hσ with rfl | rfl
  all_goals
    apply Complex.ext <;>
      simp [poleExponentialRate, poleEvenProfileReal, poleOddProfileReal,
        Complex.mul_re, Complex.mul_im] <;>
      field_simp [hL.ne', hd] <;>
      unfold poleProfileDenominator <;> ring

private theorem poleExponentialMode_eq (σ L : ℝ) (n : ℤ) (x : ℝ) :
    (Real.exp (σ * x / 2) : ℂ) * localizedMode L n x =
      ((1 / Real.sqrt L : ℝ) : ℂ) * Complex.exp (poleExponentialRate σ L n * x) := by
  unfold localizedMode
  rw [Complex.ofReal_exp]
  rw [show Complex.exp ((σ * x / 2 : ℝ) : ℂ) *
      (((1 / Real.sqrt L : ℝ) : ℂ) * Complex.exp
        (Complex.I * ((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ))) =
    ((1 / Real.sqrt L : ℝ) : ℂ) *
      (Complex.exp ((σ * x / 2 : ℝ) : ℂ) * Complex.exp
        (Complex.I * ((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ))) by ring]
  rw [← Complex.exp_add]
  congr 2
  unfold poleExponentialRate
  push_cast
  ring

/-- Exact weighted integral of one unchanged normalized localized character. -/
theorem intervalIntegral_exp_mul_localizedMode {L : ℝ} (hL : 0 < L)
    (σ : ℝ) (n : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    (∫ x in (0 : ℝ)..L, (Real.exp (σ * x / 2) : ℂ) * localizedMode L n x) =
      canonicalPoleExponentialMomentScale σ L *
        ((σ : ℂ) * (poleEvenProfileReal n L : ℂ) -
          Complex.I * (poleOddProfileReal n L : ℂ)) := by
  simp_rw [poleExponentialMode_eq]
  rw [intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (poleExponentialRate_ne_zero σ L n hσ),
    poleExponentialRate_endpoint hL]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp only [mul_one, mul_zero, Complex.exp_zero]
  rw [div_eq_mul_inv, poleExponentialRate_inv hL σ n hσ]
  unfold canonicalPoleExponentialMomentScale
  rw [← Complex.ofReal_exp]
  push_cast
  ring

/-- Preserve the actual hard window before evaluating the physical moment. -/
theorem canonicalPoleExponentialMoment_eq_intervalIntegral (σ L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (hL : 0 < L) :
    canonicalPoleExponentialMoment σ L K u =
      ∫ x in (0 : ℝ)..L,
        (Real.exp (σ * x / 2) : ℂ) * localizedFiniteFunction L K u x := by
  unfold canonicalPoleExponentialMoment
  have hf : (fun x : ℝ =>
      (Real.exp (σ * x / 2) : ℂ) * localizedFiniteVector L K u x) =
    (Icc (0 : ℝ) L).indicator (fun x =>
      (Real.exp (σ * x / 2) : ℂ) * localizedFiniteFunction L K u x) := by
    funext x
    rw [localizedFiniteVector_eq_indicator]
    by_cases hx : x ∈ Icc (0 : ℝ) L <;> simp [hx]
  rw [hf, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le]

/-- Physical moments factor through exactly the existing native pole profiles. -/
theorem canonicalPoleExponentialMoment_eq_profiles {L : ℝ} (hL : 0 < L)
    (σ : ℝ) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (hσ : σ = 1 ∨ σ = -1) :
    canonicalPoleExponentialMoment σ L K u =
      canonicalPoleExponentialMomentScale σ L *
        ((σ : ℂ) * (poleEvenProfile L K ⬝ᵥ u) -
          Complex.I * (poleOddProfile L K ⬝ᵥ u)) := by
  rw [canonicalPoleExponentialMoment_eq_intervalIntegral σ L K u hL]
  have hf : (fun x : ℝ =>
      (Real.exp (σ * x / 2) : ℂ) * localizedFiniteFunction L K u x) =
    (fun x => ∑ i, u i * ((Real.exp (σ * x / 2) : ℂ) *
      localizedMode L (centeredIndex K i) x)) := by
    funext x
    simp only [localizedFiniteFunction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hf, intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,
      intervalIntegral_exp_mul_localizedMode hL σ _ hσ]
    unfold dotProduct poleEvenProfile poleOddProfile
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  · intro i hi
    apply Continuous.intervalIntegrable
    unfold localizedMode
    fun_prop

theorem canonicalPoleExponentialMomentScale_ne_zero {L : ℝ} (hL : 0 < L)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    canonicalPoleExponentialMomentScale σ L ≠ 0 := by
  unfold canonicalPoleExponentialMomentScale
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) (by positivity))
  · apply Complex.ofReal_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro he
    have hz : σ * L / 2 = 0 := (Real.exp_eq_one_iff (σ * L / 2)).mp he
    rcases hσ with rfl | rfl <;> linarith

/-- Both physical elementary-pole moments vanish exactly on both native
profile kernels, with all phase and normalization factors retained. -/
theorem canonicalPoleExponentialMoments_iff_profiles {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    (canonicalPoleExponentialMoment 1 L K u = 0 ∧
      canonicalPoleExponentialMoment (-1) L K u = 0) ↔
    (poleEvenProfile L K ⬝ᵥ u = 0 ∧ poleOddProfile L K ⬝ᵥ u = 0) := by
  rw [canonicalPoleExponentialMoment_eq_profiles hL 1 K u (Or.inl rfl),
    canonicalPoleExponentialMoment_eq_profiles hL (-1) K u (Or.inr rfl)]
  have hp := canonicalPoleExponentialMomentScale_ne_zero hL 1 (Or.inl rfl)
  have hm := canonicalPoleExponentialMomentScale_ne_zero hL (-1) (Or.inr rfl)
  simp only [mul_eq_zero, hp, hm, false_or, Complex.ofReal_one, one_mul,
    Complex.ofReal_neg, neg_mul]
  constructor
  · rintro ⟨hpos, hneg⟩
    have he : poleEvenProfile L K ⬝ᵥ u = 0 := by
      linear_combination (1 / 2 : ℂ) * hpos - (1 / 2 : ℂ) * hneg
    refine ⟨he, ?_⟩
    rw [he, zero_sub, neg_eq_zero] at hpos
    exact (mul_eq_zero.mp hpos).resolve_left Complex.I_ne_zero
  · rintro ⟨he, ho⟩
    simp [he, ho]

theorem poleNeutralEven_iff_exponentialMoments {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : euclideanEvenBoundaryFlatSubspace K) :
    u ∈ poleNeutralEvenSubspace L K ↔
      (canonicalPoleExponentialMoment 1 L K (evenBoundaryFlatRawCoefficients K u) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K (evenBoundaryFlatRawCoefficients K u) = 0) := by
  rw [canonicalPoleExponentialMoments_iff_profiles hL]
  have ho := poleOddProfile_dot_evenBoundaryFlat_eq_zero L K u
  simp only [ho, and_true]
  rfl

theorem poleNeutralOdd_iff_exponentialMoments {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : euclideanOddBoundaryFlatSubspace K) :
    u ∈ poleNeutralOddSubspace L K ↔
      (canonicalPoleExponentialMoment 1 L K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
            (u : EuclideanSpace ℂ (Fin (2 * K + 1)))) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
            (u : EuclideanSpace ℂ (Fin (2 * K + 1)))) = 0) := by
  rw [canonicalPoleExponentialMoments_iff_profiles hL]
  have hu := ((mem_euclideanOddBoundaryFlatSubspace_iff K
    (u : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp u.property).2
  have he : poleEvenProfile L K ⬝ᵥ
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (u : EuclideanSpace ℂ (Fin (2 * K + 1)))) = 0 := by
    rw [dotProduct_comm]
    exact dotProduct_eq_zero_of_reverse_odd_even K _ (poleEvenProfile L K)
      ((mem_oddCoefficientSubspace_iff K _).mp hu)
      (reverseCoefficients_poleEvenProfile L K)
  simp only [he, true_and]
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.intervalIntegral_exp_mul_localizedMode
#print axioms Zeta23.CCM.canonicalPoleExponentialMoment_eq_profiles
#print axioms Zeta23.CCM.canonicalPoleExponentialMoments_iff_profiles
#print axioms Zeta23.CCM.poleNeutralEven_iff_exponentialMoments
#print axioms Zeta23.CCM.poleNeutralOdd_iff_exponentialMoments
