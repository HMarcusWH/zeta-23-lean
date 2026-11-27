import Zeta23.OPICASupport.NativeParityRational.PolynomialReversal
import Zeta23.OPICASupport.ParityRational.PoleSquareSampling
import Zeta23.OPICASupport.FourierBridge.FiniteFourierRational
import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices
import Zeta23.CCM.CanonicalPoleExponentialMoments
import Zeta23.CCM.SourceMomentVandermondeFiltration

/-!
The actual native coefficient vectors, parity, moment-prefix constraints and
elementary-pole kernels. The Fourier convention is exactly `exp (I*z*x)` on
the unchanged localized vector; its nodal poles are `-(2*pi/L)*centeredIndex`.
No coefficient normalization, translated window, energy sign or zero-supply
hypothesis is introduced.
-/

noncomputable section

namespace Zeta23.OPICARound20.NativeParityRational

open CCM OPICARound4.ArithmeticFrontier Polynomial
open scoped BigOperators

def physicalPole (L : ℝ) (K : ℕ) (i : Fin (2 * K + 1)) : ℂ :=
  -((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ)

def evenPhysicalCoefficients {L : ℝ} {K : ℕ} (u : poleNeutralEvenSubspace L K) :
    Fin (2 * K + 1) → ℂ :=
  (EuclideanSpace.equiv _ ℂ) u.val.val

def oddPhysicalCoefficients {L : ℝ} {K : ℕ} (u : poleNeutralOddSubspace L K) :
    Fin (2 * K + 1) → ℂ :=
  (EuclideanSpace.equiv _ ℂ) u.val.val

theorem physicalPole_reverse (L : ℝ) (K : ℕ) (i : Fin (2 * K + 1)) :
    physicalPole L K i.rev = -physicalPole L K i := by
  simp [physicalPole, centeredIndex_rev]

theorem physicalPole_injective {L : ℝ} (hL : 0 < L) (K : ℕ) :
    Function.Injective (physicalPole L K) := by
  have hω : -((2 * Real.pi / L : ℝ) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL.ne'))
  intro i j hij
  exact centeredIndex_injective K (Int.cast_injective (mul_left_cancel₀ hω hij))

theorem physicalPole_ne_of_nonresonance {L : ℝ} (hL : 0 < L) (K : ℕ) (z : ℂ)
    (hz : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) :
    ∀ i, z ≠ physicalPole L K i := by
  intro i heq
  have hn := paperModeDenominator_ne_zero_of_exp_ne_one hL z hz (centeredIndex K i)
  apply hn
  rw [heq]
  simp [physicalPole]

theorem finiteCauchySum_physicalPole_eq (L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (z : ℂ) :
    finiteCauchySum (physicalPole L K) u z =
      ∑ i, u i / (z + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ)) := by
  simp only [finiteCauchySum, physicalPole, neg_mul, sub_neg_eq_add]

theorem evenPhysicalCoefficients_mem {L : ℝ} {K : ℕ}
    (u : poleNeutralEvenSubspace L K) :
    evenPhysicalCoefficients u ∈ evenBoundaryFlatSubspace K :=
  (mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp u.val.property

theorem oddPhysicalCoefficients_mem {L : ℝ} {K : ℕ}
    (u : poleNeutralOddSubspace L K) :
    oddPhysicalCoefficients u ∈ oddBoundaryFlatSubspace K :=
  (mem_euclideanOddBoundaryFlatSubspace_iff K _).mp u.val.property

theorem evenMomentSlice_centered_moments {L : ℝ} {K : ℕ}
    (u : poleNeutralEvenSubspace L K) (hu : u ∈ evenMomentSlice L K) :
    ∀ k < 6, centeredMoment K k (evenPhysicalCoefficients u) = 0 := by
  have hm := evenPhysicalCoefficients_mem u
  have hf := (mem_boundaryFlatSubspace_iff K _).mp hm.1
  have h4 := (mem_evenMomentSlice_iff L K u).mp hu
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2
  · exact centeredMoment_odd_eq_zero_of_even hm.2 (by decide)
  · exact h4
  · exact centeredMoment_odd_eq_zero_of_even hm.2 (by decide)

theorem oddMomentSlice_centered_moments {L : ℝ} {K : ℕ}
    (u : poleNeutralOddSubspace L K) (hu : u ∈ oddMomentSlice L K) :
    ∀ k < 7, centeredMoment K k (oddPhysicalCoefficients u) = 0 := by
  have hm := oddPhysicalCoefficients_mem u
  have hf := (mem_boundaryFlatSubspace_iff K _).mp hm.1
  have h35 := (mem_oddMomentSlice_iff L K u).mp hu
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2
  · exact h35.1
  · exact centeredMoment_even_eq_zero_of_odd hm.2 (by decide)
  · exact h35.2
  · exact centeredMoment_even_eq_zero_of_odd hm.2 (by decide)

theorem physicalPole_moment_prefix (L : ℝ) (K r : ℕ)
    (u : Fin (2 * K + 1) → ℂ)
    (hm : ∀ k < r, centeredMoment K k u = 0) :
    ∀ k < r, ∑ i, physicalPole L K i ^ k * u i = 0 := by
  intro k hk
  simp only [physicalPole, mul_pow, mul_assoc]
  rw [← Finset.mul_sum]
  change _ * centeredMoment K k u = 0
  rw [hm k hk, mul_zero]

theorem evenPhysicalNumerator_square_form {L : ℝ} {K : ℕ}
    (u : poleNeutralEvenSubspace L K) :
    ∃ Q : ℂ[X], finiteCauchyNumerator (physicalPole L K) (evenPhysicalCoefficients u) =
      Q.comp (X ^ 2) := by
  apply exists_square_composition_of_comp_neg_X_eq
  apply finiteCauchyNumerator_even_of_reversal K _ _ (physicalPole_reverse L K)
  intro i
  exact congrFun ((mem_evenCoefficientSubspace_iff K _).mp
    (evenPhysicalCoefficients_mem u).2) i

theorem oddPhysicalNumerator_square_form {L : ℝ} {K : ℕ}
    (u : poleNeutralOddSubspace L K) :
    ∃ Q : ℂ[X], finiteCauchyNumerator (physicalPole L K) (oddPhysicalCoefficients u) =
      X * Q.comp (X ^ 2) := by
  apply exists_X_square_composition_of_comp_neg_X_eq_neg
  apply finiteCauchyNumerator_odd_of_reversal K _ _ (physicalPole_reverse L K)
  intro i
  exact congrFun ((mem_oddCoefficientSubspace_iff K _).mp
    (oddPhysicalCoefficients_mem u).2) i

/-- Exact imaginary-axis identification on the original physical interval.
The sign sends sigma=-1 to z=+I/2, with no additional phase factor. -/
theorem paperFT_imaginary_half_axis (σ L : ℝ) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    paperFT (localizedFiniteVector L K u) (-(Complex.I * (σ : ℂ)) / 2) =
      canonicalPoleExponentialMoment σ L K u := by
  unfold paperFT canonicalPoleExponentialMoment
  congr 1
  funext x
  have harg : Complex.I * (-(Complex.I * (σ : ℂ)) / 2) * (x : ℂ) =
      ((σ * x / 2 : ℝ) : ℂ) := by
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * (σ : ℂ) * (x : ℂ) / 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [harg, ← Complex.ofReal_exp]
  ring

theorem half_imaginary_nonresonant {L : ℝ} (hL : 0 < L) :
    Complex.exp (Complex.I * (Complex.I / 2) * (L : ℂ)) ≠ 1 := by
  have harg : Complex.I * (Complex.I / 2) * (L : ℂ) = ((-L / 2 : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (Complex.I * Complex.I) * (L : ℂ) / 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [harg, ← Complex.ofReal_exp]
  intro h
  have he : Real.exp (-L / 2) = 1 := by exact_mod_cast h
  have hz := (Real.exp_eq_one_iff (-L / 2)).mp he
  linarith

theorem evenPhysical_paperFT_half_imaginary_zero {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralEvenSubspace L K) :
    paperFT (localizedFiniteVector L K (evenPhysicalCoefficients u)) (Complex.I / 2) = 0 := by
  have hm := ((poleNeutralEven_iff_exponentialMoments hL K u.val).mp u.property).2
  have hft := paperFT_imaginary_half_axis (-1) L K (evenPhysicalCoefficients u)
  simpa [evenPhysicalCoefficients, evenBoundaryFlatRawCoefficients] using hft.trans hm

theorem oddPhysical_paperFT_half_imaginary_zero {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralOddSubspace L K) :
    paperFT (localizedFiniteVector L K (oddPhysicalCoefficients u)) (Complex.I / 2) = 0 := by
  have hm := ((poleNeutralOdd_iff_exponentialMoments hL K u.val).mp u.property).2
  have hft := paperFT_imaginary_half_axis (-1) L K (oddPhysicalCoefficients u)
  simpa [oddPhysicalCoefficients] using hft.trans hm

theorem physicalNumerator_root_of_paperFT_zero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hexp : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1)
    (hzero : paperFT (localizedFiniteVector L K u) z = 0) :
    (finiteCauchyNumerator (physicalPole L K) u).eval z = 0 := by
  have hs := (paperFT_localizedFiniteVector_zero_iff_rational_sum_zero hL K u z hexp).mp hzero
  rw [finiteCauchyNumerator_eval _ _ z (physicalPole_ne_of_nonresonance hL K z hexp),
    finiteCauchySum_physicalPole_eq, hs, mul_zero]

theorem evenPhysicalNumerator_half_imaginary_root {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralEvenSubspace L K) :
    (finiteCauchyNumerator (physicalPole L K) (evenPhysicalCoefficients u)).eval
      (Complex.I / 2) = 0 :=
  physicalNumerator_root_of_paperFT_zero hL K _ _ (half_imaginary_nonresonant hL)
    (evenPhysical_paperFT_half_imaginary_zero hL u)

theorem oddPhysicalNumerator_half_imaginary_root {L : ℝ} (hL : 0 < L) {K : ℕ}
    (u : poleNeutralOddSubspace L K) :
    (finiteCauchyNumerator (physicalPole L K) (oddPhysicalCoefficients u)).eval
      (Complex.I / 2) = 0 :=
  physicalNumerator_root_of_paperFT_zero hL K _ _ (half_imaginary_nonresonant hL)
    (oddPhysical_paperFT_half_imaginary_zero hL u)

end Zeta23.OPICARound20.NativeParityRational
