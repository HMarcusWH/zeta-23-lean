import Zeta23.CCM.DictionarySymmetry
import Zeta23.CCM.DictionarySmoothCoreBridge

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators

/-!
# Smooth-core polarization

H0 identifies the concrete zeta zero-side quadratic value with the production
`dictionaryMatrix` quadratic form on `coefficientSumReal = 0`.  This module
polarizes that restricted identity after first making deterministic matrix
symmetry explicit.

No unrestricted zero-side matrix is defined here, and no positivity statement is
claimed.
-/

/-- Real bilinear pairing induced by a complex matrix. -/
def realMatrixPairing {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℝ) : ℂ :=
  ∑ i, ∑ j, (u i : ℂ) * A i j * (v j : ℂ)

/-- Real polarization of `quadraticForm` gives the symmetrized matrix pairing. -/
theorem quadraticForm_real_polarization
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (1 / 4 : ℂ) *
        (quadraticForm A (fun i => ((u i + v i : ℝ) : ℂ)) -
          quadraticForm A (fun i => ((u i - v i : ℝ) : ℂ))) =
      (1 / 2 : ℂ) *
        (realMatrixPairing A u v + realMatrixPairing A v u) := by
  unfold quadraticForm realMatrixPairing
  simp only [Complex.conj_ofReal]
  push_cast
  simp_rw [add_mul, sub_mul, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- A symmetric matrix induces a symmetric real pairing. -/
theorem realMatrixPairing_comm_of_symmetric
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ)
    (hA : ∀ i j, A i j = A j i)
    (u v : ι → ℝ) :
    realMatrixPairing A u v = realMatrixPairing A v u := by
  unfold realMatrixPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA j i]
  ring

/-- The smooth-core condition is closed under addition. -/
theorem coefficientSumReal_add_eq_zero
    (N : ℕ) (u v : Fin (2 * N + 1) → ℝ)
    (hu : coefficientSumReal N u = 0)
    (hv : coefficientSumReal N v = 0) :
    coefficientSumReal N (fun i => u i + v i) = 0 := by
  unfold coefficientSumReal at *
  rw [Finset.sum_add_distrib, hu, hv]
  ring

/-- The smooth-core condition is closed under subtraction. -/
theorem coefficientSumReal_sub_eq_zero
    (N : ℕ) (u v : Fin (2 * N + 1) → ℝ)
    (hu : coefficientSumReal N u = 0)
    (hv : coefficientSumReal N v = 0) :
    coefficientSumReal N (fun i => u i - v i) = 0 := by
  unfold coefficientSumReal at *
  rw [Finset.sum_sub_distrib, hu, hv]
  ring

/-- Polarization of the complete zeta zero sums for the two smooth-core combinations. -/
def smoothCoreZeroPolarization
    (hs : ZetaSeam)
    (N : ℕ)
    (L : ℝ)
    (u v : Fin (2 * N + 1) → ℝ) : ℂ :=
  (1 / 4 : ℂ) *
    ((∑' ρ : (zetaZeros hs).carrier,
        ((zetaZeros hs).mult ρ : ℂ) *
          dictionaryTransform N (fun i => ((u i + v i : ℝ) : ℂ)) L (gammaOf ρ)) -
      (∑' ρ : (zetaZeros hs).carrier,
        ((zetaZeros hs).mult ρ : ℂ) *
          dictionaryTransform N (fun i => ((u i - v i : ℝ) : ℂ)) L (gammaOf ρ)))

/-- H1 endpoint: on the smooth core, zero-side polarization equals the production matrix pairing. -/
theorem smoothCoreZeroPolarization_eq_realMatrixPairing
    (hs : ZetaSeam)
    (N : ℕ)
    (u v : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0)
    (hv : coefficientSumReal N v = 0) :
    smoothCoreZeroPolarization hs N L u v =
      realMatrixPairing (dictionaryMatrix L N) u v := by
  have huv_add : coefficientSumReal N (fun i => u i + v i) = 0 :=
    coefficientSumReal_add_eq_zero N u v hu hv
  have huv_sub : coefficientSumReal N (fun i => u i - v i) = 0 :=
    coefficientSumReal_sub_eq_zero N u v hu hv
  have hplus := zeroSum_dictionaryTest_zero_sum_eq_quadraticForm
    hs N (fun i => u i + v i) hL huv_add
  have hminus := zeroSum_dictionaryTest_zero_sum_eq_quadraticForm
    hs N (fun i => u i - v i) hL huv_sub
  unfold smoothCoreZeroPolarization
  rw [hplus, hminus]
  calc
    (1 / 4 : ℂ) *
        (quadraticForm (dictionaryMatrix L N)
            (fun i => (((u i + v i : ℝ)) : ℂ)) -
          quadraticForm (dictionaryMatrix L N)
            (fun i => (((u i - v i : ℝ)) : ℂ))) =
        (1 / 2 : ℂ) *
          (realMatrixPairing (dictionaryMatrix L N) u v +
            realMatrixPairing (dictionaryMatrix L N) v u) :=
      quadraticForm_real_polarization (dictionaryMatrix L N) u v
    _ = realMatrixPairing (dictionaryMatrix L N) u v := by
      rw [realMatrixPairing_comm_of_symmetric
        (dictionaryMatrix L N) (dictionaryMatrix_apply_comm L N) v u]
      ring

end Zeta23.CCM

#print axioms Zeta23.CCM.smoothCoreZeroPolarization_eq_realMatrixPairing
