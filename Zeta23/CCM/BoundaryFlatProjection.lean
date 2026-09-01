import Zeta23.CCM.BoundaryFlatFiniteSpace

noncomputable section

namespace Zeta23.CCM

open Complex
open scoped BigOperators

/-!
# F0-B1B: exact boundary-flat projection

This module theorem-locks an explicit projection from the full centered finite
Fourier coefficient sector onto the boundary-flat subspace introduced in
`BoundaryFlatFiniteSpace`.

For `N ≥ 1`, the reserved coordinate slots `N-1`, `N`, and `N+1`
represent centered indices `-1`, `0`, and `1`. We correct exactly those
three coefficients so that centered moments of orders 0, 1, and 2 vanish.

The module deliberately stops before density/approximation, continuity of the
genuine Weil form along a family, strict-sign transfer, F1, or RH.
-/

/-- Reserved coefficient index carrying centered Fourier mode `-1`. -/
def boundaryFlatNegOneIndex (N : ℕ) (hN : 1 ≤ N) : Fin (2 * N + 1) :=
  ⟨N - 1, by omega⟩

/-- Reserved coefficient index carrying centered Fourier mode `0`. -/
def boundaryFlatZeroIndex (N : ℕ) : Fin (2 * N + 1) :=
  ⟨N, by omega⟩

/-- Reserved coefficient index carrying centered Fourier mode `1`. -/
def boundaryFlatOneIndex (N : ℕ) (hN : 1 ≤ N) : Fin (2 * N + 1) :=
  ⟨N + 1, by omega⟩

@[simp] theorem centeredIndex_boundaryFlatNegOneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    centeredIndex N (boundaryFlatNegOneIndex N hN) = -1 := by
  simp [boundaryFlatNegOneIndex, centeredIndex]
  omega

@[simp] theorem centeredIndex_boundaryFlatZeroIndex
    (N : ℕ) :
    centeredIndex N (boundaryFlatZeroIndex N) = 0 := by
  simp [boundaryFlatZeroIndex, centeredIndex]

@[simp] theorem centeredIndex_boundaryFlatOneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    centeredIndex N (boundaryFlatOneIndex N hN) = 1 := by
  simp [boundaryFlatOneIndex, centeredIndex]

theorem boundaryFlatNegOneIndex_ne_zeroIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatNegOneIndex N hN ≠ boundaryFlatZeroIndex N := by
  intro h
  have hv := congrArg Fin.val h
  simp [boundaryFlatNegOneIndex, boundaryFlatZeroIndex] at hv
  omega

theorem boundaryFlatZeroIndex_ne_negOneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatZeroIndex N ≠ boundaryFlatNegOneIndex N hN :=
  Ne.symm (boundaryFlatNegOneIndex_ne_zeroIndex N hN)

theorem boundaryFlatNegOneIndex_ne_oneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatNegOneIndex N hN ≠ boundaryFlatOneIndex N hN := by
  intro h
  have hv := congrArg Fin.val h
  simp [boundaryFlatNegOneIndex, boundaryFlatOneIndex] at hv
  omega

theorem boundaryFlatOneIndex_ne_negOneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatOneIndex N hN ≠ boundaryFlatNegOneIndex N hN :=
  Ne.symm (boundaryFlatNegOneIndex_ne_oneIndex N hN)

theorem boundaryFlatZeroIndex_ne_oneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatZeroIndex N ≠ boundaryFlatOneIndex N hN := by
  intro h
  have hv := congrArg Fin.val h
  simp [boundaryFlatZeroIndex, boundaryFlatOneIndex] at hv

theorem boundaryFlatOneIndex_ne_zeroIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatOneIndex N hN ≠ boundaryFlatZeroIndex N :=
  Ne.symm (boundaryFlatZeroIndex_ne_oneIndex N hN)

/-- Single-coordinate coefficient vector. -/
def coefficientSingle
    {N : ℕ}
    (j : Fin (2 * N + 1)) (z : ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i => if i = j then z else 0

@[simp] theorem coefficientSingle_apply_self
    {N : ℕ} (j : Fin (2 * N + 1)) (z : ℂ) :
    coefficientSingle j z j = z := by
  simp [coefficientSingle]

@[simp] theorem coefficientSingle_apply_of_ne
    {N : ℕ} (j i : Fin (2 * N + 1)) (z : ℂ)
    (hij : i ≠ j) :
    coefficientSingle j z i = 0 := by
  simp [coefficientSingle, hij]

/-- Centered moments are additive in the coefficient vector. -/
theorem centeredMoment_add
    (N : ℕ) (k : ℕ)
    (u v : Fin (2 * N + 1) → ℂ) :
    centeredMoment N k (fun i => u i + v i) =
      centeredMoment N k u + centeredMoment N k v := by
  unfold centeredMoment
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

/-- Centered moment of a single-coordinate coefficient vector. -/
theorem centeredMoment_coefficientSingle
    (N : ℕ) (k : ℕ)
    (j : Fin (2 * N + 1)) (z : ℂ) :
    centeredMoment N k (coefficientSingle j z) =
      (centeredIndex N j : ℂ) ^ k * z := by
  classical
  unfold centeredMoment coefficientSingle
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [hbj]
  · simp

/-- Three-mode correction cancelling centered moments 0, 1, and 2. -/
def boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i =>
    coefficientSingle
      (boundaryFlatNegOneIndex N hN)
      ((centeredMoment N 1 u - centeredMoment N 2 u) / 2) i +
    coefficientSingle
      (boundaryFlatZeroIndex N)
      (centeredMoment N 2 u - centeredMoment N 0 u) i +
    coefficientSingle
      (boundaryFlatOneIndex N hN)
      (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) i

/-- Projection into the exact boundary-flat coefficient sector. -/
def boundaryFlatProject
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i => u i + boundaryFlatCorrection N hN u i

@[simp] theorem boundaryFlatCorrection_apply_negOne
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryFlatCorrection N hN u (boundaryFlatNegOneIndex N hN) =
      (centeredMoment N 1 u - centeredMoment N 2 u) / 2 := by
  simp [boundaryFlatCorrection,
    boundaryFlatNegOneIndex_ne_zeroIndex N hN,
    boundaryFlatNegOneIndex_ne_oneIndex N hN]

@[simp] theorem boundaryFlatCorrection_apply_zero
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryFlatCorrection N hN u (boundaryFlatZeroIndex N) =
      centeredMoment N 2 u - centeredMoment N 0 u := by
  simp [boundaryFlatCorrection,
    boundaryFlatZeroIndex_ne_negOneIndex N hN,
    boundaryFlatZeroIndex_ne_oneIndex N hN]

@[simp] theorem boundaryFlatCorrection_apply_one
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryFlatCorrection N hN u (boundaryFlatOneIndex N hN) =
      -(centeredMoment N 1 u + centeredMoment N 2 u) / 2 := by
  simp [boundaryFlatCorrection,
    boundaryFlatOneIndex_ne_negOneIndex N hN,
    boundaryFlatOneIndex_ne_zeroIndex N hN]

/-- Generic centered moment of the three-mode correction. -/
theorem centeredMoment_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) (k : ℕ) :
    centeredMoment N k (boundaryFlatCorrection N hN u) =
      ((-1 : ℂ) ^ k) *
          ((centeredMoment N 1 u - centeredMoment N 2 u) / 2) +
        ((0 : ℂ) ^ k) *
          (centeredMoment N 2 u - centeredMoment N 0 u) +
        ((1 : ℂ) ^ k) *
          (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) := by
  unfold boundaryFlatCorrection
  rw [centeredMoment_add]
  rw [centeredMoment_add]
  simp only [centeredMoment_coefficientSingle,
    centeredIndex_boundaryFlatNegOneIndex,
    centeredIndex_boundaryFlatZeroIndex,
    centeredIndex_boundaryFlatOneIndex]

theorem centeredMoment_zero_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 0 (boundaryFlatCorrection N hN u) =
      -centeredMoment N 0 u := by
  rw [centeredMoment_boundaryFlatCorrection N hN u 0]
  norm_num
  ring

theorem centeredMoment_one_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 1 (boundaryFlatCorrection N hN u) =
      -centeredMoment N 1 u := by
  rw [centeredMoment_boundaryFlatCorrection N hN u 1]
  norm_num
  ring

theorem centeredMoment_two_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 2 (boundaryFlatCorrection N hN u) =
      -centeredMoment N 2 u := by
  rw [centeredMoment_boundaryFlatCorrection N hN u 2]
  norm_num
  ring

/-- The exact projection always lands in the boundary-flat sector. -/
theorem boundaryFlatProject_boundaryFlat
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    BoundaryFlatCoefficients N (boundaryFlatProject N hN u) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show centeredMoment N 0 (boundaryFlatProject N hN u) =
        centeredMoment N 0 u +
          centeredMoment N 0 (boundaryFlatCorrection N hN u) by
      exact centeredMoment_add N 0 u (boundaryFlatCorrection N hN u)]
    rw [centeredMoment_zero_boundaryFlatCorrection]
    ring
  · rw [show centeredMoment N 1 (boundaryFlatProject N hN u) =
        centeredMoment N 1 u +
          centeredMoment N 1 (boundaryFlatCorrection N hN u) by
      exact centeredMoment_add N 1 u (boundaryFlatCorrection N hN u)]
    rw [centeredMoment_one_boundaryFlatCorrection]
    ring
  · rw [show centeredMoment N 2 (boundaryFlatProject N hN u) =
        centeredMoment N 2 u +
          centeredMoment N 2 (boundaryFlatCorrection N hN u) by
      exact centeredMoment_add N 2 u (boundaryFlatCorrection N hN u)]
    rw [centeredMoment_two_boundaryFlatCorrection]
    ring

/-- Boundary-flat vectors are fixed by the projection. -/
theorem boundaryFlatProject_eq_self_of_boundaryFlat
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    boundaryFlatProject N hN u = u := by
  funext i
  have h0 := hflat.1
  have h1 := hflat.2.1
  have h2 := hflat.2.2
  simp [boundaryFlatProject, boundaryFlatCorrection, h0, h1, h2]

/-- The projection is idempotent. -/
theorem boundaryFlatProject_idempotent
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryFlatProject N hN (boundaryFlatProject N hN u) =
      boundaryFlatProject N hN u :=
  boundaryFlatProject_eq_self_of_boundaryFlat
    N hN _ (boundaryFlatProject_boundaryFlat N hN u)

/-- Exact left-endpoint value in terms of centered moment zero. -/
theorem localizedFiniteFunction_zero_eq_centeredMoment_zero
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteFunction L N u 0 =
      ((1 / Real.sqrt L : ℝ) : ℂ) * centeredMoment N 0 u := by
  unfold localizedFiniteFunction centeredMoment
  simp_rw [localizedMode_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact left-endpoint first jet in terms of centered moment one. -/
theorem localizedFiniteFirstJet_zero_eq_centeredMoment_one
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteFirstJet L N u 0 =
      (localizedBaseFrequency L * ((1 / Real.sqrt L : ℝ) : ℂ)) *
        centeredMoment N 1 u := by
  unfold localizedFiniteFirstJet localizedFrequency centeredMoment
  simp_rw [localizedMode_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact left-endpoint second jet in terms of centered moment two. -/
theorem localizedFiniteSecondJet_zero_eq_centeredMoment_two
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteSecondJet L N u 0 =
      (localizedBaseFrequency L ^ 2 * ((1 / Real.sqrt L : ℝ) : ℂ)) *
        centeredMoment N 2 u := by
  unfold localizedFiniteSecondJet localizedFrequency centeredMoment
  simp_rw [localizedMode_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.boundaryFlatProject_boundaryFlat
#print axioms Zeta23.CCM.boundaryFlatProject_eq_self_of_boundaryFlat
#print axioms Zeta23.CCM.boundaryFlatProject_idempotent
#print axioms Zeta23.CCM.localizedFiniteFunction_zero_eq_centeredMoment_zero
#print axioms Zeta23.CCM.localizedFiniteFirstJet_zero_eq_centeredMoment_one
#print axioms Zeta23.CCM.localizedFiniteSecondJet_zero_eq_centeredMoment_two
