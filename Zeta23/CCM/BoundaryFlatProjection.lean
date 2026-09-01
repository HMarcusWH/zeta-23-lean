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
represent centered indices `-1`, `0`, and `1`.  We correct exactly those
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
def boundaryFlatOneIndex (N : ℕ) : Fin (2 * N + 1) :=
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
    (N : ℕ) :
    centeredIndex N (boundaryFlatOneIndex N) = 1 := by
  simp [boundaryFlatOneIndex, centeredIndex]

theorem boundaryFlatNegOneIndex_ne_zeroIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatNegOneIndex N hN ≠ boundaryFlatZeroIndex N := by
  intro h
  have := congrArg Fin.val h
  simp [boundaryFlatNegOneIndex, boundaryFlatZeroIndex] at this
  omega

theorem boundaryFlatNegOneIndex_ne_oneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatNegOneIndex N hN ≠ boundaryFlatOneIndex N := by
  intro h
  have := congrArg Fin.val h
  simp [boundaryFlatNegOneIndex, boundaryFlatOneIndex] at this
  omega

theorem boundaryFlatZeroIndex_ne_oneIndex
    (N : ℕ) :
    boundaryFlatZeroIndex N ≠ boundaryFlatOneIndex N := by
  intro h
  have := congrArg Fin.val h
  simp [boundaryFlatZeroIndex, boundaryFlatOneIndex] at this

/-- Three-mode correction cancelling centered moments 0, 1, and 2.

If `m_k = centeredMoment N k u`, the correction values are
`(m₁-m₂)/2` at mode `-1`, `m₂-m₀` at mode `0`, and
`-(m₁+m₂)/2` at mode `1`.
-/
def boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i =>
    if i = boundaryFlatNegOneIndex N hN then
      (centeredMoment N 1 u - centeredMoment N 2 u) / 2
    else if i = boundaryFlatZeroIndex N then
      centeredMoment N 2 u - centeredMoment N 0 u
    else if i = boundaryFlatOneIndex N then
      -(centeredMoment N 1 u + centeredMoment N 2 u) / 2
    else
      0

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
  simp [boundaryFlatCorrection]

@[simp] theorem boundaryFlatCorrection_apply_zero
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryFlatCorrection N hN u (boundaryFlatZeroIndex N) =
      centeredMoment N 2 u - centeredMoment N 0 u := by
  simp [boundaryFlatCorrection, boundaryFlatNegOneIndex_ne_zeroIndex N hN]

@[simp] theorem boundaryFlatCorrection_apply_one
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    boundaryFlatCorrection N hN u (boundaryFlatOneIndex N) =
      -(centeredMoment N 1 u + centeredMoment N 2 u) / 2 := by
  simp [boundaryFlatCorrection,
    boundaryFlatNegOneIndex_ne_oneIndex N hN,
    boundaryFlatZeroIndex_ne_oneIndex N]

/-- A correction coefficient vanishes away from the three reserved modes. -/
theorem boundaryFlatCorrection_eq_zero_of_other
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (i : Fin (2 * N + 1))
    (hneg : i ≠ boundaryFlatNegOneIndex N hN)
    (hzero : i ≠ boundaryFlatZeroIndex N)
    (hone : i ≠ boundaryFlatOneIndex N) :
    boundaryFlatCorrection N hN u i = 0 := by
  simp [boundaryFlatCorrection, hneg, hzero, hone]

/-- Moment zero of the correction is exactly the negative original moment. -/
theorem centeredMoment_zero_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 0 (boundaryFlatCorrection N hN u) =
      -centeredMoment N 0 u := by
  classical
  unfold centeredMoment
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ)
    (a := boundaryFlatNegOneIndex N hN) (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ.erase (boundaryFlatNegOneIndex N hN))
    (a := boundaryFlatZeroIndex N)]
  · rw [Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ.erase (boundaryFlatNegOneIndex N hN)).erase
        (boundaryFlatZeroIndex N))
      (a := boundaryFlatOneIndex N)]
    · have hrest :
        ∑ x ∈ (((Finset.univ.erase (boundaryFlatNegOneIndex N hN)).erase
          (boundaryFlatZeroIndex N)).erase (boundaryFlatOneIndex N)),
          (centeredIndex N x : ℂ) ^ 0 * boundaryFlatCorrection N hN u x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hneg : i ≠ boundaryFlatNegOneIndex N hN := by
          exact Finset.ne_of_mem_erase hi
        have hzero : i ≠ boundaryFlatZeroIndex N := by
          exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hone : i ≠ boundaryFlatOneIndex N := by
          exact Finset.ne_of_mem_erase hi
        simp [boundaryFlatCorrection_eq_zero_of_other N hN u i hneg hzero hone]
      rw [hrest]
      simp
      ring
    · simp [boundaryFlatNegOneIndex_ne_oneIndex N hN,
        boundaryFlatZeroIndex_ne_oneIndex N]
  · simp [boundaryFlatNegOneIndex_ne_zeroIndex N hN]

/-- Moment one of the correction is exactly the negative original moment. -/
theorem centeredMoment_one_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 1 (boundaryFlatCorrection N hN u) =
      -centeredMoment N 1 u := by
  classical
  unfold centeredMoment
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ)
    (a := boundaryFlatNegOneIndex N hN) (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ.erase (boundaryFlatNegOneIndex N hN))
    (a := boundaryFlatZeroIndex N)]
  · rw [Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ.erase (boundaryFlatNegOneIndex N hN)).erase
        (boundaryFlatZeroIndex N))
      (a := boundaryFlatOneIndex N)]
    · have hrest :
        ∑ x ∈ (((Finset.univ.erase (boundaryFlatNegOneIndex N hN)).erase
          (boundaryFlatZeroIndex N)).erase (boundaryFlatOneIndex N)),
          (centeredIndex N x : ℂ) ^ 1 * boundaryFlatCorrection N hN u x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hneg : i ≠ boundaryFlatNegOneIndex N hN := by
          exact Finset.ne_of_mem_erase hi
        have hzero : i ≠ boundaryFlatZeroIndex N := by
          exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hone : i ≠ boundaryFlatOneIndex N := by
          exact Finset.ne_of_mem_erase hi
        simp [boundaryFlatCorrection_eq_zero_of_other N hN u i hneg hzero hone]
      rw [hrest]
      simp
      ring
    · simp [boundaryFlatNegOneIndex_ne_oneIndex N hN,
        boundaryFlatZeroIndex_ne_oneIndex N]
  · simp [boundaryFlatNegOneIndex_ne_zeroIndex N hN]

/-- Moment two of the correction is exactly the negative original moment. -/
theorem centeredMoment_two_boundaryFlatCorrection
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N 2 (boundaryFlatCorrection N hN u) =
      -centeredMoment N 2 u := by
  classical
  unfold centeredMoment
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ)
    (a := boundaryFlatNegOneIndex N hN) (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ.erase (boundaryFlatNegOneIndex N hN))
    (a := boundaryFlatZeroIndex N)]
  · rw [Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ.erase (boundaryFlatNegOneIndex N hN)).erase
        (boundaryFlatZeroIndex N))
      (a := boundaryFlatOneIndex N)]
    · have hrest :
        ∑ x ∈ (((Finset.univ.erase (boundaryFlatNegOneIndex N hN)).erase
          (boundaryFlatZeroIndex N)).erase (boundaryFlatOneIndex N)),
          (centeredIndex N x : ℂ) ^ 2 * boundaryFlatCorrection N hN u x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hneg : i ≠ boundaryFlatNegOneIndex N hN := by
          exact Finset.ne_of_mem_erase hi
        have hzero : i ≠ boundaryFlatZeroIndex N := by
          exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hone : i ≠ boundaryFlatOneIndex N := by
          exact Finset.ne_of_mem_erase hi
        simp [boundaryFlatCorrection_eq_zero_of_other N hN u i hneg hzero hone]
      rw [hrest]
      simp
      ring
    · simp [boundaryFlatNegOneIndex_ne_oneIndex N hN,
        boundaryFlatZeroIndex_ne_oneIndex N]
  · simp [boundaryFlatNegOneIndex_ne_zeroIndex N hN]

/-- The exact projection always lands in the boundary-flat sector. -/
theorem boundaryFlatProject_boundaryFlat
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ) :
    BoundaryFlatCoefficients N (boundaryFlatProject N hN u) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold centeredMoment boundaryFlatProject
    rw [Finset.sum_add_distrib, centeredMoment_zero_boundaryFlatCorrection]
    ring
  · unfold centeredMoment boundaryFlatProject
    rw [Finset.sum_add_distrib, centeredMoment_one_boundaryFlatCorrection]
    ring
  · unfold centeredMoment boundaryFlatProject
    rw [Finset.sum_add_distrib, centeredMoment_two_boundaryFlatCorrection]
    ring

/-- Boundary-flat vectors are fixed by the projection. -/
theorem boundaryFlatProject_eq_self_of_boundaryFlat
    (N : ℕ) (hN : 1 ≤ N)
    (u : Fin (2 * N + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients N u) :
    boundaryFlatProject N hN u = u := by
  funext i
  unfold boundaryFlatProject boundaryFlatCorrection
  have h0 := hflat.1
  have h1 := hflat.2.1
  have h2 := hflat.2.2
  simp [h0, h1, h2]

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
#print axioms Zeta23.CCM.localizedFiniteFunction_zero_eq_centeredMoment_zero
#print axioms Zeta23.CCM.localizedFiniteFirstJet_zero_eq_centeredMoment_one
#print axioms Zeta23.CCM.localizedFiniteSecondJet_zero_eq_centeredMoment_two
