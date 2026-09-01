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
  have hv := congrArg Fin.val h
  simp [boundaryFlatNegOneIndex, boundaryFlatZeroIndex] at hv
  omega

theorem boundaryFlatNegOneIndex_ne_oneIndex
    (N : ℕ) (hN : 1 ≤ N) :
    boundaryFlatNegOneIndex N hN ≠ boundaryFlatOneIndex N := by
  intro h
  have hv := congrArg Fin.val h
  simp [boundaryFlatNegOneIndex, boundaryFlatOneIndex] at hv
  omega

theorem boundaryFlatZeroIndex_ne_oneIndex
    (N : ℕ) :
    boundaryFlatZeroIndex N ≠ boundaryFlatOneIndex N := by
  intro h
  have hv := congrArg Fin.val h
  simp [boundaryFlatZeroIndex, boundaryFlatOneIndex] at hv

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
  classical
  unfold centeredMoment
  let a := boundaryFlatNegOneIndex N hN
  let b := boundaryFlatZeroIndex N
  let c := boundaryFlatOneIndex N
  have hab : a ≠ b := boundaryFlatNegOneIndex_ne_zeroIndex N hN
  have hac : a ≠ c := boundaryFlatNegOneIndex_ne_oneIndex N hN
  have hbc : b ≠ c := boundaryFlatZeroIndex_ne_oneIndex N
  calc
    ∑ i, (centeredIndex N i : ℂ) ^ k * boundaryFlatCorrection N hN u i =
        (centeredIndex N a : ℂ) ^ k * boundaryFlatCorrection N hN u a +
        ∑ i ∈ Finset.univ.erase a,
          (centeredIndex N i : ℂ) ^ k * boundaryFlatCorrection N hN u i := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
            ring
    _ =
        (centeredIndex N a : ℂ) ^ k * boundaryFlatCorrection N hN u a +
        ((centeredIndex N b : ℂ) ^ k * boundaryFlatCorrection N hN u b +
        ∑ i ∈ (Finset.univ.erase a).erase b,
          (centeredIndex N i : ℂ) ^ k * boundaryFlatCorrection N hN u i) := by
            rw [← Finset.sum_erase_add _ _]
            · ring
            · simp [hab]
    _ =
        (centeredIndex N a : ℂ) ^ k * boundaryFlatCorrection N hN u a +
        ((centeredIndex N b : ℂ) ^ k * boundaryFlatCorrection N hN u b +
        ((centeredIndex N c : ℂ) ^ k * boundaryFlatCorrection N hN u c +
        ∑ i ∈ ((Finset.univ.erase a).erase b).erase c,
          (centeredIndex N i : ℂ) ^ k * boundaryFlatCorrection N hN u i)) := by
            rw [← Finset.sum_erase_add _ _]
            · ring
            · simp [hac, hbc]
    _ =
        (centeredIndex N a : ℂ) ^ k * boundaryFlatCorrection N hN u a +
        ((centeredIndex N b : ℂ) ^ k * boundaryFlatCorrection N hN u b +
        ((centeredIndex N c : ℂ) ^ k * boundaryFlatCorrection N hN u c + 0)) := by
            congr 1
            congr 1
            congr 1
            apply Finset.sum_eq_zero
            intro i hi
            have hia : i ≠ a := by
              exact Finset.ne_of_mem_erase
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
            have hib : i ≠ b := by
              exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
            have hic : i ≠ c := Finset.ne_of_mem_erase hi
            rw [boundaryFlatCorrection_eq_zero_of_other N hN u i hia hib hic]
            simp
    _ =
      ((-1 : ℂ) ^ k) *
          ((centeredMoment N 1 u - centeredMoment N 2 u) / 2) +
        ((0 : ℂ) ^ k) *
          (centeredMoment N 2 u - centeredMoment N 0 u) +
        ((1 : ℂ) ^ k) *
          (-(centeredMoment N 1 u + centeredMoment N 2 u) / 2) := by
            simp [a, b, c]
            ring

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
#print axioms Zeta23.CCM.boundaryFlatProject_idempotent
#print axioms Zeta23.CCM.localizedFiniteFunction_zero_eq_centeredMoment_zero
#print axioms Zeta23.CCM.localizedFiniteFirstJet_zero_eq_centeredMoment_one
#print axioms Zeta23.CCM.localizedFiniteSecondJet_zero_eq_centeredMoment_two
