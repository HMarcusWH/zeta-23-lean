import Zeta23.CCM.CrossParityQuotientTransport

noncomputable section

namespace Zeta23.CCM

open Matrix Set Finset
open scoped BigOperators ComplexConjugate

/-!
# Cross-parity cubic correction collapse

The post-#223 exact-algebra audit exposed that the two odd predecessor
corrections used by the centered-index transport and by the cubic generator
are not independent.  This module proves that relation in the native finite
geometry before composing it with any aperture, source matrix, first-bad
certificate, or RH-directed assumption.
-/

private theorem sum_range_pow_one_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 1) =
      (m : ℚ) * (m - 1 : ℚ) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_pow_two_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 2) =
      (m : ℚ) * (m - 1 : ℚ) * (2 * m - 1 : ℚ) / 6 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_pow_three_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 3) =
      ((m : ℚ) * (m - 1 : ℚ) / 2) ^ 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_pow_four_rat (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℚ) ^ 4) =
      (m : ℚ) * (m - 1 : ℚ) * (2 * m - 1 : ℚ) *
        (3 * m ^ 2 - 3 * m - 1 : ℚ) / 30 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem centered_square_sum_rat (N : ℕ) :
    (∑ i : Fin (2 * N + 1),
        (((i.1 : ℚ) - (N : ℚ)) ^ 2)) =
      (N : ℚ) * (N + 1 : ℚ) * (2 * N + 1 : ℚ) / 3 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (((k : ℚ) - (N : ℚ)) ^ 2))]
  have hsum :
      (∑ k ∈ Finset.range (2 * N + 1),
          (((k : ℚ) - (N : ℚ)) ^ 2)) =
        (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 2) -
          2 * (N : ℚ) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) +
          ((2 * N + 1 : ℕ) : ℚ) * (N : ℚ) ^ 2 := by
    calc
      (∑ k ∈ Finset.range (2 * N + 1),
          (((k : ℚ) - (N : ℚ)) ^ 2)) =
        ∑ k ∈ Finset.range (2 * N + 1),
          ((k : ℚ) ^ 2 - 2 * (N : ℚ) * (k : ℚ) + (N : ℚ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ =
        (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 2) -
          2 * (N : ℚ) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) +
          ((2 * N + 1 : ℕ) : ℚ) * (N : ℚ) ^ 2 := by
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
            simp
            ring
  rw [hsum, sum_range_pow_two_rat]
  have hone :
      (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) =
        ∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 1 := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hone, sum_range_pow_one_rat]
  push_cast
  ring

private theorem centered_fourth_sum_rat (N : ℕ) :
    (∑ i : Fin (2 * N + 1),
        (((i.1 : ℚ) - (N : ℚ)) ^ 4)) =
      (N : ℚ) * (N + 1 : ℚ) * (2 * N + 1 : ℚ) *
        (3 * N ^ 2 + 3 * N - 1 : ℚ) / 15 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (((k : ℚ) - (N : ℚ)) ^ 4))]
  have hsum :
      (∑ k ∈ Finset.range (2 * N + 1),
          (((k : ℚ) - (N : ℚ)) ^ 4)) =
        (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 4) -
          4 * (N : ℚ) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 3) +
          6 * (N : ℚ) ^ 2 *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 2) -
          4 * (N : ℚ) ^ 3 *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) +
          ((2 * N + 1 : ℕ) : ℚ) * (N : ℚ) ^ 4 := by
    calc
      (∑ k ∈ Finset.range (2 * N + 1),
          (((k : ℚ) - (N : ℚ)) ^ 4)) =
        ∑ k ∈ Finset.range (2 * N + 1),
          ((k : ℚ) ^ 4 -
            4 * (N : ℚ) * (k : ℚ) ^ 3 +
            6 * (N : ℚ) ^ 2 * (k : ℚ) ^ 2 -
            4 * (N : ℚ) ^ 3 * (k : ℚ) +
            (N : ℚ) ^ 4) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ =
        (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 4) -
          4 * (N : ℚ) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 3) +
          6 * (N : ℚ) ^ 2 *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 2) -
          4 * (N : ℚ) ^ 3 *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) +
          ((2 * N + 1 : ℕ) : ℚ) * (N : ℚ) ^ 4 := by
              simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum]
              simp
              ring
  rw [hsum, sum_range_pow_four_rat, sum_range_pow_three_rat,
    sum_range_pow_two_rat]
  have hone :
      (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) =
        ∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 1 := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hone, sum_range_pow_one_rat]
  push_cast
  ring

private theorem centered_square_sum_complex (N : ℕ) :
    (∑ i : Fin (2 * N + 1), (centeredIndex N i : ℂ) ^ 2) =
      ((N : ℂ) * (N + 1 : ℂ) * (2 * N + 1 : ℂ)) / 3 := by
  have h := congrArg (fun x : ℚ => (x : ℂ)) (centered_square_sum_rat N)
  simpa [centeredIndex] using h

private theorem centered_fourth_sum_complex (N : ℕ) :
    (∑ i : Fin (2 * N + 1), (centeredIndex N i : ℂ) ^ 4) =
      ((N : ℂ) * (N + 1 : ℂ) * (2 * N + 1 : ℂ) *
        (3 * (N : ℂ) ^ 2 + 3 * N - 1)) / 15 := by
  have h := congrArg (fun x : ℚ => (x : ℂ)) (centered_fourth_sum_rat N)
  simpa [centeredIndex] using h

/-- Closed coefficient of the residual removed by the odd cubic projection. -/
def oddCubicProjectionSlope (K : ℕ) : ℂ :=
  (3 * (K : ℂ) ^ 2 + 3 * K - 1) / 5

private theorem centeredMoment_one_centeredPowerVector_one (K : ℕ) :
    centeredMoment K 1
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (centeredPowerVector K 1)) =
      ∑ i : Fin (2 * K + 1), (centeredIndex K i : ℂ) ^ 2 := by
  unfold centeredMoment
  apply Finset.sum_congr rfl
  intro i _
  simp [centeredPowerVector_apply, pow_succ]

private theorem centeredMoment_one_centeredPowerVector_three (K : ℕ) :
    centeredMoment K 1
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (centeredPowerVector K 3)) =
      ∑ i : Fin (2 * K + 1), (centeredIndex K i : ℂ) ^ 4 := by
  unfold centeredMoment
  apply Finset.sum_congr rfl
  intro i _
  simp [centeredPowerVector_apply, pow_succ]
  ring

/-- The exact odd cubic compression is raw `d^3` minus the closed
centered-grid slope times `d`. -/
theorem cubicProjectionResidual_eq_oddCubicProjectionSlope_smul
    (K : ℕ) (hK : 1 ≤ K) :
    centeredPowerVector K 3 -
        ((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
          EuclideanSpace ℂ (Fin (2 * K + 1))) =
      oddCubicProjectionSlope K • centeredPowerVector K 1 := by
  have hnormal := cubicProjectionResidual_mem_oddNormalSubspace K
  rw [oddNormalSubspace, Submodule.mem_span_singleton] at hnormal
  rcases hnormal with ⟨a, ha⟩

  have hgFlat :
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))) ∈
        boundaryFlatSubspace K := by
    exact
      ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp
        (oddCubicCompressionVector K).property).1
  have hgMoment :
      centeredMoment K 1
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
            (((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
              EuclideanSpace ℂ (Fin (2 * K + 1))))) = 0 :=
    ((mem_boundaryFlatSubspace_iff K _).mp hgFlat).2.1

  have hgInner :
      inner ℂ (centeredPowerVector K 1)
          (((oddCubicCompressionVector K : euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))) = 0 := by
    rw [inner_centeredPowerVector]
    exact hgMoment

  have hpair := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) =>
      inner ℂ (centeredPowerVector K 1) x) ha
  rw [inner_smul_right, inner_sub_right, hgInner, sub_zero,
    inner_centeredPowerVector, inner_centeredPowerVector,
    centeredMoment_one_centeredPowerVector_three,
    centeredMoment_one_centeredPowerVector_one,
    centered_fourth_sum_complex,
    centered_square_sum_complex] at hpair
  have hK0 : (K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK)
  have hK1 : (K : ℂ) + 1 ≠ 0 := by
    have : (K : ℂ) + 1 = ((K + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero K
  have h2K1 : 2 * (K : ℂ) + 1 ≠ 0 := by
    have hnat : 2 * K + 1 ≠ 0 := by omega
    have : 2 * (K : ℂ) + 1 = ((2 * K + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast hnat
  have hS2 :
      ((K : ℂ) * (K + 1 : ℂ) * (2 * K + 1 : ℂ)) / 3 ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero hK0 hK1) h2K1
    · norm_num

  have haCoeff : a = oddCubicProjectionSlope K := by
    apply (mul_right_cancel₀ hS2)
    rw [hpair]
    unfold oddCubicProjectionSlope
    field_simp
    ring

  simpa [haCoeff] using ha

end Zeta23.CCM
