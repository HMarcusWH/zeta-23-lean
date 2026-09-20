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
          ((k : ℚ) ^ 4 +
            (-4 * (N : ℚ)) * (k : ℚ) ^ 3 +
            (6 * (N : ℚ) ^ 2) * (k : ℚ) ^ 2 +
            (-4 * (N : ℚ) ^ 3) * (k : ℚ) +
            (N : ℚ) ^ 4) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ =
        (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 4) +
          (-4 * (N : ℚ)) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 3) +
          (6 * (N : ℚ) ^ 2) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 2) +
          (-4 * (N : ℚ) ^ 3) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) +
          ((2 * N + 1 : ℕ) : ℚ) * (N : ℚ) ^ 4 := by
              simp_rw [Finset.sum_add_distrib]
              simp_rw [← Finset.mul_sum]
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ =
        (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 4) -
          4 * (N : ℚ) *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 3) +
          6 * (N : ℚ) ^ 2 *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ) ^ 2) -
          4 * (N : ℚ) ^ 3 *
            (∑ k ∈ Finset.range (2 * N + 1), (k : ℚ)) +
          ((2 * N + 1 : ℕ) : ℚ) * (N : ℚ) ^ 4 := by
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
    push_cast
    ring

  simpa [haCoeff] using ha.symm


/-!
## Exact one-step predecessor correction

The closed odd cubic projection coefficient above determines the remaining
one-step cross-parity predecessor correction exactly. The proof uses only the
native centered embedding, shell orthogonality, and the already-identified
even/odd normal spaces.
-/

/-- Scalar relating the two odd predecessor corrections at one centered
successor step. The coefficient is stated directly in complex scalars so no
natural subtraction or division can enter downstream rewrites. -/
def crossParityCubicCorrectionKappa (N : ℕ) : ℂ :=
  (2 * (N : ℂ) - 1) / 6

/-- Restriction of a successor-grid Euclidean vector to the centered
predecessor coordinates. -/
private def oneStepCenteredRestrict
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) :
    EuclideanSpace ℂ (Fin (2 * N + 1)) :=
  (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm
    (fun i => x (centeredEmbedding N (N + 1) (Nat.le_succ N) i))

@[simp] private theorem oneStepCenteredRestrict_apply
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
    (i : Fin (2 * N + 1)) :
    oneStepCenteredRestrict N x i =
      x (centeredEmbedding N (N + 1) (Nat.le_succ N) i) := by
  rfl

private def successorLeftOuterIndex
    (N : ℕ) : Fin (2 * (N + 1) + 1) :=
  ⟨0, by omega⟩

@[simp] private theorem centeredIndex_successorLeftOuterIndex
    (N : ℕ) :
    centeredIndex (N + 1) (successorLeftOuterIndex N) =
      -(N + 1 : ℤ) := by
  simp [successorLeftOuterIndex, centeredIndex]

@[simp] private theorem successorRightOuterIndex_rev
    (N : ℕ) :
    (successorRightOuterIndex N).rev = successorLeftOuterIndex N := by
  apply Fin.ext
  simp [successorRightOuterIndex, successorLeftOuterIndex]

private theorem successorLeftOuterIndex_not_mem_centeredEmbedding_range
    (N : ℕ) :
    successorLeftOuterIndex N ∉
      Set.range (centeredEmbedding N (N + 1) (Nat.le_succ N)) := by
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  simp [successorLeftOuterIndex, centeredEmbedding] at hval

private theorem euclideanCenteredZeroExtend_succ_leftOuter_eq_zero
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    euclideanCenteredZeroExtend (Nat.le_succ N) x
        (successorLeftOuterIndex N) = 0 := by
  exact euclideanCenteredZeroExtendLinearMap_apply_of_not_mem_range
    (Nat.le_succ N) x (successorLeftOuterIndex N)
      (successorLeftOuterIndex_not_mem_centeredEmbedding_range N)

private theorem sum_oneStepCentered_split
    (N : ℕ)
    (f : Fin (2 * (N + 1) + 1) → ℂ) :
    (∑ j, f j) =
      f (successorLeftOuterIndex N) +
        ((∑ i : Fin (2 * N + 1),
            f (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) +
          f (successorRightOuterIndex N)) := by
  have houter := Fin.sum_univ_succ f
  have hinner :=
    Fin.sum_univ_castSucc
      (fun i : Fin (2 * N + 2) => f i.succ)
  have hmiddle :
      (∑ i : Fin (2 * N + 1), f i.castSucc.succ) =
        ∑ i : Fin (2 * N + 1),
          f (centeredEmbedding N (N + 1) (Nat.le_succ N) i) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [centeredEmbedding]
  have hright :
      (Fin.last (2 * N + 1)).succ = successorRightOuterIndex N := by
    apply Fin.ext
    simp [successorRightOuterIndex]
    omega
  calc
    (∑ j, f j) =
        f 0 + ∑ i : Fin (2 * N + 2), f i.succ := by
      exact houter
    _ =
        f 0 +
          ((∑ i : Fin (2 * N + 1), f i.castSucc.succ) +
            f (Fin.last (2 * N + 1)).succ) := by
      exact congrArg (fun t => f 0 + t) hinner
    _ =
        f (successorLeftOuterIndex N) +
          ((∑ i : Fin (2 * N + 1),
              f (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) +
            f (successorRightOuterIndex N)) := by
      rw [hmiddle, hright]
      rfl

private theorem inner_oneStepCenteredRestrict
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
    (y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) :
    inner ℂ x (oneStepCenteredRestrict N y) =
      inner ℂ (euclideanCenteredZeroExtend (Nat.le_succ N) x) y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [Fintype.sum_of_injective
    (centeredEmbedding N (N + 1) (Nat.le_succ N))
    (centeredEmbedding N (N + 1) (Nat.le_succ N)).injective
    (fun i : Fin (2 * N + 1) =>
      inner ℂ (x i) ((oneStepCenteredRestrict N y) i))
    (fun j : Fin (2 * (N + 1) + 1) =>
      inner ℂ
        ((euclideanCenteredZeroExtend (Nat.le_succ N) x) j)
        (y j))]
  · intro j hj
    have hzero :
        (euclideanCenteredZeroExtend (Nat.le_succ N) x) j = 0 := by
      exact euclideanCenteredZeroExtendLinearMap_apply_of_not_mem_range
        (Nat.le_succ N) x j (by simpa using hj)
    rw [hzero]
    simp
  · intro i
    simp [oneStepCenteredRestrict_apply]

private theorem oneStepCenteredRestrict_mem_evenCoefficient
    (N : ℕ)
    {y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))}
    (hy : y ∈ euclideanEvenCoefficientSubspace (N + 1)) :
    oneStepCenteredRestrict N y ∈ euclideanEvenCoefficientSubspace N := by
  rw [mem_euclideanEvenCoefficientSubspace_iff]
  apply (mem_evenCoefficientSubspace_iff N _).2
  have hyRaw :
      (EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ) y ∈
        evenCoefficientSubspace (N + 1) :=
    (mem_euclideanEvenCoefficientSubspace_iff (N + 1) y).mp hy
  have hyRev :=
    (mem_evenCoefficientSubspace_iff (N + 1) _).mp hyRaw
  ext i
  have hi := congrFun hyRev
    (centeredEmbedding N (N + 1) (Nat.le_succ N) i)
  simp only [reverseCoefficients] at hi ⊢
  simpa [oneStepCenteredRestrict_apply,
    centeredEmbedding_rev N (N + 1) (Nat.le_succ N) i] using hi

private theorem oneStepCenteredRestrict_mem_oddCoefficient
    (N : ℕ)
    {y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))}
    (hy : y ∈ euclideanOddCoefficientSubspace (N + 1)) :
    oneStepCenteredRestrict N y ∈ euclideanOddCoefficientSubspace N := by
  rw [mem_euclideanOddCoefficientSubspace_iff]
  apply (mem_oddCoefficientSubspace_iff N _).2
  have hyRaw :
      (EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ) y ∈
        oddCoefficientSubspace (N + 1) :=
    (mem_euclideanOddCoefficientSubspace_iff (N + 1) y).mp hy
  have hyRev :=
    (mem_oddCoefficientSubspace_iff (N + 1) _).mp hyRaw
  ext i
  have hi := congrFun hyRev
    (centeredEmbedding N (N + 1) (Nat.le_succ N) i)
  simp only [reverseCoefficients, Pi.neg_apply] at hi ⊢
  simpa [oneStepCenteredRestrict_apply,
    centeredEmbedding_rev N (N + 1) (Nat.le_succ N) i] using hi

private theorem oneStepCenteredRestrict_evenShell_mem_normal
    (N : ℕ)
    (s : intrinsicParitySuccShell .even N) :
    oneStepCenteredRestrict N
        ((s : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
      evenNormalSubspace N := by
  let y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) :=
    ((s : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  have hsAmbient := s.property
  change y ∈
      (euclideanParityEmbeddedSuccSubspace .even N)ᗮ ⊓
        euclideanParityBoundaryFlatSubspace .even (N + 1) at hsAmbient
  have hyOrth : y ∈ (euclideanParityEmbeddedSuccSubspace .even N)ᗮ :=
    hsAmbient.1
  have hyCoeff :
      y ∈ euclideanEvenCoefficientSubspace (N + 1) := by
    have h :=
      euclideanParityBoundaryFlatSubspace_le_coefficientSubspace
        .even (N + 1) hsAmbient.2
    simpa [euclideanParityCoefficientSubspace] using h
  have hrOrth :
      oneStepCenteredRestrict N y ∈
        (euclideanEvenBoundaryFlatSubspace N)ᗮ := by
    rw [(euclideanEvenBoundaryFlatSubspace N).mem_orthogonal]
    intro x hx
    rw [inner_oneStepCenteredRestrict]
    have hxEmb :
        euclideanCenteredZeroExtend (Nat.le_succ N) x ∈
          euclideanParityEmbeddedSuccSubspace .even N := by
      exact ⟨x, hx, rfl⟩
    exact
      ((euclideanParityEmbeddedSuccSubspace .even N).mem_orthogonal y).mp
        hyOrth _ hxEmb
  have hrEven :
      oneStepCenteredRestrict N y ∈
        euclideanEvenCoefficientSubspace N :=
    oneStepCenteredRestrict_mem_evenCoefficient N hyCoeff
  have hi :
      oneStepCenteredRestrict N y ∈
        (euclideanEvenBoundaryFlatSubspace N)ᗮ ⊓
          euclideanEvenCoefficientSubspace N :=
    ⟨hrOrth, hrEven⟩
  rw [evenBoundaryFlat_normal_eq_evenNormalSubspace N] at hi
  exact hi

private theorem oneStepCenteredRestrict_oddShell_mem_normal
    (N : ℕ)
    (s : intrinsicParitySuccShell .odd N) :
    oneStepCenteredRestrict N
        ((s : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
      oddNormalSubspace N := by
  let y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) :=
    ((s : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  have hsAmbient := s.property
  change y ∈
      (euclideanParityEmbeddedSuccSubspace .odd N)ᗮ ⊓
        euclideanParityBoundaryFlatSubspace .odd (N + 1) at hsAmbient
  have hyOrth : y ∈ (euclideanParityEmbeddedSuccSubspace .odd N)ᗮ :=
    hsAmbient.1
  have hyCoeff :
      y ∈ euclideanOddCoefficientSubspace (N + 1) := by
    have h :=
      euclideanParityBoundaryFlatSubspace_le_coefficientSubspace
        .odd (N + 1) hsAmbient.2
    simpa [euclideanParityCoefficientSubspace] using h
  have hrOrth :
      oneStepCenteredRestrict N y ∈
        (euclideanOddBoundaryFlatSubspace N)ᗮ := by
    rw [(euclideanOddBoundaryFlatSubspace N).mem_orthogonal]
    intro x hx
    rw [inner_oneStepCenteredRestrict]
    have hxEmb :
        euclideanCenteredZeroExtend (Nat.le_succ N) x ∈
          euclideanParityEmbeddedSuccSubspace .odd N := by
      exact ⟨x, hx, rfl⟩
    exact
      ((euclideanParityEmbeddedSuccSubspace .odd N).mem_orthogonal y).mp
        hyOrth _ hxEmb
  have hrOdd :
      oneStepCenteredRestrict N y ∈
        euclideanOddCoefficientSubspace N :=
    oneStepCenteredRestrict_mem_oddCoefficient N hyCoeff
  have hi :
      oneStepCenteredRestrict N y ∈
        (euclideanOddBoundaryFlatSubspace N)ᗮ ⊓
          euclideanOddCoefficientSubspace N :=
    ⟨hrOrth, hrOdd⟩
  rw [oddBoundaryFlat_normal_eq_oddNormalSubspace N] at hi
  exact hi

private theorem centeredMoment_zero_successor_split
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) :
    centeredMoment (N + 1) 0
        ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ) x) =
      centeredMoment N 0
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
            (oneStepCenteredRestrict N x)) +
        x (successorLeftOuterIndex N) +
        x (successorRightOuterIndex N) := by
  have h := sum_oneStepCentered_split N (fun j => x j)
  unfold centeredMoment
  simpa [oneStepCenteredRestrict, add_assoc, add_comm, add_left_comm] using h

private theorem centeredMoment_two_successor_split
    (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) :
    centeredMoment (N + 1) 2
        ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ) x) =
      centeredMoment N 2
          ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
            (oneStepCenteredRestrict N x)) +
        ((N + 1 : ℕ) : ℂ) ^ 2 * x (successorLeftOuterIndex N) +
        ((N + 1 : ℕ) : ℂ) ^ 2 * x (successorRightOuterIndex N) := by
  have h := sum_oneStepCentered_split N
    (fun j =>
      (((centeredIndex (N + 1) j : ℤ) : ℂ) ^ 2) * x j)
  have hnegSq :
      ((-(N : ℂ) + -1) ^ 2) = (((N + 1 : ℕ) : ℂ) ^ 2) := by
    push_cast
    ring
  unfold centeredMoment
  simpa [oneStepCenteredRestrict,
    centeredIndex_centeredEmbedding,
    centeredIndex_successorLeftOuterIndex,
    centeredIndex_successorRightOuterIndex,
    hnegSq, add_assoc, add_comm, add_left_comm] using h

private theorem centeredMoment_zero_centeredPowerVector_zero
    (N : ℕ) :
    centeredMoment N 0
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
          (centeredPowerVector N 0)) =
      (2 * (N : ℂ) + 1) := by
  unfold centeredMoment
  simp [centeredPowerVector_apply]

private theorem centeredMoment_zero_centeredPowerVector_two
    (N : ℕ) :
    centeredMoment N 0
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
          (centeredPowerVector N 2)) =
      ((N : ℂ) * (N + 1 : ℂ) * (2 * N + 1 : ℂ)) / 3 := by
  unfold centeredMoment
  simpa [centeredPowerVector_apply] using centered_square_sum_complex N

private theorem centeredMoment_two_centeredPowerVector_zero
    (N : ℕ) :
    centeredMoment N 2
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
          (centeredPowerVector N 0)) =
      ((N : ℂ) * (N + 1 : ℂ) * (2 * N + 1 : ℂ)) / 3 := by
  unfold centeredMoment
  simpa [centeredPowerVector_apply] using centered_square_sum_complex N

private theorem centeredMoment_two_centeredPowerVector_two
    (N : ℕ) :
    centeredMoment N 2
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ)
          (centeredPowerVector N 2)) =
      ((N : ℂ) * (N + 1 : ℂ) * (2 * N + 1 : ℂ) *
        (3 * (N : ℂ) ^ 2 + 3 * N - 1)) / 15 := by
  unfold centeredMoment
  simpa [centeredPowerVector_apply, pow_succ, pow_two, mul_assoc] using
    centered_fourth_sum_complex N

private theorem evenShell_rightOuter_eq
    (N : ℕ) :
    (((intrinsicCubicShellPart .even N :
        intrinsicParitySuccShell .even N) :
      euclideanParityBoundaryFlatSubspace .even (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
        (successorRightOuterIndex N) =
      ((N : ℂ) * (2 * (N : ℂ) + 1)) / 5 := by
  let e : euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    successorPulledBackCubicCompressionVector N
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    successorParityCubicVector .odd N
  let r := successorRightOuterIndex N
  have hD :=
    evenIndex_successorPulledBackCubicCompressionVector N
  have hDcoord := congrArg
    (fun y : euclideanOddBoundaryFlatSubspace (N + 1) =>
      ((y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r)) hD
  have hmul :
      (((N + 1 : ℕ) : ℂ) *
        ((e : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r) =
        ((g : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r := by
    change
      (euclideanIndexLinearMap (N + 1)
        ((e : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) r =
        ((g : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r at hDcoord
    have hcoords := congrArg
      (fun z : Fin (2 * (N + 1) + 1) → ℂ => z r)
      (euclideanIndexLinearMap_coordinates (N + 1)
        ((e : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
    rw [indexMatrix_mulVec_apply,
      centeredIndex_successorRightOuterIndex] at hcoords
    simpa using hcoords.symm.trans hDcoord
  have hproj :=
    cubicProjectionResidual_eq_oddCubicProjectionSlope_smul
      (N + 1) (by omega)
  have hprojcoord := congrArg
    (fun y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) => y r) hproj
  have hprojcoord' :
      (((N + 1 : ℕ) : ℂ) ^ 3 -
          ((g : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r) =
        oddCubicProjectionSlope (N + 1) * ((N + 1 : ℕ) : ℂ) := by
    simpa [r, g, successorParityCubicVector, centeredPowerVector_apply,
      centeredIndex_successorRightOuterIndex, smul_eq_mul] using hprojcoord
  have hg :
      ((g : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r =
        (((N + 1 : ℕ) : ℂ) ^ 3 -
          oddCubicProjectionSlope (N + 1) * ((N + 1 : ℕ) : ℂ)) := by
    linear_combination -hprojcoord'
  have hK0 : (((N + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  have heOuter :
      ((e : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r =
        ((N : ℂ) * (2 * (N : ℂ) + 1)) / 5 := by
    apply (mul_left_cancel₀ hK0)
    rw [hmul, hg]
    unfold oddCubicProjectionSlope
    field_simp
    push_cast
    ring
  have hrec := intrinsicPredecessorPart_add_shellPart .even N e
  have hpOuter :
      (((intrinsicPredecessorPart .even N e :
          intrinsicParityPredecessorSubspace .even N) :
        euclideanParityBoundaryFlatSubspace .even (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r = 0 := by
    exact intrinsicPredecessor_rightOuter_eq_zero
      .even N
      ((intrinsicPredecessorPart .even N e :
        intrinsicParityPredecessorSubspace .even N) :
        euclideanParityBoundaryFlatSubspace .even (N + 1))
      (intrinsicPredecessorPart .even N e).property
  have hcoord := congrArg
    (fun y : euclideanParityBoundaryFlatSubspace .even (N + 1) =>
      ((y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r)) hrec
  have hs :
      intrinsicShellPart .even N e = intrinsicCubicShellPart .even N := by
    rfl
  rw [hs] at hcoord
  have hcoord' :
      (((intrinsicPredecessorPart .even N e :
          intrinsicParityPredecessorSubspace .even N) :
        euclideanParityBoundaryFlatSubspace .even (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r +
      (((intrinsicCubicShellPart .even N :
          intrinsicParitySuccShell .even N) :
        euclideanParityBoundaryFlatSubspace .even (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r =
      ((e : euclideanParityBoundaryFlatSubspace .even (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) r := by
    simpa only [Submodule.coe_add, PiLp.add_apply] using hcoord
  rw [hpOuter, heOuter] at hcoord'
  simpa using hcoord'

private theorem evenShell_leftOuter_eq_rightOuter
    (N : ℕ) :
    (((intrinsicCubicShellPart .even N :
        intrinsicParitySuccShell .even N) :
      euclideanParityBoundaryFlatSubspace .even (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
        (successorLeftOuterIndex N) =
    (((intrinsicCubicShellPart .even N :
        intrinsicParitySuccShell .even N) :
      euclideanParityBoundaryFlatSubspace .even (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
        (successorRightOuterIndex N) := by
  let c : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) :=
    (((intrinsicCubicShellPart .even N :
        intrinsicParitySuccShell .even N) :
      euclideanParityBoundaryFlatSubspace .even (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  have hcBoundary :
      c ∈ euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    (intrinsicCubicShellPart .even N).property.2
  have hcCoeff :
      c ∈ euclideanEvenCoefficientSubspace (N + 1) := by
    have h :=
      euclideanParityBoundaryFlatSubspace_le_coefficientSubspace
        .even (N + 1) hcBoundary
    simpa [euclideanParityCoefficientSubspace] using h
  have hcRaw :=
    (mem_euclideanEvenCoefficientSubspace_iff (N + 1) c).mp hcCoeff
  have hrev :=
    (mem_evenCoefficientSubspace_iff (N + 1) _).mp hcRaw
  have h := congrFun hrev (successorRightOuterIndex N)
  simp only [reverseCoefficients] at h
  simpa [successorRightOuterIndex_rev] using h

private theorem evenShell_restrict_eq_const_add_quadratic
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : ℂ,
      oneStepCenteredRestrict N
          ((((intrinsicCubicShellPart .even N :
              intrinsicParitySuccShell .even N) :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
        A • centeredPowerVector N 0 +
          (-(6 : ℂ) / (2 * (N : ℂ) - 1)) •
            centeredPowerVector N 2 := by
  let c : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) :=
    (((intrinsicCubicShellPart .even N :
        intrinsicParitySuccShell .even N) :
      euclideanParityBoundaryFlatSubspace .even (N + 1)) :
      EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  let r := oneStepCenteredRestrict N c
  have hrNormal :
      r ∈ evenNormalSubspace N := by
    exact oneStepCenteredRestrict_evenShell_mem_normal N
      (intrinsicCubicShellPart .even N)
  rw [evenNormalSubspace, Submodule.mem_sup] at hrNormal
  rcases hrNormal with ⟨u, hu, v, hv, huv⟩
  rw [Submodule.mem_span_singleton] at hu hv
  rcases hu with ⟨A, rfl⟩
  rcases hv with ⟨B, rfl⟩
  have hrep :
      A • centeredPowerVector N 0 +
          B • centeredPowerVector N 2 = r := huv
  have hm0rep := congrArg
    (fun z : EuclideanSpace ℂ (Fin (2 * N + 1)) =>
      inner ℂ (centeredPowerVector N 0) z) hrep
  have hm2rep := congrArg
    (fun z : EuclideanSpace ℂ (Fin (2 * N + 1)) =>
      inner ℂ (centeredPowerVector N 2) z) hrep
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    inner_centeredPowerVector, inner_centeredPowerVector,
    inner_centeredPowerVector,
    centeredMoment_zero_centeredPowerVector_zero,
    centeredMoment_zero_centeredPowerVector_two] at hm0rep
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    inner_centeredPowerVector, inner_centeredPowerVector,
    inner_centeredPowerVector,
    centeredMoment_two_centeredPowerVector_zero,
    centeredMoment_two_centeredPowerVector_two] at hm2rep
  have hcBoundary :
      c ∈ euclideanParityBoundaryFlatSubspace .even (N + 1) :=
    (intrinsicCubicShellPart .even N).property.2
  have hcRaw :
      (EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ) c ∈
        evenBoundaryFlatSubspace (N + 1) := by
    simpa using hcBoundary
  have hcFlat := hcRaw.1
  have hcMom :=
    (mem_boundaryFlatSubspace_iff (N + 1) _).mp hcFlat
  have hsplit0 := centeredMoment_zero_successor_split N c
  have hsplit2 := centeredMoment_two_successor_split N c
  have hright :
      c (successorRightOuterIndex N) =
        ((N : ℂ) * (2 * (N : ℂ) + 1)) / 5 := by
    exact evenShell_rightOuter_eq N
  have hleft :
      c (successorLeftOuterIndex N) =
        ((N : ℂ) * (2 * (N : ℂ) + 1)) / 5 := by
    rw [evenShell_leftOuter_eq_rightOuter N]
    exact hright
  rw [hcMom.1, hleft, hright] at hsplit0
  rw [hcMom.2.2, hleft, hright] at hsplit2
  rw [← hm0rep] at hsplit0
  rw [← hm2rep] at hsplit2
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hNp1 : (N : ℂ) + 1 ≠ 0 := by
    have h : (N : ℂ) + 1 = ((N + 1 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [h]
    exact_mod_cast Nat.succ_ne_zero N
  have h2Np1 : 2 * (N : ℂ) + 1 ≠ 0 := by
    have hnat : 2 * N + 1 ≠ 0 := by omega
    have h : 2 * (N : ℂ) + 1 = ((2 * N + 1 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [h]
    exact_mod_cast hnat
  have h2Np3 : 2 * (N : ℂ) + 3 ≠ 0 := by
    have hnat : 2 * N + 3 ≠ 0 := by omega
    have h : 2 * (N : ℂ) + 3 = ((2 * N + 3 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [h]
    exact_mod_cast hnat
  have h2Nm1 : 2 * (N : ℂ) - 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    norm_num at hre
    nlinarith
  let C : ℂ :=
    (N : ℂ) * ((N : ℂ) + 1) *
      (2 * (N : ℂ) + 1) ^ 2 * (2 * (N : ℂ) + 3)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hN0 hNp1)
        (pow_ne_zero 2 h2Np1))
      h2Np3
  push_cast at hsplit2
  have hcomb :
      C * ((2 * (N : ℂ) - 1) * B + 6) = 0 := by
    dsimp [C]
    linear_combination
      -45 * ((2 * (N : ℂ) + 1) * hsplit2 -
        (((N : ℂ) * ((N : ℂ) + 1) *
          (2 * (N : ℂ) + 1)) / 3) * hsplit0)
  have hBlinear : (2 * (N : ℂ) - 1) * B + 6 = 0 :=
    (mul_eq_zero.mp hcomb).resolve_left hC
  have hB : B = -(6 : ℂ) / (2 * (N : ℂ) - 1) := by
    apply (eq_div_iff h2Nm1).2
    linear_combination hBlinear
  refine ⟨A, ?_⟩
  simpa [r, c, hB] using hrep.symm

theorem oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
    (N : ℕ) (hN : 1 ≤ N) :
    oddCubicGeneratorPredecessorPart N =
      -(crossParityCubicCorrectionKappa N) •
        oddIndexCubicShellPredecessorPart N := by
  let a := oddCubicGeneratorPredecessorPart N
  let d := oddIndexCubicShellPredecessorPart N
  let cPlus := intrinsicCubicShellPart .even N
  let cMinus := intrinsicCubicShellPart .odd N
  let kappa := crossParityCubicCorrectionKappa N
  let z : intrinsicParityPredecessorSubspace .odd N := a + kappa • d
  have hg :=
    oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N
  have hd :=
    evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN
  obtain ⟨A, hcPlusRestrict⟩ :=
    evenShell_restrict_eq_const_add_quadratic N hN
  have hcMinusNormal :=
    oneStepCenteredRestrict_oddShell_mem_normal N cMinus
  rw [oddNormalSubspace, Submodule.mem_span_singleton] at hcMinusNormal
  rcases hcMinusNormal with ⟨C, hcMinusRestrict⟩
  have hproj :=
    cubicProjectionResidual_eq_oddCubicProjectionSlope_smul
      (N + 1) (by omega)
  have hrestrictG :
      oneStepCenteredRestrict N
        (((successorParityCubicVector .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
        centeredPowerVector N 3 -
          oddCubicProjectionSlope (N + 1) • centeredPowerVector N 1 := by
    ext i
    have hi := congrArg
      (fun y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) =>
        y (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) hproj
    have hi' :
        (((centeredIndex N i : ℤ) : ℂ) ^ 3 -
          oneStepCenteredRestrict N
            (((successorParityCubicVector .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
              EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) i) =
          oddCubicProjectionSlope (N + 1) *
            (((centeredIndex N i : ℤ) : ℂ) ^ 1) := by
      simpa [oneStepCenteredRestrict_apply, successorParityCubicVector,
        centeredPowerVector_apply, centeredIndex_centeredEmbedding,
        smul_eq_mul] using hi
    rw [oneStepCenteredRestrict_apply] at hi'
    rw [oneStepCenteredRestrict_apply]
    simp [centeredPowerVector_apply] at hi' ⊢
    linear_combination -hi'
  have hrestrictD :
      oneStepCenteredRestrict N
        (((evenIndexParityLinearMap (N + 1)
            (cPlus :
              euclideanParityBoundaryFlatSubspace .even (N + 1)) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
        A • centeredPowerVector N 1 -
          ((6 : ℂ) / (2 * (N : ℂ) - 1)) • centeredPowerVector N 3 := by
    ext i
    have hc := congrArg
      (fun y : EuclideanSpace ℂ (Fin (2 * N + 1)) => y i)
      hcPlusRestrict
    change
      oneStepCenteredRestrict N
        (((evenIndexParityLinearMap (N + 1)
            (cPlus :
              euclideanParityBoundaryFlatSubspace .even (N + 1)) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) i =
        _
    rw [oneStepCenteredRestrict_apply]
    change
      (euclideanIndexLinearMap (N + 1)
        ((cPlus :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i) = _
    have hcoords := congrArg
      (fun z : Fin (2 * (N + 1) + 1) → ℂ =>
        z (centeredEmbedding N (N + 1) (Nat.le_succ N) i))
      (euclideanIndexLinearMap_coordinates (N + 1)
        ((cPlus :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
    rw [indexMatrix_mulVec_apply,
      centeredIndex_centeredEmbedding] at hcoords
    have hcoords' :
        (euclideanIndexLinearMap (N + 1)
          ((cPlus :
              euclideanParityBoundaryFlatSubspace .even (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
            (centeredEmbedding N (N + 1) (Nat.le_succ N) i) =
          (((centeredIndex N i : ℤ) : ℂ) *
            (((cPlus :
                euclideanParityBoundaryFlatSubspace .even (N + 1)) :
              EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i))) := by
      simpa using hcoords
    have hc' :
        (((cPlus :
            euclideanParityBoundaryFlatSubspace .even (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) =
        (A • centeredPowerVector N 0 +
          (-(6 : ℂ) / (2 * (N : ℂ) - 1)) •
            centeredPowerVector N 2) i := by
      simpa [oneStepCenteredRestrict_apply] using hc
    rw [hcoords', hc']
    simp [centeredPowerVector_apply]
    ring
  have hkappa :
      kappa * ((6 : ℂ) / (2 * (N : ℂ) - 1)) = 1 := by
    dsimp [kappa, crossParityCubicCorrectionKappa]
    have hden : 2 * (N : ℂ) - 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hN
      norm_num at hre
      nlinarith
    field_simp [hden]
  have hzRestrictNormal :
      oneStepCenteredRestrict N
        ((z : intrinsicParityPredecessorSubspace .odd N) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        oddNormalSubspace N := by
    rw [oddNormalSubspace, Submodule.mem_span_singleton]
    refine ⟨
      -(oddCubicProjectionSlope (N + 1)) + kappa * A -
        (1 + kappa) * C, ?_⟩
    apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
    ext i
    have hga := congrArg
      (fun y : euclideanParityBoundaryFlatSubspace .odd (N + 1) =>
        ((y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i))) hg
    have hdd := congrArg
      (fun y : euclideanParityBoundaryFlatSubspace .odd (N + 1) =>
        ((y : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i))) hd
    have hgR := congrArg
      (fun y : EuclideanSpace ℂ (Fin (2 * N + 1)) => y i) hrestrictG
    have hdR := congrArg
      (fun y : EuclideanSpace ℂ (Fin (2 * N + 1)) => y i) hrestrictD
    have hcR := congrArg
      (fun y : EuclideanSpace ℂ (Fin (2 * N + 1)) => y i)
      hcMinusRestrict
    symm
    change
      oneStepCenteredRestrict N
          ((z : intrinsicParityPredecessorSubspace .odd N) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) i =
        _
    dsimp [z, a, d]
    rw [oneStepCenteredRestrict_apply]
    change
      (((a : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i) +
        kappa *
          (((d : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i) = _
    have hga' :
        (((successorParityCubicVector .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) =
          (((a : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i) +
          (((cMinus : intrinsicParitySuccShell .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i) := by
      simpa only [Submodule.coe_add, PiLp.add_apply] using hga
    have hdd' :
        (((evenIndexParityLinearMap (N + 1)
            (cPlus :
              euclideanParityBoundaryFlatSubspace .even (N + 1)) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) =
          (((d : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i) +
          (((cMinus : intrinsicParitySuccShell .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i) := by
      simpa only [Submodule.coe_add, PiLp.add_apply] using hdd
    have hgR' :
        (((successorParityCubicVector .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) =
          (centeredPowerVector N 3 -
            oddCubicProjectionSlope (N + 1) • centeredPowerVector N 1) i := by
      simpa [oneStepCenteredRestrict_apply] using hgR
    have hdR' :
        (((evenIndexParityLinearMap (N + 1)
            (cPlus :
              euclideanParityBoundaryFlatSubspace .even (N + 1)) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          (centeredEmbedding N (N + 1) (Nat.le_succ N) i)) =
          (A • centeredPowerVector N 1 -
            ((6 : ℂ) / (2 * (N : ℂ) - 1)) •
              centeredPowerVector N 3) i := by
      simpa [oneStepCenteredRestrict_apply] using hdR
    have hcR' :
        (C • centeredPowerVector N 1) i =
          (((cMinus : intrinsicParitySuccShell .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
              (centeredEmbedding N (N + 1) (Nat.le_succ N) i) := by
      simpa [oneStepCenteredRestrict_apply] using hcR
    simp [centeredPowerVector_apply] at hgR' hdR' hcR' ⊢
    linear_combination
      -hga' - kappa * hdd' + hgR' + kappa * hdR' +
        (1 + kappa) * hcR' -
        ((((centeredIndex N i : ℤ) : ℂ) ^ 3) * hkappa)
  have hzBoundary :
      oneStepCenteredRestrict N
          ((z : intrinsicParityPredecessorSubspace .odd N) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanOddBoundaryFlatSubspace N := by
    rcases z.property with ⟨x, hx, hxz⟩
    change
      ((euclideanCenteredZeroExtend (Nat.le_succ N)).toLinearMap x) =
        ((z : intrinsicParityPredecessorSubspace .odd N) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) at hxz
    have hrestrict := congrArg
      (oneStepCenteredRestrict N) hxz
    have hleft :
        oneStepCenteredRestrict N
            ((euclideanCenteredZeroExtend (Nat.le_succ N)).toLinearMap x) = x := by
      change
        oneStepCenteredRestrict N
            (euclideanCenteredZeroExtendLinearMap (Nat.le_succ N) x) = x
      ext i
      simp [oneStepCenteredRestrict_apply]
    rw [hleft] at hrestrict
    have hrestrict' :
        x =
          oneStepCenteredRestrict N
            ((z : intrinsicParityPredecessorSubspace .odd N) :
              EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
      simpa using hrestrict
    exact hrestrict' ▸ hx
  have hzOrth :
      oneStepCenteredRestrict N
          ((z : intrinsicParityPredecessorSubspace .odd N) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        (euclideanOddBoundaryFlatSubspace N)ᗮ := by
    rw [← oddBoundaryFlat_normal_eq_oddNormalSubspace N] at hzRestrictNormal
    exact hzRestrictNormal.1
  have hzInner :
      inner ℂ
        (oneStepCenteredRestrict N
          ((z : intrinsicParityPredecessorSubspace .odd N) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
        (oneStepCenteredRestrict N
          ((z : intrinsicParityPredecessorSubspace .odd N) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) = 0 := by
    exact
      ((euclideanOddBoundaryFlatSubspace N).mem_orthogonal _).mp
        hzOrth _ hzBoundary
  have hzRestrictZero :
      oneStepCenteredRestrict N
          ((z : intrinsicParityPredecessorSubspace .odd N) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0 :=
    (inner_self_eq_zero).mp hzInner
  have hzZero : z = 0 := by
    rcases z.property with ⟨x, hx, hxz⟩
    change
      ((euclideanCenteredZeroExtend (Nat.le_succ N)).toLinearMap x) =
        ((z : intrinsicParityPredecessorSubspace .odd N) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) at hxz
    have hrestrict := congrArg
      (oneStepCenteredRestrict N) hxz
    have hleft :
        oneStepCenteredRestrict N
            ((euclideanCenteredZeroExtend (Nat.le_succ N)).toLinearMap x) = x := by
      change
        oneStepCenteredRestrict N
            (euclideanCenteredZeroExtendLinearMap (Nat.le_succ N) x) = x
      ext i
      simp [oneStepCenteredRestrict_apply]
    rw [hleft] at hrestrict
    have hrestrict' :
        x =
          oneStepCenteredRestrict N
            ((z : intrinsicParityPredecessorSubspace .odd N) :
              EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
      simpa using hrestrict
    rw [hzRestrictZero] at hrestrict'
    have hx0 : x = 0 := hrestrict'
    apply Subtype.ext
    apply Subtype.ext
    change
      ((z : intrinsicParityPredecessorSubspace .odd N) :
        EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) = 0
    rw [← hxz, hx0]
    simp
  dsimp [z, a, d, kappa] at hzZero
  have hneg :
      oddCubicGeneratorPredecessorPart N =
        -(crossParityCubicCorrectionKappa N •
          oddIndexCubicShellPredecessorPart N) :=
    eq_neg_of_add_eq_zero_left hzZero
  calc
    oddCubicGeneratorPredecessorPart N =
        -(crossParityCubicCorrectionKappa N •
          oddIndexCubicShellPredecessorPart N) := hneg
    _ = -(crossParityCubicCorrectionKappa N) •
        oddIndexCubicShellPredecessorPart N := by
      exact (neg_smul
        (crossParityCubicCorrectionKappa N)
        (oddIndexCubicShellPredecessorPart N)).symm

theorem oddCubicGenerator_add_kappa_evenIndexCubicShell_eq_shell
    (N : ℕ) (hN : 1 ≤ N) :
    successorParityCubicVector .odd N +
        crossParityCubicCorrectionKappa N •
          evenIndexParityLinearMap (N + 1)
            (intrinsicCubicShellPart .even N :
              euclideanParityBoundaryFlatSubspace .even (N + 1)) =
      (1 + crossParityCubicCorrectionKappa N) •
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let kappa := crossParityCubicCorrectionKappa N
  let a := oddCubicGeneratorPredecessorPart N
  let d := oddIndexCubicShellPredecessorPart N
  let c : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    intrinsicCubicShellPart .odd N
  have hpred :=
    oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul N hN
  have hpredAmbient :
      (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        (-kappa) •
          (d : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    apply Subtype.ext
    have h := congrArg
      (fun x : intrinsicParityPredecessorSubspace .odd N =>
        ((x : euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) hpred
    simpa only [Submodule.coe_smul] using h
  have hcancel :
      (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
          kappa •
            (d : euclideanParityBoundaryFlatSubspace .odd (N + 1)) = 0 := by
    rw [hpredAmbient]
    module
  rw [oddCubicCompressionVector_eq_predecessor_add_cubicShellPart N]
  rw [evenIndex_cubicShellPart_eq_predecessor_add_oddCubicShellPart N hN]
  change
    (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + c +
        kappa •
          ((d : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + c) =
      (1 + kappa) • c
  rw [smul_add]
  calc
    (a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) + c +
          (kappa •
              (d : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
            kappa • c) =
        ((a : euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
            kappa •
              (d : euclideanParityBoundaryFlatSubspace .odd (N + 1))) +
          (c + kappa • c) := by abel
    _ = c + kappa • c := by rw [hcancel, zero_add]
    _ = (1 + kappa) • c := by module

#print axioms Zeta23.CCM.oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
#print axioms Zeta23.CCM.oddCubicGenerator_add_kappa_evenIndexCubicShell_eq_shell

end Zeta23.CCM
