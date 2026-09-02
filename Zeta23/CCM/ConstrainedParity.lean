import Zeta23.CCM.NestedFinite
import Zeta23.CCM.Displacement
import Mathlib.Data.Fin.Rev

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ArithmeticFunction

/-!
# PARITY: exact reversal symmetry of the constrained finite CCM sector

This module theorem-locks the exact centered reversal i ↦ i.rev on the
(2N+1)-point Fourier grid. It proves index sign reversal, compatibility with
the exact centered N-flow, centered-moment parity, invariance of the
boundary-flat sector, reversal invariance of the canonical source matrix,
oddness of the displacement vector, and the resulting vanishing of the
one-channel displacement pairing on even boundary-flat vectors.

No parity-dimension theorem, constrained compression/eigenmode, first-bad
shell theorem, positivity theorem, or RH claim is made here.
-/

/-- Raw coefficient reversal on the centered finite grid. -/
def reverseCoefficients
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i => u i.rev

/-- Coefficient reversal as a complex-linear map. -/
def reversalLinearMap
    (N : ℕ) :
    (Fin (2 * N + 1) → ℂ) →ₗ[ℂ]
      (Fin (2 * N + 1) → ℂ) where
  toFun := reverseCoefficients N
  map_add' := by
    intro u v
    ext i
    rfl
  map_smul' := by
    intro c u
    ext i
    rfl

@[simp] theorem reversalLinearMap_apply
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (i : Fin (2 * N + 1)) :
    reversalLinearMap N u i = u i.rev := rfl

@[simp] theorem reverseCoefficients_reverseCoefficients
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    reverseCoefficients N (reverseCoefficients N u) = u := by
  ext i
  simp [reverseCoefficients]

/-- Reversal negates the represented centered Fourier index. -/
@[simp] theorem centeredIndex_rev
    (N : ℕ)
    (i : Fin (2 * N + 1)) :
    centeredIndex N i.rev = - centeredIndex N i := by
  unfold centeredIndex
  simp only [Fin.val_rev]
  omega

/-- The exact centered N-flow embedding commutes with reversal. -/
@[simp] theorem centeredEmbedding_rev
    (N M : ℕ) (hNM : N ≤ M)
    (i : Fin (2 * N + 1)) :
    centeredEmbedding N M hNM i.rev =
      (centeredEmbedding N M hNM i).rev := by
  apply Fin.ext
  simp only [centeredEmbedding_val, Fin.val_rev]
  omega

/-- Raw centered zero extension commutes with reversal. -/
theorem centeredZeroExtend_reverseCoefficients
    {N M : ℕ} (hNM : N ≤ M)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredZeroExtend hNM (reverseCoefficients N u) =
      reverseCoefficients M (centeredZeroExtend hNM u) := by
  ext j
  by_cases hj : j ∈ Set.range (centeredEmbedding N M hNM)
  · obtain ⟨i, rfl⟩ := hj
    simp only [reverseCoefficients, centeredZeroExtend_apply_centeredEmbedding]
    rw [← centeredEmbedding_rev N M hNM i]
    simp
  · have hjrev :
        j.rev ∉ Set.range (centeredEmbedding N M hNM) := by
      intro h
      obtain ⟨i, hi⟩ := h
      apply hj
      refine ⟨i.rev, ?_⟩
      simpa using congrArg Fin.rev hi
    rw [centeredZeroExtend_apply_of_not_mem_range hNM _ j hj]
    change 0 = centeredZeroExtend hNM u j.rev
    rw [centeredZeroExtend_apply_of_not_mem_range hNM _ j.rev hjrev]

/-- Every centered moment has the expected reversal parity. -/
theorem centeredMoment_reverseCoefficients
    (N k : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    centeredMoment N k (reverseCoefficients N u) =
      (-1 : ℂ) ^ k * centeredMoment N k u := by
  unfold centeredMoment
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, reverseCoefficients, Fin.rev_rev, centeredIndex_rev]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  rw [neg_pow]
  ring

/-- Reversal preserves the three boundary-flat moment constraints. -/
theorem reverseCoefficients_boundaryFlat
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : BoundaryFlatCoefficients N u) :
    BoundaryFlatCoefficients N (reverseCoefficients N u) := by
  constructor
  · rw [centeredMoment_reverseCoefficients]
    simpa using hu.1
  · constructor
    · rw [centeredMoment_reverseCoefficients]
      simpa using hu.2.1
    · rw [centeredMoment_reverseCoefficients]
      simpa using hu.2.2

theorem reverseCoefficients_mem_boundaryFlatSubspace
    {N : ℕ}
    {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ boundaryFlatSubspace N) :
    reverseCoefficients N u ∈ boundaryFlatSubspace N := by
  rw [mem_boundaryFlatSubspace_iff] at hu ⊢
  exact reverseCoefficients_boundaryFlat hu

/-- Raw even coefficient sector. -/
def evenCoefficientSubspace
    (N : ℕ) :
    Submodule ℂ (Fin (2 * N + 1) → ℂ) :=
  LinearMap.ker (reversalLinearMap N - LinearMap.id)

@[simp] theorem mem_evenCoefficientSubspace_iff
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    u ∈ evenCoefficientSubspace N ↔ reverseCoefficients N u = u := by
  change reverseCoefficients N u - u = 0 ↔ reverseCoefficients N u = u
  exact sub_eq_zero

/-- Raw odd coefficient sector. -/
def oddCoefficientSubspace
    (N : ℕ) :
    Submodule ℂ (Fin (2 * N + 1) → ℂ) :=
  LinearMap.ker (reversalLinearMap N + LinearMap.id)

@[simp] theorem mem_oddCoefficientSubspace_iff
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    u ∈ oddCoefficientSubspace N ↔ reverseCoefficients N u = -u := by
  change
    (reversalLinearMap N +
      (LinearMap.id :
        (Fin (2 * N + 1) → ℂ) →ₗ[ℂ] (Fin (2 * N + 1) → ℂ))) u = 0 ↔
      reverseCoefficients N u = -u
  simp only [LinearMap.add_apply, LinearMap.id_apply, reversalLinearMap_apply]
  exact eq_neg_iff_add_eq_zero.symm

/-- Even constrained coefficient sector. -/
def evenBoundaryFlatSubspace
    (N : ℕ) :
    Submodule ℂ (Fin (2 * N + 1) → ℂ) :=
  boundaryFlatSubspace N ⊓ evenCoefficientSubspace N

/-- Odd constrained coefficient sector. -/
def oddBoundaryFlatSubspace
    (N : ℕ) :
    Submodule ℂ (Fin (2 * N + 1) → ℂ) :=
  boundaryFlatSubspace N ⊓ oddCoefficientSubspace N

/-- The centered index operator flips coefficient parity. -/
theorem reverseCoefficients_indexMatrix_mulVec
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    reverseCoefficients N (indexMatrix N *ᵥ u) =
      -(indexMatrix N *ᵥ reverseCoefficients N u) := by
  ext i
  simp [reverseCoefficients, indexMatrix_mulVec_apply]

/-- The pole displacement sequence is odd in the centered Fourier index. -/
@[simp] theorem poleSeq_neg
    (n : ℤ) (L : ℝ) :
    poleSeq (-n) L = - poleSeq n L := by
  unfold poleSeq
  push_cast
  ring

/-- The off-diagonal archimedean potential is odd in the Fourier index. -/
@[simp] theorem alphaL_neg
    (n : ℤ) (L : ℝ) :
    alphaL (-n) L = - alphaL n L := by
  unfold alphaL
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hxmem
  by_cases hx : x = 0
  · subst x
    by_cases hn : n = 0
    · simp [hn]
    · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
      simp [hn, hneg]
      push_cast
      ring
  · simp only [hx, if_false]
    rw [show
      2 * Real.pi * ((-n : ℤ) : ℝ) * x / L =
        -(2 * Real.pi * (n : ℝ) * x / L) by
          push_cast
          ring]
    rw [Real.sin_neg]
    ring

/-- The diagonal beta term is even in the Fourier index. -/
@[simp] theorem betaL_neg
    (n : ℤ) (L : ℝ) :
    betaL (-n) L = betaL n L := by
  unfold betaL
  congr 1
  apply intervalIntegral.integral_congr
  intro x hxmem
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, if_false]
    rw [show
      2 * Real.pi * ((-n : ℤ) : ℝ) * x / L =
        -(2 * Real.pi * (n : ℝ) * x / L) by
          push_cast
          ring]
    rw [Real.cos_neg]

/-- The printed diagonal gamma term is even in the Fourier index. -/
@[simp] theorem gammaL_neg
    (n : ℤ) (L : ℝ) :
    gammaL (-n) L = gammaL n L := by
  unfold gammaL
  congr 2
  apply intervalIntegral.integral_congr
  intro x hxmem
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, if_false]
    rw [show
      2 * Real.pi * ((-n : ℤ) : ℝ) * x / L =
        -(2 * Real.pi * (n : ℝ) * x / L) by
          push_cast
          ring]
    rw [Real.cos_neg]

/-- The prime displacement sequence is odd in the Fourier index. -/
@[simp] theorem primeSeq_neg
    (n : ℤ) (L : ℝ) :
    primeSeq (-n) L = - primeSeq n L := by
  unfold primeSeq
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show
    2 * Real.pi * ((-n : ℤ) : ℝ) * Real.log k / L =
      -(2 * Real.pi * (n : ℝ) * Real.log k / L) by
        push_cast
        ring]
  rw [Real.sin_neg]
  ring

/-- The full displacement-generating scalar sequence is odd. -/
@[simp] theorem displacementSeq_neg
    (n : ℤ) (L : ℝ) :
    displacementSeq (-n) L = - displacementSeq n L := by
  simp only [displacementSeq, poleSeq_neg, alphaL_neg, primeSeq_neg]
  ring

/-- The concrete finite kernel is invariant under simultaneous index negation. -/
@[simp] theorem qBasis_neg_neg
    (n m : ℤ) (y L : ℝ) :
    qBasis (-n) (-m) y L = qBasis n m y L := by
  by_cases h : n = m
  · subst m
    rw [qBasis, if_pos rfl, qBasis, if_pos rfl]
    rw [show
      2 * Real.pi * ((-n : ℤ) : ℝ) * y / L =
        -(2 * Real.pi * (n : ℝ) * y / L) by
          push_cast
          ring]
    rw [Real.cos_neg]
  · have hneg : -n ≠ -m := by simpa using h
    have hmnZ : m - n ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hmnR : (((m - n : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hmnZ
    have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
    rw [qBasis, if_neg hneg, qBasis, if_neg h]
    rw [show
      2 * Real.pi * ((-n : ℤ) : ℝ) * y / L =
        -(2 * Real.pi * (n : ℝ) * y / L) by
          push_cast
          ring]
    rw [show
      2 * Real.pi * ((-m : ℤ) : ℝ) * y / L =
        -(2 * Real.pi * (m : ℝ) * y / L) by
          push_cast
          ring]
    rw [Real.sin_neg, Real.sin_neg]
    field_simp [Real.pi_ne_zero, hmnR, hnmR]
    push_cast
    ring

/-- The pole matrix channel is invariant under simultaneous index negation. -/
@[simp] theorem poleComponent_neg_neg
    (n m : ℤ) (L : ℝ) :
    poleComponent (-n) (-m) L = poleComponent n m L := by
  unfold poleComponent
  push_cast
  ring

/-- The archimedean matrix channel is invariant under simultaneous index negation. -/
@[simp] theorem archComponent_neg_neg
    (n m : ℤ) (L : ℝ) :
    archComponent (-n) (-m) L = archComponent n m L := by
  by_cases h : n = m
  · subst m
    simp [archComponent]
  · have hneg : -n ≠ -m := by simpa using h
    rw [archComponent, if_neg hneg, archComponent, if_neg h]
    simp only [alphaL_neg]
    push_cast
    have hnum :
        -alphaL m L - -alphaL n L =
          -(alphaL m L - alphaL n L) := by
      ring
    have hden :
        -(n : ℝ) - -(m : ℝ) =
          -((n : ℝ) - (m : ℝ)) := by
      ring
    rw [hnum, hden, neg_div_neg_eq]

/-- The finite prime-power matrix channel is invariant under simultaneous negation. -/
@[simp] theorem primeComponent_neg_neg
    (n m : ℤ) (L : ℝ) :
    primeComponent (-n) (-m) L = primeComponent n m L := by
  unfold primeComponent
  apply Finset.sum_congr rfl
  intro k hk
  rw [qBasis_neg_neg]

/-- The historical finite scalar entry is reversal invariant. -/
@[simp] theorem entry_neg_neg
    (n m : ℤ) (L : ℝ) :
    entry (-n) (-m) L = entry n m L := by
  simp [entry]

/-- The cutoff-free diagonal primitive is even. -/
@[simp] theorem cutoffFreeGammaL_neg
    (n : ℤ) (L : ℝ) :
    cutoffFreeGammaL (-n) L = cutoffFreeGammaL n L := by
  simp [cutoffFreeGammaL]

/-- The cutoff-free archimedean channel is reversal invariant. -/
@[simp] theorem cutoffFreeArchComponent_neg_neg
    (n m : ℤ) (L : ℝ) :
    cutoffFreeArchComponent (-n) (-m) L =
      cutoffFreeArchComponent n m L := by
  by_cases h : n = m
  · subst m
    simp [cutoffFreeArchComponent]
  · have hneg : -n ≠ -m := by simpa using h
    rw [cutoffFreeArchComponent, if_neg hneg,
      cutoffFreeArchComponent, if_neg h]
    simp only [alphaL_neg]
    push_cast
    have hnum :
        -alphaL m L - -alphaL n L =
          -(alphaL m L - alphaL n L) := by
      ring
    have hden :
        -(n : ℝ) - -(m : ℝ) =
          -((n : ℝ) - (m : ℝ)) := by
      ring
    rw [hnum, hden, neg_div_neg_eq]

/-- The canonical cutoff-free scalar entry is reversal invariant. -/
@[simp] theorem cutoffFreeEntry_neg_neg
    (n m : ℤ) (L : ℝ) :
    cutoffFreeEntry (-n) (-m) L = cutoffFreeEntry n m L := by
  simp [cutoffFreeEntry]

/-- Canonical finite CCM entries are fixed by simultaneous Fin reversal. -/
@[simp] theorem canonicalSourceMatrix_apply_rev_rev
    (L : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    canonicalSourceMatrix L N i.rev j.rev =
      canonicalSourceMatrix L N i j := by
  simp [canonicalSourceMatrix, cutoffFreeMatrix]

/-- The concrete CCM displacement vector is odd under Fin reversal. -/
@[simp] theorem displacementVector_rev
    (L : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    displacementVector L N i.rev =
      - displacementVector L N i := by
  simp [displacementVector, dividedDifferenceVector, ccmPotential]

/-- The exact canonical matrix action commutes with raw coefficient reversal. -/
theorem canonicalSourceMatrix_mulVec_reverseCoefficients
    (L : ℝ) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    canonicalSourceMatrix L N *ᵥ reverseCoefficients N u =
      reverseCoefficients N (canonicalSourceMatrix L N *ᵥ u) := by
  ext i
  change
    (canonicalSourceMatrix L N).row i ⬝ᵥ reverseCoefficients N u =
      (canonicalSourceMatrix L N).row i.rev ⬝ᵥ u
  unfold dotProduct
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, reverseCoefficients, Fin.rev_rev, Matrix.row_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simpa using congrArg (fun z : ℂ => z * u j)
    (canonicalSourceMatrix_apply_rev_rev L N i.rev j)

/-- Even coefficient vectors annihilate the odd displacement vector in the
ordinary bilinear pairing used by the exact commutator theorem. -/
theorem displacementPairing_eq_zero_of_even
    (L : ℝ) (N : ℕ)
    {u : Fin (2 * N + 1) → ℂ}
    (hu : u ∈ evenCoefficientSubspace N) :
    displacementPairing L N u = 0 := by
  rw [mem_evenCoefficientSubspace_iff] at hu
  unfold displacementPairing
  have hrev :
      (∑ i, displacementVector L N i * u i) =
        -(∑ i, displacementVector L N i * u i) := by
    calc
      (∑ i, displacementVector L N i * u i)
          = ∑ i : Fin (2 * N + 1),
              displacementVector L N i.rev * u i.rev := by
              rw [← Equiv.sum_comp Fin.revPerm]
              simp
      _ = -(∑ i, displacementVector L N i * u i) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              rw [displacementVector_rev]
              have hui := congrFun hu i
              simp only [reverseCoefficients] at hui
              rw [hui]
              ring
  have hsum :
      (∑ i, displacementVector L N i * u i) +
          (∑ i, displacementVector L N i * u i) = 0 :=
    (eq_neg_iff_add_eq_zero).mp hrev
  linear_combination (1 / 2 : ℂ) * hsum

/-- On an even boundary-flat vector, the exact one-channel canonical
commutator collapses all the way to zero. -/
theorem canonicalSourceMatrix_displacement_mulVec_even_boundaryFlat
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    (hflat : u ∈ boundaryFlatSubspace N)
    (heven : u ∈ evenCoefficientSubspace N) :
    (indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N) *ᵥ u = 0 := by
  have hbf : BoundaryFlatCoefficients N u := by
    exact (mem_boundaryFlatSubspace_iff N u).mp hflat
  rw [canonicalSourceMatrix_displacement_mulVec_boundaryFlat hL N u hbf]
  rw [displacementPairing_eq_zero_of_even L N heven]
  ext i
  simp

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredIndex_rev
#print axioms Zeta23.CCM.centeredEmbedding_rev
#print axioms Zeta23.CCM.centeredMoment_reverseCoefficients
#print axioms Zeta23.CCM.canonicalSourceMatrix_apply_rev_rev
#print axioms Zeta23.CCM.displacementVector_rev
#print axioms Zeta23.CCM.canonicalSourceMatrix_mulVec_reverseCoefficients
#print axioms Zeta23.CCM.displacementPairing_eq_zero_of_even
#print axioms Zeta23.CCM.canonicalSourceMatrix_displacement_mulVec_even_boundaryFlat
