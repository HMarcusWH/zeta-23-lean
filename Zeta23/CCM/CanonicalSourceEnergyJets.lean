import Zeta23.CCM.CanonicalPolePrimeDiscrepancy
import Zeta23.CCM.ConstrainedParity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03: source-energy endpoint jets

This module discovers the endpoint cancellations of the *production*
`sourceAtomRealEnergy`.  The first structural fact is exact oddness in the
source coordinate.  Consequently every even source-coordinate jet vanishes at
zero.  The remaining odd jets are then reduced to the theorem-backed centered
moments carried by the boundary-flat/parity sectors.

No Riesz order is assumed here in advance.  The admissible smoothing order is
an output of these endpoint theorems.
-/

@[simp] theorem sourcePotential_neg_sourceCoordinate
    (ω : ℝ) (n : ℤ) :
    sourcePotential (-ω) n = -sourcePotential ω n := by
  unfold sourcePotential
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * (-ω) =
      -(2 * Real.pi * (n : ℝ) * ω) by ring]
  rw [Real.sin_neg]
  ring

@[simp] theorem sourceDiagonal_neg_sourceCoordinate
    (ω : ℝ) (n : ℤ) :
    sourceDiagonal (-ω) n = -sourceDiagonal ω n := by
  unfold sourceDiagonal
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * (-ω) =
      -(2 * Real.pi * (n : ℝ) * ω) by ring]
  rw [Real.cos_neg]
  ring

@[simp] theorem sourceEntry_neg_sourceCoordinate
    (ω : ℝ) (n m : ℤ) :
    sourceEntry (-ω) n m = -sourceEntry ω n m := by
  unfold sourceEntry dividedDifferenceEntry
  by_cases h : n = m
  · simp [h, sourceDiagonal_neg_sourceCoordinate]
  · simp [h, sourcePotential_neg_sourceCoordinate]

@[simp] theorem sourceMatrix_neg_sourceCoordinate
    (ω : ℝ) (K : ℕ) :
    sourceMatrix (-ω) K = -sourceMatrix ω K := by
  ext i j
  simp [sourceMatrix_apply]

/-- The production source-atom real energy is exactly odd in its source
coordinate. -/
@[simp] theorem sourceAtomRealEnergy_neg_sourceCoordinate
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    sourceAtomRealEnergy K x (-ω) = -sourceAtomRealEnergy K x ω := by
  unfold sourceAtomRealEnergy
  rw [sourceMatrix_neg_sourceCoordinate]
  have hneg :
      (-sourceMatrix ω K : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) =
        (((-1 : ℝ) : ℂ)) • sourceMatrix ω K := by
    ext i j
    simp
  rw [hneg, matrixRealEnergy_smul_real]
  ring

/-- Every even source-coordinate derivative of the production source energy
vanishes at the left endpoint. -/
theorem iteratedDeriv_even_sourceAtomRealEnergy_zero
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (k : ℕ) :
    iteratedDeriv (2 * k) (sourceAtomRealEnergy K x) 0 = 0 := by
  let g : ℝ → ℝ := sourceAtomRealEnergy K x
  have hfun : (fun ω : ℝ => g (-ω)) = fun ω => -g ω := by
    funext ω
    exact sourceAtomRealEnergy_neg_sourceCoordinate K x ω
  have hleft := iteratedDeriv_comp_neg (2 * k) g (0 : ℝ)
  have hright := congrArg
    (fun f : ℝ → ℝ => iteratedDeriv (2 * k) f 0) hfun
  have heven : Even (2 * k) := ⟨k, by omega⟩
  rw [iteratedDeriv_fun_neg] at hright
  simp only [neg_zero] at hleft
  rw [Even.neg_one_pow heven] at hleft
  norm_num at hleft
  rw [hleft] at hright
  linarith

/-- Even reversal parity kills centered moment three. -/
theorem centeredMoment_three_eq_zero_of_even
    {K : ℕ}
    {u : Fin (2 * K + 1) → ℂ}
    (hu : u ∈ evenCoefficientSubspace K) :
    centeredMoment K 3 u = 0 := by
  have heven : reverseCoefficients K u = u :=
    (mem_evenCoefficientSubspace_iff K u).mp hu
  have hrev := centeredMoment_reverseCoefficients K 3 u
  rw [heven] at hrev
  norm_num at hrev
  have htwo : (2 : ℂ) * centeredMoment K 3 u = 0 := by
    linear_combination hrev
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceAtomRealEnergy_neg_sourceCoordinate
#print axioms Zeta23.CCM.iteratedDeriv_even_sourceAtomRealEnergy_zero
#print axioms Zeta23.CCM.centeredMoment_three_eq_zero_of_even
