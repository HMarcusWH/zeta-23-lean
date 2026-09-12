import Zeta23.CCM.CanonicalPolePrimeDiscrepancy
import Zeta23.CCM.SourceDerivativeTransport
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
zero.  The remaining odd jets are supplied by the exact source-coordinate
`D`-transport from `SourceDerivativeTransport` and the theorem-backed centered
moments carried by the boundary-flat/parity sectors.

No sign of a high derivative away from the endpoint is asserted here.
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
  by_cases h : n = m
  · subst m
    rw [sourceEntry_self, sourceEntry_self]
    exact sourceDiagonal_neg_sourceCoordinate ω n
  · rw [sourceEntry_of_ne (-ω) h, sourceEntry_of_ne ω h]
    rw [sourcePotential_neg_sourceCoordinate, sourcePotential_neg_sourceCoordinate]
    ring

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

/-- Every odd centered moment vanishes on the even reversal sector. -/
theorem centeredMoment_odd_eq_zero_of_even
    {K k : ℕ}
    {u : Fin (2 * K + 1) → ℂ}
    (hu : u ∈ evenCoefficientSubspace K)
    (hk : Odd k) :
    centeredMoment K k u = 0 := by
  have heven : reverseCoefficients K u = u :=
    (mem_evenCoefficientSubspace_iff K u).mp hu
  have hrev := centeredMoment_reverseCoefficients K k u
  rw [heven, hk.neg_one_pow] at hrev
  have htwo : (2 : ℂ) * centeredMoment K k u = 0 := by
    linear_combination hrev
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Compatibility theorem retained from #155. -/
theorem centeredMoment_three_eq_zero_of_even
    {K : ℕ}
    {u : Fin (2 * K + 1) → ℂ}
    (hu : u ∈ evenCoefficientSubspace K) :
    centeredMoment K 3 u = 0 := by
  exact centeredMoment_odd_eq_zero_of_even hu (by norm_num)

/-- The Euclidean index action shifts centered moments exactly. -/
theorem centeredMoment_sourceIndexAction
    (K k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    centeredMoment K k
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (sourceIndexAction K x)) =
      centeredMoment K (k + 1)
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  rw [sourceIndexAction_coordinates]
  exact centeredMoment_indexMatrix_mulVec K k
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)

/-- The first production source-energy jet vanishes whenever the coefficient
sum vanishes.  This is the complex-production endpoint theorem: the real and
imaginary coordinate sums are both discharged explicitly. -/
theorem iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hsum :
      ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0) :
    iteratedDeriv 1 (sourceAtomRealEnergy K x) 0 = 0 := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  obtain ⟨hre, him⟩ :=
    coefficientSumReal_re_im_eq_zero_of_sum_eq_zero K u hsum
  rw [iteratedDeriv_one]
  rw [(hasDerivAt_sourceAtomRealEnergy_transport K x 0).deriv]
  unfold sourceAtomRealEnergyDerivative
  rw [sourceContractRealDerivative_zero_eq_two_coefficientSum_sq,
    sourceContractRealDerivative_zero_eq_two_coefficientSum_sq]
  rw [hre, him]
  ring

/-- Two source-coordinate derivatives transport to one centered-index action
on the production coefficient vector. -/
theorem iteratedDeriv_two_sourceAtomRealEnergy_eq_indexAction
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ)
    (hsum :
      ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0) :
    iteratedDeriv 2 (sourceAtomRealEnergy K x) ω =
      -(2 * Real.pi) ^ 2 *
        sourceAtomRealEnergy K (sourceIndexAction K x) ω := by
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ]
  have hderiv :
      deriv (sourceAtomRealEnergy K x) =
        sourceAtomRealEnergyDerivative K x := by
    funext t
    exact (hasDerivAt_sourceAtomRealEnergy_transport K x t).deriv
  rw [hderiv]
  rw [(hasDerivAt_sourceAtomRealEnergyDerivative_transport K x ω).deriv]
  exact sourceAtomRealEnergySecondDerivative_eq_indexAction K x ω hsum

/-- General two-step transport for higher production jets. -/
theorem iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (j : ℕ)
    (ω : ℝ)
    (hsum :
      ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0) :
    iteratedDeriv (j + 2) (sourceAtomRealEnergy K x) ω =
      -(2 * Real.pi) ^ 2 *
        iteratedDeriv j (sourceAtomRealEnergy K (sourceIndexAction K x)) ω := by
  have htwo :
      iteratedDeriv 2 (sourceAtomRealEnergy K x) =
        fun t => -(2 * Real.pi) ^ 2 *
          sourceAtomRealEnergy K (sourceIndexAction K x) t := by
    funext t
    exact iteratedDeriv_two_sourceAtomRealEnergy_eq_indexAction K x t hsum
  calc
    iteratedDeriv (j + 2) (sourceAtomRealEnergy K x) ω =
        iteratedDeriv j
          (iteratedDeriv 2 (sourceAtomRealEnergy K x)) ω := by
      simp only [iteratedDeriv_eq_iterate]
      exact Function.iterate_add_apply
        (fun f : ℝ → ℝ => deriv f) j 2 (sourceAtomRealEnergy K x) ω
    _ = iteratedDeriv j
        (fun t => -(2 * Real.pi) ^ 2 *
          sourceAtomRealEnergy K (sourceIndexAction K x) t) ω := by
      rw [htwo]
    _ = -(2 * Real.pi) ^ 2 *
        iteratedDeriv j (sourceAtomRealEnergy K (sourceIndexAction K x)) ω := by
      simpa using
        (iteratedDeriv_const_mul_field
          (x := ω) (n := j)
          (-(2 * Real.pi) ^ 2)
          (sourceAtomRealEnergy K (sourceIndexAction K x)))

/-- Boundary-flatness gives zero coefficient sum for the production carrier. -/
theorem sourceAtom_sum_eq_zero_of_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0 :=
  sum_eq_zero_of_boundaryFlat hflat

/-- The first index iterate of a boundary-flat production carrier has zero
coefficient sum. -/
theorem sourceIndexAction_sum_eq_zero_of_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    ∑ i,
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (sourceIndexAction K x)) i = 0 := by
  rw [sourceIndexAction_coordinates]
  exact sum_indexMatrix_mulVec_eq_zero_of_boundaryFlat hflat

/-- The second index iterate of a boundary-flat production carrier has zero
coefficient sum. -/
theorem sourceIndexAction_sq_sum_eq_zero_of_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    ∑ i,
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (sourceIndexAction K (sourceIndexAction K x))) i = 0 := by
  rw [sourceIndexAction_coordinates, sourceIndexAction_coordinates]
  exact sum_indexMatrix_mulVec_sq_eq_zero_of_boundaryFlat hflat

/-- The third index iterate has coefficient sum equal to centered moment three. -/
theorem sourceIndexAction_cube_sum_eq_centeredMoment_three
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (∑ i,
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (sourceIndexAction K
          (sourceIndexAction K (sourceIndexAction K x)))) i) =
      centeredMoment K 3
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  rw [← centeredMoment_zero_eq_sum]
  rw [centeredMoment_sourceIndexAction,
    centeredMoment_sourceIndexAction,
    centeredMoment_sourceIndexAction]
  norm_num

/-- Odd jet three vanishes on every production boundary-flat carrier. -/
theorem iteratedDeriv_three_sourceAtomRealEnergy_zero_of_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    iteratedDeriv 3 (sourceAtomRealEnergy K x) 0 = 0 := by
  rw [show 3 = 1 + 2 by omega,
    iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
      K x 1 0 (sourceAtom_sum_eq_zero_of_boundaryFlat K x hflat)]
  rw [iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
    K (sourceIndexAction K x)
    (sourceIndexAction_sum_eq_zero_of_boundaryFlat K x hflat)]
  ring

/-- Odd jet five vanishes on every production boundary-flat carrier. -/
theorem iteratedDeriv_five_sourceAtomRealEnergy_zero_of_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    iteratedDeriv 5 (sourceAtomRealEnergy K x) 0 = 0 := by
  rw [show 5 = 3 + 2 by omega,
    iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
      K x 3 0 (sourceAtom_sum_eq_zero_of_boundaryFlat K x hflat)]
  rw [show 3 = 1 + 2 by omega,
    iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
      K (sourceIndexAction K x) 1 0
      (sourceIndexAction_sum_eq_zero_of_boundaryFlat K x hflat)]
  rw [iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
    K (sourceIndexAction K (sourceIndexAction K x))
    (sourceIndexAction_sq_sum_eq_zero_of_boundaryFlat K x hflat)]
  ring

/-- Production boundary-flat coefficients kill every source-energy jet from
order one through order six. -/
theorem sourceAtomRealEnergy_boundaryFlat_jets_through_six
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 6 →
      iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0 := by
  intro j hj1 hj6
  have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
      K x (sourceAtom_sum_eq_zero_of_boundaryFlat K x hflat)
  · simpa using iteratedDeriv_even_sourceAtomRealEnergy_zero K x 1
  · exact iteratedDeriv_three_sourceAtomRealEnergy_zero_of_boundaryFlat K x hflat
  · simpa using iteratedDeriv_even_sourceAtomRealEnergy_zero K x 2
  · exact iteratedDeriv_five_sourceAtomRealEnergy_zero_of_boundaryFlat K x hflat
  · simpa using iteratedDeriv_even_sourceAtomRealEnergy_zero K x 3

/-- On an even boundary-flat production carrier, the third index iterate also
has zero coefficient sum because even reversal kills moment three. -/
theorem sourceIndexAction_cube_sum_eq_zero_of_even_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    (∑ i,
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (sourceIndexAction K
          (sourceIndexAction K (sourceIndexAction K x)))) i) = 0 := by
  rw [sourceIndexAction_cube_sum_eq_centeredMoment_three]
  exact centeredMoment_three_eq_zero_of_even heven

/-- Odd jet seven vanishes on the even production boundary-flat sector. -/
theorem iteratedDeriv_seven_sourceAtomRealEnergy_zero_of_even_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    iteratedDeriv 7 (sourceAtomRealEnergy K x) 0 = 0 := by
  rw [show 7 = 5 + 2 by omega,
    iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
      K x 5 0 (sourceAtom_sum_eq_zero_of_boundaryFlat K x hflat)]
  rw [show 5 = 3 + 2 by omega,
    iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
      K (sourceIndexAction K x) 3 0
      (sourceIndexAction_sum_eq_zero_of_boundaryFlat K x hflat)]
  rw [show 3 = 1 + 2 by omega,
    iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
      K (sourceIndexAction K (sourceIndexAction K x)) 1 0
      (sourceIndexAction_sq_sum_eq_zero_of_boundaryFlat K x hflat)]
  rw [iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
    K (sourceIndexAction K
      (sourceIndexAction K (sourceIndexAction K x)))
    (sourceIndexAction_cube_sum_eq_zero_of_even_boundaryFlat K x heven)]
  ring

/-- Even boundary-flat production coefficients kill every source-energy jet
from order one through order eight. -/
theorem sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 8 →
      iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0 := by
  intro j hj1 hj8
  by_cases hj6 : j ≤ 6
  · exact sourceAtomRealEnergy_boundaryFlat_jets_through_six K x hflat j hj1 hj6
  have hj : j = 7 ∨ j = 8 := by omega
  rcases hj with rfl | rfl
  · exact iteratedDeriv_seven_sourceAtomRealEnergy_zero_of_even_boundaryFlat
      K x hflat heven
  · simpa using iteratedDeriv_even_sourceAtomRealEnergy_zero K x 4

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceAtomRealEnergy_neg_sourceCoordinate
#print axioms Zeta23.CCM.iteratedDeriv_even_sourceAtomRealEnergy_zero
#print axioms Zeta23.CCM.centeredMoment_odd_eq_zero_of_even
#print axioms Zeta23.CCM.iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
#print axioms Zeta23.CCM.sourceAtomRealEnergy_boundaryFlat_jets_through_six
#print axioms Zeta23.CCM.sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
