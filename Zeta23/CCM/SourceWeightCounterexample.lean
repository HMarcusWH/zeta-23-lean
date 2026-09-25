import Zeta23.CCM.CanonicalSourceMomentJets
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators

/-!
# Exact counterexample to carrier-wide source-weight positivity

This is an actual real even boundary-flat K=4 vector, not a scalar toy and not
an asserted canonical ground eigenvector. Its ninth source-energy jet is
positive, but its first source-energy derivative at 1/8 is negative.
-/

def sourceWeightCounterexampleReal : Fin 9 → ℝ :=
  ![-1, 3, 1, -15, 24, -15, 1, 3, -1]

def sourceWeightCounterexampleCoefficients : Fin 9 → ℂ :=
  fun i => (sourceWeightCounterexampleReal i : ℂ)

def sourceWeightCounterexampleVector : EuclideanSpace ℂ (Fin 9) :=
  (EuclideanSpace.equiv (Fin 9) ℂ).symm sourceWeightCounterexampleCoefficients

@[simp] theorem sourceWeightCounterexample_coordinates :
    (EuclideanSpace.equiv (Fin 9) ℂ) sourceWeightCounterexampleVector =
      sourceWeightCounterexampleCoefficients := by
  simp [sourceWeightCounterexampleVector]

theorem sourceWeightCounterexample_boundaryFlat :
    BoundaryFlatCoefficients 4 sourceWeightCounterexampleCoefficients := by
  norm_num [BoundaryFlatCoefficients, centeredMoment, centeredIndex,
    sourceWeightCounterexampleCoefficients, sourceWeightCounterexampleReal,
    Fin.sum_univ_succ]

theorem sourceWeightCounterexample_even :
    sourceWeightCounterexampleCoefficients ∈ evenCoefficientSubspace 4 := by
  apply (mem_evenCoefficientSubspace_iff 4 _).mpr
  ext i
  fin_cases i <;>
    norm_num [reverseCoefficients, sourceWeightCounterexampleCoefficients,
      sourceWeightCounterexampleReal, Fin.rev]

theorem sourceWeightCounterexample_fourthMoment :
    centeredMoment 4 4 sourceWeightCounterexampleCoefficients = -24 := by
  norm_num [centeredMoment, centeredIndex, sourceWeightCounterexampleCoefficients,
    sourceWeightCounterexampleReal, Fin.sum_univ_succ]

private def cosEighthTable : Fin 9 → ℝ :=
  ![-1, -Real.sqrt 2 / 2, 0, Real.sqrt 2 / 2, 1,
    Real.sqrt 2 / 2, 0, -Real.sqrt 2 / 2, -1]

private def sinEighthTable : Fin 9 → ℝ :=
  ![0, -Real.sqrt 2 / 2, -1, -Real.sqrt 2 / 2, 0,
    Real.sqrt 2 / 2, 1, Real.sqrt 2 / 2, 0]

private theorem cos_counterexample_indices (i : Fin 9) :
    Real.cos (2 * Real.pi * (centeredIndex 4 i : ℝ) * (1 / 8)) =
      cosEighthTable i := by
  have h0 : Real.cos (2 * Real.pi * (-4 : ℝ) * (1 / 8)) = -1 := by
    rw [show 2 * Real.pi * (-4 : ℝ) * (1 / 8) = -(Real.pi) by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h1 : Real.cos (2 * Real.pi * (-3 : ℝ) * (1 / 8)) = -Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (-3 : ℝ) * (1 / 8) = -(Real.pi - Real.pi / 4) by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h2 : Real.cos (2 * Real.pi * (-2 : ℝ) * (1 / 8)) = 0 := by
    rw [show 2 * Real.pi * (-2 : ℝ) * (1 / 8) = -(Real.pi / 2) by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h3 : Real.cos (2 * Real.pi * (-1 : ℝ) * (1 / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (-1 : ℝ) * (1 / 8) = -(Real.pi / 4) by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h4 : Real.cos (2 * Real.pi * (0 : ℝ) * (1 / 8)) = 1 := by
    rw [show 2 * Real.pi * (0 : ℝ) * (1 / 8) = 0 by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h5 : Real.cos (2 * Real.pi * (1 : ℝ) * (1 / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (1 : ℝ) * (1 / 8) = Real.pi / 4 by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h6 : Real.cos (2 * Real.pi * (2 : ℝ) * (1 / 8)) = 0 := by
    rw [show 2 * Real.pi * (2 : ℝ) * (1 / 8) = Real.pi / 2 by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h7 : Real.cos (2 * Real.pi * (3 : ℝ) * (1 / 8)) = -Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (3 : ℝ) * (1 / 8) = Real.pi - Real.pi / 4 by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  have h8 : Real.cos (2 * Real.pi * (4 : ℝ) * (1 / 8)) = -1 := by
    rw [show 2 * Real.pi * (4 : ℝ) * (1 / 8) = Real.pi by ring]
    simp [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four,
      Real.cos_pi_div_two, Real.cos_pi]
  fin_cases i
  · simpa [centeredIndex, cosEighthTable] using h0
  · simpa [centeredIndex, cosEighthTable] using h1
  · simpa [centeredIndex, cosEighthTable] using h2
  · simpa [centeredIndex, cosEighthTable] using h3
  · simpa [centeredIndex, cosEighthTable] using h4
  · simpa [centeredIndex, cosEighthTable] using h5
  · simpa [centeredIndex, cosEighthTable] using h6
  · simpa [centeredIndex, cosEighthTable] using h7
  · simpa [centeredIndex, cosEighthTable] using h8

private theorem sin_counterexample_indices (i : Fin 9) :
    Real.sin (2 * Real.pi * (centeredIndex 4 i : ℝ) * (1 / 8)) =
      sinEighthTable i := by
  have h0 : Real.sin (2 * Real.pi * (-4 : ℝ) * (1 / 8)) = 0 := by
    rw [show 2 * Real.pi * (-4 : ℝ) * (1 / 8) = -(Real.pi) by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h1 : Real.sin (2 * Real.pi * (-3 : ℝ) * (1 / 8)) = -Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (-3 : ℝ) * (1 / 8) = -(Real.pi - Real.pi / 4) by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h2 : Real.sin (2 * Real.pi * (-2 : ℝ) * (1 / 8)) = -1 := by
    rw [show 2 * Real.pi * (-2 : ℝ) * (1 / 8) = -(Real.pi / 2) by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h3 : Real.sin (2 * Real.pi * (-1 : ℝ) * (1 / 8)) = -Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (-1 : ℝ) * (1 / 8) = -(Real.pi / 4) by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h4 : Real.sin (2 * Real.pi * (0 : ℝ) * (1 / 8)) = 0 := by
    rw [show 2 * Real.pi * (0 : ℝ) * (1 / 8) = 0 by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h5 : Real.sin (2 * Real.pi * (1 : ℝ) * (1 / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (1 : ℝ) * (1 / 8) = Real.pi / 4 by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h6 : Real.sin (2 * Real.pi * (2 : ℝ) * (1 / 8)) = 1 := by
    rw [show 2 * Real.pi * (2 : ℝ) * (1 / 8) = Real.pi / 2 by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h7 : Real.sin (2 * Real.pi * (3 : ℝ) * (1 / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (3 : ℝ) * (1 / 8) = Real.pi - Real.pi / 4 by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  have h8 : Real.sin (2 * Real.pi * (4 : ℝ) * (1 / 8)) = 0 := by
    rw [show 2 * Real.pi * (4 : ℝ) * (1 / 8) = Real.pi by ring]
    simp [Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four,
      Real.sin_pi_div_two, Real.sin_pi]
  fin_cases i
  · simpa [centeredIndex, sinEighthTable] using h0
  · simpa [centeredIndex, sinEighthTable] using h1
  · simpa [centeredIndex, sinEighthTable] using h2
  · simpa [centeredIndex, sinEighthTable] using h3
  · simpa [centeredIndex, sinEighthTable] using h4
  · simpa [centeredIndex, sinEighthTable] using h5
  · simpa [centeredIndex, sinEighthTable] using h6
  · simpa [centeredIndex, sinEighthTable] using h7
  · simpa [centeredIndex, sinEighthTable] using h8

private theorem sourcePotentialDerivative_cancel_pi (ω : ℝ) (n : ℤ) :
    sourcePotentialDerivative ω n =
      2 * (n : ℝ) * Real.cos (2 * Real.pi * (n : ℝ) * ω) := by
  unfold sourcePotentialDerivative
  field_simp [Real.pi_ne_zero]
  ring

/-- Exact symbolic derivative in the production source-energy normalization. -/
theorem sourceWeightCounterexample_derivative_exact :
    deriv (sourceAtomRealEnergy 4 sourceWeightCounterexampleVector) (1 / 8) =
      25432 / 21 - (15962 / 35) * Real.sqrt 2 -
        126 * Real.sqrt 2 * Real.pi - 2 * Real.pi := by
  rw [(hasDerivAt_sourceAtomRealEnergy_transport
    4 sourceWeightCounterexampleVector (1 / 8)).deriv]
  unfold sourceAtomRealEnergyDerivative
  simp only [sourceWeightCounterexample_coordinates,
    sourceWeightCounterexampleCoefficients, Complex.ofReal_re, Complex.ofReal_im]
  unfold sourceContractRealDerivative
  simp only [zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  simp_rw [sourceEntryDerivative, sourceDiagonalDerivative_formula,
    sourcePotentialDerivative_cancel_pi, cos_counterexample_indices,
    sin_counterexample_indices]
  norm_num [sourceWeightCounterexampleReal, centeredIndex, cosEighthTable,
    sinEighthTable, Fin.sum_univ_succ] <;> ring

/-- Kernel-checked rational inequalities decide the sign; no floating-point
or external symbolic solver is trusted by this proof. -/
theorem sourceWeightCounterexample_derivative_neg :
    deriv (sourceAtomRealEnergy 4 sourceWeightCounterexampleVector) (1 / 8) < 0 := by
  rw [sourceWeightCounterexample_derivative_exact]
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : (14142135 / 10000000 : ℝ) < Real.sqrt 2 := by
    by_contra h
    have hle : Real.sqrt 2 ≤ (14142135 / 10000000 : ℝ) := le_of_not_gt h
    have hm := mul_le_mul hle hle hs0 (show (0 : ℝ) ≤ 14142135 / 10000000 by norm_num)
    nlinarith
  have hp : (3141592 / 1000000 : ℝ) < Real.pi := by
    exact Real.pi_gt_d6
  have hprod : (14142135 / 10000000 : ℝ) * (3141592 / 1000000) ≤
      Real.sqrt 2 * Real.pi :=
    mul_le_mul hs.le hp.le (by norm_num) hs0
  nlinarith

/-- Every source-energy jet from order one through eight vanishes for this
same exact vector. -/
theorem sourceWeightCounterexample_jets_through_eight :
    ∀ j : ℕ, 1 ≤ j → j ≤ 8 →
      iteratedDeriv j (sourceAtomRealEnergy 4 sourceWeightCounterexampleVector) 0 = 0 := by
  apply sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
  · simpa using sourceWeightCounterexample_boundaryFlat
  · simpa using sourceWeightCounterexample_even

/-- Positive ninth source-energy jet for the same vector with negative
interior first derivative. This disproves a carrier-wide jet-to-sign shortcut. -/
theorem sourceWeightCounterexample_ninthJet :
    iteratedDeriv 9 (sourceAtomRealEnergy 4 sourceWeightCounterexampleVector) 0 =
      1152 * (2 * Real.pi) ^ 8 := by
  rw [iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
    4 sourceWeightCounterexampleVector
    (by simpa using sourceWeightCounterexample_boundaryFlat)
    (by simpa using sourceWeightCounterexample_even)]
  simp only [sourceWeightCounterexample_coordinates,
    sourceWeightCounterexample_fourthMoment]
  norm_num [Complex.normSq] <;> ring

/-- The falsified statement is universal positivity on the even boundary-flat
carrier. No claim is made that the counterexample is a canonical ground mode. -/
theorem not_all_evenBoundaryFlat_sourceDerivatives_nonneg :
    ¬ (∀ x : EuclideanSpace ℂ (Fin 9),
      BoundaryFlatCoefficients 4 ((EuclideanSpace.equiv (Fin 9) ℂ) x) →
      ((EuclideanSpace.equiv (Fin 9) ℂ) x) ∈ evenCoefficientSubspace 4 →
      ∀ ω : ℝ, 0 < ω → ω < 1 → 0 ≤ deriv (sourceAtomRealEnergy 4 x) ω) := by
  intro h
  have hn := h sourceWeightCounterexampleVector
    (by simpa using sourceWeightCounterexample_boundaryFlat)
    (by simpa using sourceWeightCounterexample_even)
    (1 / 8) (by norm_num) (by norm_num)
  exact (not_lt_of_ge hn) sourceWeightCounterexample_derivative_neg

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceWeightCounterexample_derivative_exact
#print axioms Zeta23.CCM.sourceWeightCounterexample_derivative_neg
#print axioms Zeta23.CCM.sourceWeightCounterexample_ninthJet
#print axioms Zeta23.CCM.not_all_evenBoundaryFlat_sourceDerivatives_nonneg
