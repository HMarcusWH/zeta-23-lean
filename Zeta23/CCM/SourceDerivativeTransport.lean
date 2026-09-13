import Zeta23.CCM.DictionaryRegularity
import Zeta23.CCM.ConstrainedCanonicalSector
import Zeta23.CCM.CanonicalPolePrimeDiscrepancy

noncomputable section

namespace Zeta23.CCM

open Complex Matrix
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03E: source-coordinate D transport

This module theorem-locks the source-coordinate second-derivative identity
behind the production endpoint jets.  The low-level calculation is carried out
on the existing real analytic shadow, but the final theorem is for the genuine
complex `sourceAtomRealEnergy`: complex coefficients are decomposed into their
real and imaginary coordinate vectors exactly, rather than silently reusing a
real-vector result.

The rank-two defect is retained explicitly until the coefficient-sum hypothesis
kills it.  No positivity or sign theorem is asserted.
-/

/-- Closed second derivative of the diagonal source datum. -/
theorem sourceDiagonalSecondDerivative_formula
    (ω : ℝ) (n : ℤ) :
    sourceDiagonalSecondDerivative ω n =
      -8 * Real.pi * (n : ℝ) *
          Real.sin (2 * Real.pi * (n : ℝ) * ω)
      - 8 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ω *
          Real.cos (2 * Real.pi * (n : ℝ) * ω) := by
  let a : ℝ := 2 * Real.pi * (n : ℝ)
  have hfun : (fun t : ℝ => sourceDiagonalDerivative t n) =
      fun t => 2 * Real.cos (a * t) +
        2 * t * (-Real.sin (a * t) * a) := by
    funext t
    simpa [a] using sourceDiagonalDerivative_formula t n
  unfold sourceDiagonalSecondDerivative
  rw [hfun]
  have harg : HasDerivAt (fun t : ℝ => a * t) a ω := by
    simpa using (hasDerivAt_id ω).const_mul a
  have hleft : HasDerivAt (fun t : ℝ => 2 * Real.cos (a * t))
      (2 * (-Real.sin (a * ω) * a)) ω := by
    simpa [mul_assoc] using harg.cos.const_mul (2 : ℝ)
  have htwot : HasDerivAt (fun t : ℝ => 2 * t) 2 ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 : ℝ)
  have hinner : HasDerivAt (fun t : ℝ => -Real.sin (a * t) * a)
      (-(Real.cos (a * ω) * a) * a) ω := by
    simpa [mul_assoc] using harg.sin.neg.mul_const a
  rw [deriv_fun_add hleft.differentiableAt
    (htwot.mul hinner).differentiableAt]
  rw [hleft.deriv]
  rw [deriv_fun_mul htwot.differentiableAt hinner.differentiableAt]
  rw [htwot.deriv, hinner.deriv]
  dsimp [a]
  ring

/-- Exact entrywise second-derivative transport.  The first term is the
`D S D` contribution and the remaining two terms form the rank-two defect. -/
theorem sourceEntrySecondDerivative_transport
    (ω : ℝ) (n m : ℤ) :
    sourceEntrySecondDerivative ω n m =
      -(2 * Real.pi) ^ 2 * (n : ℝ) * (m : ℝ) *
          sourceEntryReal ω n m
      - 4 * Real.pi *
          ((n : ℝ) * Real.sin (2 * Real.pi * (n : ℝ) * ω) +
            (m : ℝ) * Real.sin (2 * Real.pi * (m : ℝ) * ω)) := by
  by_cases h : n = m
  · subst m
    rw [sourceEntrySecondDerivative, if_pos rfl,
      sourceDiagonalSecondDerivative_formula]
    simp [sourceEntryReal, sourceDiagonalReal]
    ring
  · rw [sourceEntrySecondDerivative, if_neg h, sourceEntryReal, if_neg h]
    unfold sourcePotentialSecondDerivative sourcePotentialReal
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
    field_simp [Real.pi_ne_zero, hnmR]
    push_cast
    ring

/-- Centered-index action on real coefficient coordinates. -/
def sourceIndexActionReal
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) :
    Fin (2 * K + 1) → ℝ :=
  fun i => (centeredIndex K i : ℝ) * u i

/-- Scalar carrying the rank-two second-derivative defect. -/
def sourceDerivativeDefectReal
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) (ω : ℝ) : ℝ :=
  ∑ i,
    (centeredIndex K i : ℝ) *
      Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) * u i

private theorem sum_sum_rankTwo_real
    {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) :
    (∑ i, ∑ j, u i * (v i + v j) * u j) =
      2 * (∑ i, u i) * (∑ i, v i * u i) := by
  have hleft :
      (∑ i, ∑ j, u i * v i * u j) =
        (∑ i, u i * v i) * (∑ j, u j) := by
    calc
      _ = ∑ i, (u i * v i) * (∑ j, u j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  have hright :
      (∑ i, ∑ j, u i * v j * u j) =
        (∑ i, u i) * (∑ j, v j * u j) := by
    calc
      _ = ∑ i, u i * (∑ j, v j * u j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_mul]
  have huv :
      (∑ i, u i * v i) = ∑ i, v i * u i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    (∑ i, ∑ j, u i * (v i + v j) * u j) =
        (∑ i, ∑ j, u i * v i * u j) +
          (∑ i, ∑ j, u i * v j * u j) := by
      simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    _ = _ := by
      rw [hleft, hright, huv]
      ring

private theorem sum_sum_rankTwo_scaled_real
    {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (c : ℝ) :
    (∑ i, ∑ j, u i * (c * (v i + v j)) * u j) =
      2 * c * (∑ i, u i) * (∑ i, v i * u i) := by
  calc
    (∑ i, ∑ j, u i * (c * (v i + v j)) * u j) =
        c * (∑ i, ∑ j, u i * (v i + v j) * u j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [sum_sum_rankTwo_real u v]; ring

/-- Full real contraction identity before zero-sum cancellation. -/
theorem sourceContractRealSecondDerivative_transport_with_defect
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) (ω : ℝ) :
    sourceContractRealSecondDerivative K u ω =
      -(2 * Real.pi) ^ 2 *
          sourceContractReal K (sourceIndexActionReal K u) ω
      - 8 * Real.pi * coefficientSumReal K u *
          sourceDerivativeDefectReal K u ω := by
  let v : Fin (2 * K + 1) → ℝ := fun i =>
    (centeredIndex K i : ℝ) *
      Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω)
  unfold sourceContractRealSecondDerivative sourceContractReal
    sourceIndexActionReal coefficientSumReal sourceDerivativeDefectReal
  simp_rw [sourceEntrySecondDerivative_transport]
  have hmain :
      (∑ i, ∑ j,
        u i *
          (-(2 * Real.pi) ^ 2 * (centeredIndex K i : ℝ) *
              (centeredIndex K j : ℝ) *
              sourceEntryReal ω (centeredIndex K i) (centeredIndex K j)) *
          u j) =
        -(2 * Real.pi) ^ 2 *
          ∑ i, ∑ j,
            ((centeredIndex K i : ℝ) * u i) *
              sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) *
              ((centeredIndex K j : ℝ) * u j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hrank :
      (∑ i, ∑ j,
        u i *
          (4 * Real.pi *
            ((centeredIndex K i : ℝ) *
                Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) +
              (centeredIndex K j : ℝ) *
                Real.sin (2 * Real.pi * (centeredIndex K j : ℝ) * ω))) *
          u j) =
        8 * Real.pi * (∑ i, u i) *
          ∑ i,
            (centeredIndex K i : ℝ) *
              Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) * u i := by
    calc
      _ = 2 * (4 * Real.pi) * (∑ i, u i) *
          ∑ i,
            (centeredIndex K i : ℝ) *
              Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) * u i := by
        simpa [v] using
          (sum_sum_rankTwo_scaled_real u v (4 * Real.pi))
      _ = _ := by ring
  calc
    (∑ i, ∑ j,
      u i *
        (-(2 * Real.pi) ^ 2 * (centeredIndex K i : ℝ) *
            (centeredIndex K j : ℝ) *
            sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) -
          4 * Real.pi *
            ((centeredIndex K i : ℝ) *
                Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) +
              (centeredIndex K j : ℝ) *
                Real.sin (2 * Real.pi * (centeredIndex K j : ℝ) * ω))) *
        u j) =
      (∑ i, ∑ j,
        u i *
          (-(2 * Real.pi) ^ 2 * (centeredIndex K i : ℝ) *
              (centeredIndex K j : ℝ) *
              sourceEntryReal ω (centeredIndex K i) (centeredIndex K j)) *
          u j) -
        (∑ i, ∑ j,
          u i *
            (4 * Real.pi *
              ((centeredIndex K i : ℝ) *
                  Real.sin (2 * Real.pi * (centeredIndex K i : ℝ) * ω) +
                (centeredIndex K j : ℝ) *
                  Real.sin (2 * Real.pi * (centeredIndex K j : ℝ) * ω))) *
            u j) := by
      simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
    _ = _ := by rw [hmain, hrank]

/-- Zero coefficient sum kills the entire rank-two second-derivative defect. -/
theorem sourceContractRealSecondDerivative_transport
    (K : ℕ) (u : Fin (2 * K + 1) → ℝ) (ω : ℝ)
    (hsum : coefficientSumReal K u = 0) :
    sourceContractRealSecondDerivative K u ω =
      -(2 * Real.pi) ^ 2 *
        sourceContractReal K (sourceIndexActionReal K u) ω := by
  rw [sourceContractRealSecondDerivative_transport_with_defect, hsum]
  ring

/-- Real-coordinate decomposition of the genuine complex production energy. -/
theorem sourceAtomRealEnergy_eq_re_im_contracts
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    sourceAtomRealEnergy K x ω =
      sourceContractReal K
          (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).re) ω +
        sourceContractReal K
          (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).im) ω := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  unfold sourceAtomRealEnergy matrixRealEnergy quadraticForm sourceContractReal
  simp_rw [sourceMatrix_apply, sourceEntry_eq_ofReal]
  change Complex.reCLM (∑ i, ∑ j,
      (starRingEnd ℂ) (u i) *
        (sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) : ℂ) *
        u j) = _
  rw [map_sum]
  simp_rw [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  change
    Complex.re
        ((starRingEnd ℂ) (u i) *
          (sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) : ℂ) *
          u j) =
      (u i).re * sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) * (u j).re +
        (u i).im * sourceEntryReal ω (centeredIndex K i) (centeredIndex K j) * (u j).im
  simp only [starRingEnd_apply, Complex.star_def, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- First derivative of the production source energy, expressed through the
existing real derivative contractions on the real and imaginary coordinates. -/
def sourceAtomRealEnergyDerivative
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) : ℝ :=
  sourceContractRealDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).re) ω +
    sourceContractRealDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).im) ω

/-- Second derivative of the production source energy. -/
def sourceAtomRealEnergySecondDerivative
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) : ℝ :=
  sourceContractRealSecondDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).re) ω +
    sourceContractRealSecondDerivative K
      (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).im) ω

/-- Exact first derivative of the genuine production source energy. -/
theorem hasDerivAt_sourceAtomRealEnergy_transport
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    HasDerivAt (sourceAtomRealEnergy K x)
      (sourceAtomRealEnergyDerivative K x ω) ω := by
  rw [show sourceAtomRealEnergy K x = fun t =>
      sourceContractReal K
          (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).re) t +
        sourceContractReal K
          (fun i => (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i).im) t by
    funext t
    exact sourceAtomRealEnergy_eq_re_im_contracts K x t]
  exact (hasDerivAt_sourceContractReal K _ ω).add
    (hasDerivAt_sourceContractReal K _ ω)

/-- Exact second derivative of the genuine production source energy. -/
theorem hasDerivAt_sourceAtomRealEnergyDerivative_transport
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    HasDerivAt (sourceAtomRealEnergyDerivative K x)
      (sourceAtomRealEnergySecondDerivative K x ω) ω := by
  unfold sourceAtomRealEnergyDerivative sourceAtomRealEnergySecondDerivative
  exact (hasDerivAt_sourceContractRealDerivative K _ ω).add
    (hasDerivAt_sourceContractRealDerivative K _ ω)

/-- Euclidean centered-index action used by the production transport theorem. -/
def sourceIndexAction
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).symm
    (indexMatrix K *ᵥ
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)

@[simp] theorem sourceIndexAction_coordinates
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) (sourceIndexAction K x) =
      indexMatrix K *ᵥ
        (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x := by
  unfold sourceIndexAction
  exact (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).apply_symm_apply _

/-- Zero complex coefficient sum implies zero real and imaginary coordinate
sums. -/
theorem coefficientSumReal_re_im_eq_zero_of_sum_eq_zero
    (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ)
    (hsum : ∑ i, u i = 0) :
    coefficientSumReal K (fun i => (u i).re) = 0 ∧
      coefficientSumReal K (fun i => (u i).im) = 0 := by
  unfold coefficientSumReal
  have hre := congrArg (fun z : ℂ => Complex.reCLM z) hsum
  have him := congrArg (fun z : ℂ => Complex.imCLM z) hsum
  simpa only [map_sum, map_zero] using And.intro hre him

/-- Production `D`-transport: after the exact zero-moment condition kills the
rank-two defect, two source-coordinate derivatives equal one centered-index
transport on the coefficient vector. -/
theorem sourceAtomRealEnergySecondDerivative_eq_indexAction
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ)
    (hsum :
      ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0) :
    sourceAtomRealEnergySecondDerivative K x ω =
      -(2 * Real.pi) ^ 2 *
        sourceAtomRealEnergy K (sourceIndexAction K x) ω := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  obtain ⟨hre, him⟩ := coefficientSumReal_re_im_eq_zero_of_sum_eq_zero K u hsum
  rw [sourceAtomRealEnergy_eq_re_im_contracts]
  unfold sourceAtomRealEnergySecondDerivative
  rw [sourceContractRealSecondDerivative_transport K (fun i => (u i).re) ω hre,
    sourceContractRealSecondDerivative_transport K (fun i => (u i).im) ω him]
  rw [sourceIndexAction_coordinates]
  unfold sourceIndexActionReal
  simp only [indexMatrix_mulVec_apply]
  change
    -(2 * Real.pi) ^ 2 * sourceContractReal K (fun i => (centeredIndex K i : ℝ) * (u i).re) ω +
        -(2 * Real.pi) ^ 2 * sourceContractReal K (fun i => (centeredIndex K i : ℝ) * (u i).im) ω =
      -(2 * Real.pi) ^ 2 *
        (sourceContractReal K
            (fun i => (((centeredIndex K i : ℂ) * u i)).re) ω +
          sourceContractReal K
            (fun i => (((centeredIndex K i : ℂ) * u i)).im) ω)
  have hreIndex :
      (fun i => (((centeredIndex K i : ℂ) * u i)).re) =
        (fun i => (centeredIndex K i : ℝ) * (u i).re) := by
    funext i
    simp [Complex.mul_re]
  have himIndex :
      (fun i => (((centeredIndex K i : ℂ) * u i)).im) =
        (fun i => (centeredIndex K i : ℝ) * (u i).im) := by
    funext i
    simp [Complex.mul_im]
  rw [hreIndex, himIndex]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceEntrySecondDerivative_transport
#print axioms Zeta23.CCM.sourceContractRealSecondDerivative_transport
#print axioms Zeta23.CCM.sourceAtomRealEnergy_eq_re_im_contracts
#print axioms Zeta23.CCM.sourceAtomRealEnergySecondDerivative_eq_indexAction