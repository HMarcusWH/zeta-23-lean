import Zeta23.CCM.DictionaryZeroSideBridge
import Zeta23.CCM.DictionaryRHSIdentity

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-!
# Full real finite-dictionary explicit-formula closure

After the exact finite zero-side bridge is available, the remaining
arbitrary-real-coefficient dictionary explicit formula is finite quadratic
algebra.  Each spectral-matrix entry is already absolutely summable over the
concrete zeta zeros.  Finite contraction therefore commutes with the zero sum,
and the exact matrix bridge plus the deterministic RHS identity closes the
full real dictionary endpoint.

No new analytic limit argument, regularity theorem, positivity claim, or
finite-to-infinite statement is introduced here.
-/

/-- Finite quadratic contraction commutes with the concrete zeta zero sum.

This is the only new summation step needed after the exact finite matrix bridge:
entrywise absolute summability is already theorem-authoritative upstream. -/
theorem dictionaryTransform_zero_sum_eq_quadraticForm_zeroSideMatrix
    (hs : ZetaSeam)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
      quadraticForm
        (zeroSideMatrix hs N L)
        (fun i => (u i : ℂ)) := by
  have hentry (i j : Fin (2 * N + 1)) :
      HasSum
        (fun ρ : (zetaZeros hs).carrier =>
          (starRingEnd ℂ) (u i : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) *
            (u j : ℂ))
        ((starRingEnd ℂ) (u i : ℂ) *
          zeroSideMatrix hs N L i j *
          (u j : ℂ)) := by
    have h :=
      (dictionarySpectralMatrix_zero_entry_summable hs N i j hL).hasSum
    have h' :=
      (h.mul_left ((starRingEnd ℂ) (u i : ℂ))).mul_right (u j : ℂ)
    simpa [zeroSideMatrix, mul_assoc] using h'

  have hrow (i : Fin (2 * N + 1)) :
      HasSum
        (fun ρ : (zetaZeros hs).carrier =>
          ∑ j,
            (starRingEnd ℂ) (u i : ℂ) *
              (((zetaZeros hs).mult ρ : ℂ) *
                dictionarySpectralMatrix N L (gammaOf ρ) i j) *
              (u j : ℂ))
        (∑ j,
          (starRingEnd ℂ) (u i : ℂ) *
            zeroSideMatrix hs N L i j *
            (u j : ℂ)) := by
    simpa using
      (hasSum_sum (s := Finset.univ)
        (fun j _ => hentry i j))

  have hdouble :
      HasSum
        (fun ρ : (zetaZeros hs).carrier =>
          ∑ i, ∑ j,
            (starRingEnd ℂ) (u i : ℂ) *
              (((zetaZeros hs).mult ρ : ℂ) *
                dictionarySpectralMatrix N L (gammaOf ρ) i j) *
              (u j : ℂ))
        (∑ i, ∑ j,
          (starRingEnd ℂ) (u i : ℂ) *
            zeroSideMatrix hs N L i j *
            (u j : ℂ)) := by
    simpa using
      (hasSum_sum (s := Finset.univ)
        (fun i _ => hrow i))

  have hpoint :
      (fun ρ : (zetaZeros hs).carrier =>
        ((zetaZeros hs).mult ρ : ℂ) *
          dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
      (fun ρ : (zetaZeros hs).carrier =>
        ∑ i, ∑ j,
          (starRingEnd ℂ) (u i : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) *
            (u j : ℂ)) := by
    funext ρ
    rw [dictionaryTransform_eq_quadraticForm_spectralMatrix
      N (fun i => (u i : ℂ)) hL (gammaOf ρ)]
    unfold quadraticForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

  rw [hpoint]
  simpa [quadraticForm] using hdouble.tsum_eq

/-- Full arbitrary-real finite-dictionary explicit-formula equality.

The proof direction is intentionally post-bridge: the exact zero-side matrix
identity now implies the full real dictionary identity by finite contraction. -/
theorem dictionaryTransform_zero_sum_eq_literatureRHS
    (hs : ZetaSeam)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
      Zeta23.EF.literatureRHS
        (dictionaryTest N (fun i => (u i : ℂ)) L) := by
  rw [dictionaryTransform_zero_sum_eq_quadraticForm_zeroSideMatrix
      hs N u hL,
    zeroSideMatrix_eq_dictionaryMatrix hs N hL]
  exact (literatureRHS_dictionaryTest_eq_quadraticForm N u hL).symm

/-- Packaged full real dictionary explicit formula, including the already-proved
absolute zero-side summability. -/
theorem dictionaryTransform_explicitFormula
    (hs : ZetaSeam)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) ∧
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
      Zeta23.EF.literatureRHS
        (dictionaryTest N (fun i => (u i : ℂ)) L) := by
  exact ⟨
    dictionaryTransform_zero_sum_summable hs N u hL,
    dictionaryTransform_zero_sum_eq_literatureRHS hs N u hL
  ⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTransform_zero_sum_eq_quadraticForm_zeroSideMatrix
#print axioms Zeta23.CCM.dictionaryTransform_zero_sum_eq_literatureRHS
#print axioms Zeta23.CCM.dictionaryTransform_explicitFormula
