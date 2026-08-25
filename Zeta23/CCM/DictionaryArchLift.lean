import Zeta23.CCM.DictionaryPrimeLift

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-! # Finite dictionary archimedean-channel lift

Phase J3 of the deterministic R003 completion.  The full dictionary transform
is expanded only as a finite coefficient sum, and the integral is commuted only
with those finite sums using the all-entry integrability certificate from Phase
H.  The diagonal correction remains exactly the identity-channel scalar
`2*cCorrection(L)`.
-/

/-- The archimedean channel of the full finite dictionary is the coefficient
contraction of `-archComponent` plus the diagonal identity correction. -/
theorem dictionaryArchRHS_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryArchRHS (dictionaryTest N u L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          ((-archComponent (centeredIndex N i) (centeredIndex N j) L +
            (if i = j then 2 * cCorrection L else 0) : ℝ) : ℂ) *
          u j := by
  rw [dictionaryArchRHS_eq_integral_mu]
  have hfun :
      (fun τ : ℝ =>
        Zeta23.paperFT (dictionaryTest N u L) (τ : ℂ) *
          (Zeta23.mu τ : ℂ)) =
        fun τ : ℝ => ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (Zeta23.paperFT
                (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
                (τ : ℂ) * (Zeta23.mu τ : ℂ)) * u j := by
    funext τ
    rw [paperFT_dictionaryTest_eq_basis_sum N u hL (τ : ℂ)]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  have hint (i j : Fin (2 * N + 1)) : Integrable (fun τ : ℝ =>
      (starRingEnd ℂ) (u i) *
        (Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
            (τ : ℂ) * (Zeta23.mu τ : ℂ)) * u j) :=
    ((integrable_paperFT_dictionaryBasisTest_mul_mu hL
      (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Zeta23.integral_mul_const_C, Zeta23.integral_const_mul_C,
    ← dictionaryArchRHS_eq_integral_mu,
    dictionaryArchRHS_basis hL
      (centeredIndex N i) (centeredIndex N j)]
  simp only [(centeredIndex_injective N).eq_iff]

end Zeta23.CCM
