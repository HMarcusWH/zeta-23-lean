import Zeta23.CCM.DictionaryArchEntries
import Zeta23.CCM.DictionaryFiniteExpansion
import Zeta23.CCM.DictionaryArchFourier

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators FourierTransform

/-!
# Full finite-dictionary arch-density packaging

The generic positive-density identity in `DictionaryArchSourceBridge` already
contains the analytic content needed for the small-aperture archimedean bound.
This file supplies only the missing finite-sum packaging for the production
`dictionaryTest`.

No RH hypothesis, positivity hypothesis, project axiom, or placeholder proof is
introduced.
-/

/-- Every production basis test has an integrable Fourier transform.  The
diagonal case is already theorem-backed.  Off the diagonal, the displacement
identity reduces the paper transform to a nonzero scalar multiple of a
difference of the two already-integrable scalar source transforms. -/
theorem integrable_fourier_dictionaryBasisTest
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable (𝓕 (dictionaryBasisTest n m L)) := by
  by_cases hnm : n = m
  · subst m
    exact integrable_fourier_dictionaryBasisTest_diag hL n
  · let c : ℂ := (((n - m : ℤ) : ℂ))
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast hnmZ
    have hN :=
      Zeta23.EF.integrable_paperFT_ofReal
        (integrable_fourier_dictionarySourceTest hL n)
    have hM :=
      Zeta23.EF.integrable_paperFT_ofReal
        (integrable_fourier_dictionarySourceTest hL m)
    have hscaled := (hN.sub hM).const_mul c⁻¹
    have hpaper :
        Integrable
          (fun tau : ℝ =>
            Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ)) := by
      refine hscaled.congr (Filter.Eventually.of_forall fun tau => ?_)
      have hrel :=
        paperFT_dictionaryBasisTest_displacement_eq_sourceTest_sub
          hL hnm tau
      change
        c⁻¹ *
            (Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
              Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ)) =
          Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ)
      rw [← hrel]
      change
        c⁻¹ *
            (c * Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ)) =
          Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ)
      rw [inv_mul_cancel₀ hc, one_mul]
    exact integrable_fourier_of_integrable_paperFT hpaper

/-- Every production basis test has an integrable real-frequency paper
transform. -/
theorem integrable_paperFT_dictionaryBasisTest
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionaryBasisTest n m L) (r : ℂ)) :=
  Zeta23.EF.integrable_paperFT_ofReal
    (integrable_fourier_dictionaryBasisTest hL n m)

/-- The full finite production dictionary has an integrable real-frequency
paper transform. -/
theorem integrable_paperFT_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable
      (fun r : ℝ => Zeta23.paperFT (dictionaryTest N u L) (r : ℂ)) := by
  have hint (i j : Fin (2 * N + 1)) :
      Integrable
        (fun r : ℝ =>
          (starRingEnd ℂ) (u i) *
            Zeta23.paperFT
              (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
              (r : ℂ) *
            u j) :=
    ((integrable_paperFT_dictionaryBasisTest hL
      (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _
  have hsum :
      Integrable
        (fun r : ℝ =>
          ∑ i, ∑ j,
            (starRingEnd ℂ) (u i) *
              Zeta23.paperFT
                (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
                (r : ℂ) *
              u j) := by
    exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint i j
  refine hsum.congr (Filter.Eventually.of_forall fun r => ?_)
  exact (paperFT_dictionaryTest_eq_basis_sum N u hL (r : ℂ)).symm

/-- The full finite production dictionary has an integrable Mathlib Fourier
transform. -/
theorem integrable_fourier_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable (𝓕 (dictionaryTest N u L)) :=
  integrable_fourier_of_integrable_paperFT
    (integrable_paperFT_dictionaryTest N u hL)

/-- The full finite dictionary has an integrable full-`mu` archimedean
integrand, by finite contraction of the already-proved all-entry result. -/
theorem integrable_paperFT_dictionaryTest_mul_mu
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable
      (fun tau : ℝ =>
        Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
          (Zeta23.mu tau : ℂ)) := by
  have hint (i j : Fin (2 * N + 1)) :
      Integrable
        (fun tau : ℝ =>
          (starRingEnd ℂ) (u i) *
            (Zeta23.paperFT
                (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
                (tau : ℂ) *
              (Zeta23.mu tau : ℂ)) *
            u j) :=
    ((integrable_paperFT_dictionaryBasisTest_mul_mu hL
      (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _
  have hsum :
      Integrable
        (fun tau : ℝ =>
          ∑ i, ∑ j,
            (starRingEnd ℂ) (u i) *
              (Zeta23.paperFT
                  (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
                  (tau : ℂ) *
                (Zeta23.mu tau : ℂ)) *
              u j) := by
    exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint i j
  refine hsum.congr (Filter.Eventually.of_forall fun tau => ?_)
  change
    (∑ i, ∑ j,
      (starRingEnd ℂ) (u i) *
        (Zeta23.paperFT
            (dictionaryBasisTest (centeredIndex N i) (centeredIndex N j) L)
            (tau : ℂ) *
          (Zeta23.mu tau : ℂ)) *
        u j) =
      Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
        (Zeta23.mu tau : ℂ)
  rw [paperFT_dictionaryTest_eq_basis_sum N u hL (tau : ℂ)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact `mu - mu(0)` integrability hypothesis required by the generic
positive-density theorem is available for every full finite dictionary. -/
theorem integrable_paperFT_dictionaryTest_mul_mu_sub_mu_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable
      (fun tau : ℝ =>
        Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
          ((Zeta23.mu tau - Zeta23.mu 0 : ℝ) : ℂ)) := by
  have hmu := integrable_paperFT_dictionaryTest_mul_mu N u hL
  have hpaper := integrable_paperFT_dictionaryTest N u hL
  have hconst :
      Integrable
        (fun tau : ℝ =>
          Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
            (Zeta23.mu 0 : ℂ)) :=
    hpaper.mul_const _
  refine (hmu.sub hconst).congr
    (Filter.Eventually.of_forall fun tau => ?_)
  change
    Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
          (Zeta23.mu tau : ℂ) -
        Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
          (Zeta23.mu 0 : ℂ) =
      Zeta23.paperFT (dictionaryTest N u L) (tau : ℂ) *
        ((Zeta23.mu tau - Zeta23.mu 0 : ℝ) : ℂ)
  push_cast
  ring

/-- The generic positive-density archimedean identity specialized to the actual
full production `dictionaryTest`. -/
theorem dictionaryArchRHS_dictionaryTest_eq_mu_zero_add_archDensity_integral
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryArchRHS (dictionaryTest N u L) =
      (((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) *
          dictionaryTest N u L 0) +
        (2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (dictionaryTest N u L 0 - dictionaryTest N u L x) *
            (archDensity x : ℂ) := by
  have hk := continuous_dictionaryTest N u hL
  have hki : Integrable (dictionaryTest N u L) :=
    hk.integrable_of_hasCompactSupport
      (dictionaryTest_hasCompactSupport N u L)
  have hFk := integrable_fourier_dictionaryTest N u hL
  have heven : ∀ x : ℝ,
      dictionaryTest N u L (-x) = dictionaryTest N u L x :=
    fun x => dictionaryTest_neg N u L x
  have hmu :=
    integrable_paperFT_dictionaryTest_mul_mu_sub_mu_zero N u hL
  exact dictionaryArchRHS_eq_mu_zero_add_archDensity_integral
    hk hki hFk heven hmu

/-- The defect integrand occurring in the full-dictionary density formula is
integrable on the positive half-line. -/
theorem integrableOn_dictionaryTest_sub_mul_archDensity_Ioi
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    IntegrableOn
      (fun x : ℝ =>
        (dictionaryTest N u L 0 - dictionaryTest N u L x) *
          (archDensity x : ℂ))
      (Ioi 0) := by
  have hk := continuous_dictionaryTest N u hL
  have hki : Integrable (dictionaryTest N u L) :=
    hk.integrable_of_hasCompactSupport
      (dictionaryTest_hasCompactSupport N u L)
  exact integrableOn_sub_mul_archDensity_Ioi
    hk hki
    (integrable_fourier_dictionaryTest N u hL)
    (fun x => dictionaryTest_neg N u L x)
    (integrable_paperFT_dictionaryTest_mul_mu_sub_mu_zero N u hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.integrable_fourier_dictionaryBasisTest
#print axioms Zeta23.CCM.integrable_fourier_dictionaryTest
#print axioms Zeta23.CCM.integrable_paperFT_dictionaryTest_mul_mu_sub_mu_zero
#print axioms Zeta23.CCM.dictionaryArchRHS_dictionaryTest_eq_mu_zero_add_archDensity_integral
#print axioms Zeta23.CCM.integrableOn_dictionaryTest_sub_mul_archDensity_Ioi
