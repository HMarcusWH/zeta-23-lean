import Zeta23.CCM.DictionaryArchSourceBridge
import Zeta23.CCM.Displacement

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set

/-!
Compiler draft for Phase E/G.  This intentionally depends only on the three
public Phase-D exports documented below:

* `dictionaryArchRHS_eq_integral_mu`
* `integrable_paperFT_dictionarySourceTest_mul_mu`
* `dictionaryArchRHS_sourceTest`
-/

/-- Fourier-side displacement identity for one off-diagonal basis test.  Both
source transforms are subtracted only after their physical integrands have been
certified integrable. -/
theorem paperFT_dictionaryBasisTest_displacement_eq_sourceTest_sub
    {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) (tau : ℝ) :
    (((n - m : ℤ) : ℂ)) *
        Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) =
      Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
        Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ) := by
  let c : ℂ := ((n - m : ℤ) : ℂ)
  have hfun :
      (fun y : ℝ => c * dictionaryBasisTest n m L y) =
        fun y => dictionarySourceTest n L y - dictionarySourceTest m L y := by
    funext y
    exact dictionaryBasisTest_displacement_eq_sourceTest_sub hL hnm y
  have hsmul :
      Zeta23.paperFT
          (fun y : ℝ => c * dictionaryBasisTest n m L y) (tau : ℂ) =
        c * Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) := by
    rw [Zeta23.paperFT_def, Zeta23.paperFT_def]
    have hpoint :
        (fun y : ℝ =>
            c * dictionaryBasisTest n m L y *
              Complex.exp (I * (tau : ℂ) * y)) =
          fun y => c *
            (dictionaryBasisTest n m L y *
              Complex.exp (I * (tau : ℂ) * y)) := by
      funext y
      ring
    rw [hpoint, Zeta23.integral_const_mul_C]
  have hkN := continuous_dictionarySourceTest n L
  have hkM := continuous_dictionarySourceTest m L
  have hkcN := dictionarySourceTest_hasCompactSupport hL n
  have hkcM := dictionarySourceTest_hasCompactSupport hL m
  have hsub :
      Zeta23.paperFT
          (fun y : ℝ =>
            dictionarySourceTest n L y - dictionarySourceTest m L y) (tau : ℂ) =
        Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
          Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ) := by
    rw [Zeta23.paperFT_def, Zeta23.paperFT_def, Zeta23.paperFT_def]
    have hiN : Integrable
        (fun y : ℝ => dictionarySourceTest n L y *
          Complex.exp (I * (tau : ℂ) * y)) :=
      (hkN.mul (by fun_prop)).integrable_of_hasCompactSupport hkcN.mul_right
    have hiM : Integrable
        (fun y : ℝ => dictionarySourceTest m L y *
          Complex.exp (I * (tau : ℂ) * y)) :=
      (hkM.mul (by fun_prop)).integrable_of_hasCompactSupport hkcM.mul_right
    have hpoint :
        (fun y : ℝ =>
            (dictionarySourceTest n L y - dictionarySourceTest m L y) *
              Complex.exp (I * (tau : ℂ) * y)) =
          fun y =>
            dictionarySourceTest n L y *
                Complex.exp (I * (tau : ℂ) * y) -
              dictionarySourceTest m L y *
                Complex.exp (I * (tau : ℂ) * y) := by
      funext y
      ring
    rw [hpoint, integral_sub hiN hiM]
  change c * Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) = _
  rw [← hsmul, hfun, hsub]

/-- The full `mu`-weighted literature integrand for an off-diagonal basis test
is genuinely integrable. -/
theorem integrable_paperFT_dictionaryBasisTest_mul_mu_of_ne
    {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) :
    Integrable (fun tau : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) *
        (Zeta23.mu tau : ℂ)) := by
  let c : ℂ := ((n - m : ℤ) : ℂ)
  have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast hnmZ
  have hmuN := integrable_paperFT_dictionarySourceTest_mul_mu hL n
  have hmuM := integrable_paperFT_dictionarySourceTest_mul_mu hL m
  have hdiff : Integrable (fun tau : ℝ =>
      (Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
          Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ)) *
        (Zeta23.mu tau : ℂ)) := by
    refine (hmuN.sub hmuM).congr ?_
    filter_upwards with tau
    change
      Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) *
          (Zeta23.mu tau : ℂ) -
        Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ) *
          (Zeta23.mu tau : ℂ) = _
    ring
  have hscaled := hdiff.const_mul c⁻¹
  refine hscaled.congr ?_
  filter_upwards with tau
  have hpaper :=
    paperFT_dictionaryBasisTest_displacement_eq_sourceTest_sub hL hnm tau
  change c⁻¹ *
      ((Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
          Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ)) *
        (Zeta23.mu tau : ℂ)) = _
  rw [← hpaper]
  calc
    c⁻¹ *
        ((c * Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ)) *
          (Zeta23.mu tau : ℂ)) =
      (c⁻¹ * c) *
        (Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) *
          (Zeta23.mu tau : ℂ)) := by ring
    _ = Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) *
          (Zeta23.mu tau : ℂ) := by
      rw [inv_mul_cancel₀ hc, one_mul]

/-- Off the diagonal, the actual literature archimedean channel is minus the
fork-owned archimedean matrix component. -/
theorem dictionaryArchRHS_basis_of_ne
    {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) :
    dictionaryArchRHS (dictionaryBasisTest n m L) =
      -((archComponent n m L : ℝ) : ℂ) := by
  let c : ℂ := ((n - m : ℤ) : ℂ)
  have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast hnmZ
  have hfun :
      (fun y : ℝ => c * dictionaryBasisTest n m L y) =
        fun y => dictionarySourceTest n L y - dictionarySourceTest m L y := by
    funext y
    exact dictionaryBasisTest_displacement_eq_sourceTest_sub hL hnm y
  have hlin_smul :
      dictionaryArchRHS
          (fun y : ℝ => c * dictionaryBasisTest n m L y) =
        c * dictionaryArchRHS (dictionaryBasisTest n m L) := by
    rw [dictionaryArchRHS_eq_integral_mu,
      dictionaryArchRHS_eq_integral_mu]
    have hpaper (tau : ℝ) :
        Zeta23.paperFT
            (fun y : ℝ => c * dictionaryBasisTest n m L y) (tau : ℂ) =
          c * Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) := by
      rw [Zeta23.paperFT_def, Zeta23.paperFT_def]
      have hpoint :
          (fun y : ℝ =>
              c * dictionaryBasisTest n m L y *
                Complex.exp (I * (tau : ℂ) * y)) =
            fun y => c *
              (dictionaryBasisTest n m L y *
                Complex.exp (I * (tau : ℂ) * y)) := by
        funext y
        ring
      rw [hpoint, Zeta23.integral_const_mul_C]
    simp_rw [hpaper]
    have hpoint :
        (fun tau : ℝ =>
            (c * Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ)) *
              (Zeta23.mu tau : ℂ)) =
          fun tau : ℝ => c *
            (Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) *
              (Zeta23.mu tau : ℂ)) := by
      funext tau
      ring
    rw [hpoint, Zeta23.integral_const_mul_C]
  have hkN := continuous_dictionarySourceTest n L
  have hkM := continuous_dictionarySourceTest m L
  have hkcN := dictionarySourceTest_hasCompactSupport hL n
  have hkcM := dictionarySourceTest_hasCompactSupport hL m
  have hlin_sub :
      dictionaryArchRHS
          (fun y : ℝ => dictionarySourceTest n L y - dictionarySourceTest m L y) =
        dictionaryArchRHS (dictionarySourceTest n L) -
          dictionaryArchRHS (dictionarySourceTest m L) := by
    rw [dictionaryArchRHS_eq_integral_mu,
      dictionaryArchRHS_eq_integral_mu,
      dictionaryArchRHS_eq_integral_mu]
    have hpaper (tau : ℝ) :
        Zeta23.paperFT
            (fun y : ℝ =>
              dictionarySourceTest n L y - dictionarySourceTest m L y) (tau : ℂ) =
          Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
            Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ) := by
      rw [Zeta23.paperFT_def, Zeta23.paperFT_def, Zeta23.paperFT_def]
      have hiN : Integrable
          (fun y : ℝ => dictionarySourceTest n L y *
            Complex.exp (I * (tau : ℂ) * y)) :=
        (hkN.mul (by fun_prop)).integrable_of_hasCompactSupport hkcN.mul_right
      have hiM : Integrable
          (fun y : ℝ => dictionarySourceTest m L y *
            Complex.exp (I * (tau : ℂ) * y)) :=
        (hkM.mul (by fun_prop)).integrable_of_hasCompactSupport hkcM.mul_right
      have hpoint :
          (fun y : ℝ =>
              (dictionarySourceTest n L y - dictionarySourceTest m L y) *
                Complex.exp (I * (tau : ℂ) * y)) =
            fun y =>
              dictionarySourceTest n L y *
                  Complex.exp (I * (tau : ℂ) * y) -
                dictionarySourceTest m L y *
                  Complex.exp (I * (tau : ℂ) * y) := by
        funext y
        ring
      rw [hpoint, integral_sub hiN hiM]
    simp_rw [hpaper]
    have hmuN := integrable_paperFT_dictionarySourceTest_mul_mu hL n
    have hmuM := integrable_paperFT_dictionarySourceTest_mul_mu hL m
    have hpoint :
        (fun tau : ℝ =>
            (Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) -
                Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ)) *
              (Zeta23.mu tau : ℂ)) =
          fun tau : ℝ =>
            Zeta23.paperFT (dictionarySourceTest n L) (tau : ℂ) *
                (Zeta23.mu tau : ℂ) -
              Zeta23.paperFT (dictionarySourceTest m L) (tau : ℂ) *
                (Zeta23.mu tau : ℂ) := by
      funext tau
      ring
    rw [hpoint, integral_sub hmuN hmuM]
  have hdisp :
      c * dictionaryArchRHS (dictionaryBasisTest n m L) =
        ((alphaL n L - alphaL m L : ℝ) : ℂ) := by
    rw [← hlin_smul, hfun, hlin_sub,
      dictionaryArchRHS_sourceTest hL n,
      dictionaryArchRHS_sourceTest hL m]
    push_cast
    ring
  have hcompReal := archComponent_displacement hnm L
  have hcomp :
      c * (-((archComponent n m L : ℝ) : ℂ)) =
        ((alphaL n L - alphaL m L : ℝ) : ℂ) := by
    dsimp [c]
    exact_mod_cast hcompReal
  apply mul_left_cancel₀ hc
  rw [hdisp, hcomp]

/- Phase G should live with the diagonal theorem and use no analysis.  The
parameter `hdiag` records the exact public signature Phase F must export. -/
theorem dictionaryArchRHS_basis_of_diag
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    (∀ j : ℤ,
      dictionaryArchRHS (dictionaryBasisTest j j L) =
        -((archComponent j j L : ℝ) : ℂ) +
          ((2 * cCorrection L : ℝ) : ℂ)) →
    dictionaryArchRHS (dictionaryBasisTest n m L) =
      -((archComponent n m L : ℝ) : ℂ) +
        if n = m then ((2 * cCorrection L : ℝ) : ℂ) else 0 := by
  intro hdiag
  by_cases hnm : n = m
  · subst m
    simpa using hdiag n
  · simpa [hnm] using dictionaryArchRHS_basis_of_ne hL hnm

end Zeta23.CCM
