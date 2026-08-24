import Zeta23.CCM.DictionaryArchDiagonal

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped FourierTransform Interval

/-! # Diagonal literature-to-physical archimedean bridge

This module is the Phase-G1 continuation of `DictionaryArchDiagonal`.  The
analytic diagonal prerequisites are already proved there; this file only
converts the generic infinite-half-line density representation into the
finite-aperture physical functional used by the CCM matrix entry.
-/

private theorem dictionaryBasisTest_diag_zero_physical
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryBasisTest n n L 0 = 1 := by
  simp [dictionaryBasisTest, kernel_zero hL.le]

private theorem continuous_dictionaryBasisTest_diag_physical
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Continuous (dictionaryBasisTest n n L) := by
  unfold dictionaryBasisTest
  exact continuous_const.mul (kernel_continuous hL n n)

private theorem integrable_dictionaryBasisTest_diag_physical
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Integrable (dictionaryBasisTest n n L) := by
  unfold dictionaryBasisTest
  exact (kernel_integrable hL n n).const_mul (1 / 2 : ℂ)

/-- The finite-part physical integrand of a diagonal basis entry is genuinely
integrable on the positive half-line. -/
theorem integrableOn_dictionaryBasisTest_diag_sub_exp_mul_archDensity_Ioi
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    IntegrableOn (fun x : ℝ =>
      (dictionaryBasisTest n n L x - (Real.exp (-x / 2) : ℂ)) *
        (archDensity x : ℂ)) (Ioi 0) := by
  have hk := continuous_dictionaryBasisTest_diag_physical hL n
  have hki := integrable_dictionaryBasisTest_diag_physical hL n
  have hFk := integrable_fourier_dictionaryBasisTest_diag hL n
  have heven : ∀ x : ℝ,
      dictionaryBasisTest n n L (-x) = dictionaryBasisTest n n L x :=
    fun x => dictionaryBasisTest_neg n n L x
  have hmu :=
    integrable_paperFT_dictionaryBasisTest_diag_mul_mu_sub_mu_zero hL n
  have hsub :=
    integrableOn_sub_mul_archDensity_Ioi hk hki hFk heven hmu
  have href : IntegrableOn (fun x : ℝ =>
      (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi.ofReal
  have hdifference := href.sub hsub
  refine hdifference.congr ?_
  filter_upwards with x
  rw [dictionaryBasisTest_diag_zero_physical hL n]
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- For a diagonal basis entry, the generic infinite-half-line density formula
is exactly the repository's finite-aperture physical functional. -/
theorem dictionaryArchRHS_basis_diag_eq_physical
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryArchRHS (dictionaryBasisTest n n L) =
      dictionaryArchPhysicalRHS (dictionaryBasisTest n n L) L := by
  let k : ℝ → ℂ := dictionaryBasisTest n n L
  have hk : Continuous k := by
    simpa [k] using continuous_dictionaryBasisTest_diag_physical hL n
  have hki : Integrable k := by
    simpa [k] using integrable_dictionaryBasisTest_diag_physical hL n
  have hFk : Integrable (𝓕 k) := by
    simpa [k] using integrable_fourier_dictionaryBasisTest_diag hL n
  have heven : ∀ x : ℝ, k (-x) = k x := by
    intro x
    simpa [k] using dictionaryBasisTest_neg n n L x
  have hk0 : k 0 = 1 := by
    simpa [k] using dictionaryBasisTest_diag_zero_physical hL n
  have hmu : Integrable (fun τ : ℝ =>
      Zeta23.paperFT k (τ : ℂ) *
        ((Zeta23.mu τ - Zeta23.mu 0 : ℝ) : ℂ)) := by
    simpa [k] using
      integrable_paperFT_dictionaryBasisTest_diag_mul_mu_sub_mu_zero hL n
  have hgeneric :=
    dictionaryArchRHS_eq_mu_zero_add_archDensity_integral
      hk hki hFk heven hmu
  have href : IntegrableOn (fun x : ℝ =>
      (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi.ofReal
  have hp : IntegrableOn (fun x : ℝ =>
      (k x - (Real.exp (-x / 2) : ℂ)) * (archDensity x : ℂ))
      (Ioi 0) := by
    simpa [k] using
      integrableOn_dictionaryBasisTest_diag_sub_exp_mul_archDensity_Ioi hL n
  have heminus : IntegrableOn (fun x : ℝ =>
      ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ))
      (Ioi 0) := by
    refine hp.neg.congr ?_
    filter_upwards with x
    simp only [Pi.neg_apply]
    ring
  have hone : IntegrableOn (fun x : ℝ =>
      (k 0 - k x) * (archDensity x : ℂ)) (Ioi 0) :=
    integrableOn_sub_mul_archDensity_Ioi hk hki hFk heven hmu
  have honeSplit :
      (∫ x : ℝ in Ioi 0,
          (k 0 - k x) * (archDensity x : ℂ)) =
        (∫ x : ℝ in Ioi 0,
          (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) +
        ∫ x : ℝ in Ioi 0,
          ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ) := by
    calc
      (∫ x : ℝ in Ioi 0,
          (k 0 - k x) * (archDensity x : ℂ)) =
          ∫ x : ℝ in Ioi 0,
            ((((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ) +
              (((Real.exp (-x / 2) : ℂ) - k x) *
                (archDensity x : ℂ))) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hk0]
        push_cast
        ring
      _ = (∫ x : ℝ in Ioi 0,
          (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) +
          ∫ x : ℝ in Ioi 0,
            ((Real.exp (-x / 2) : ℂ) - k x) *
              (archDensity x : ℂ) := by
        rw [integral_add href heminus]
  have htailRef : IntegrableOn (fun x : ℝ =>
      ((Real.exp (-x / 2) * archDensity x : ℝ) : ℂ)) (Ioi L) :=
    (integrableOn_exp_neg_half_mul_archDensity_Ioi hL).ofReal
  have heminusTail : IntegrableOn (fun x : ℝ =>
      ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ))
      (Ioi L) := by
    refine htailRef.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hL.trans hx
    have habs : L < |x| := by simpa [abs_of_pos hx0] using hx
    have hzero : k x = 0 := by
      simpa [k] using
        dictionaryBasisTest_eq_zero_of_lt_abs
          (n := n) (m := n) (L := L) (y := x) habs
    rw [hzero]
    push_cast
    ring
  have heminusSplit :
      (∫ x : ℝ in Ioi 0,
          ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ)) =
        (∫ x : ℝ in (0 : ℝ)..L,
          ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ)) +
        ∫ x : ℝ in Ioi L,
          ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ) := by
    exact (intervalIntegral.integral_interval_add_Ioi heminus heminusTail).symm
  have htailValue :
      (∫ x : ℝ in Ioi L,
          ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ)) =
        ∫ x : ℝ in Ioi L,
          ((Real.exp (-x / 2) * archDensity x : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hL.trans hx
    have habs : L < |x| := by simpa [abs_of_pos hx0] using hx
    have hzero : k x = 0 := by
      simpa [k] using
        dictionaryBasisTest_eq_zero_of_lt_abs
          (n := n) (m := n) (L := L) (y := x) habs
    rw [hzero]
    push_cast
    ring
  have hfiniteNeg :
      (∫ x : ℝ in (0 : ℝ)..L,
          ((Real.exp (-x / 2) : ℂ) - k x) * (archDensity x : ℂ)) =
        -(∫ x : ℝ in (0 : ℝ)..L,
          (k x - (Real.exp (-x / 2) : ℂ)) * (archDensity x : ℂ)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hreferenceCast :
      (∫ x : ℝ in Ioi 0,
        (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) =
        (((∫ x : ℝ in Ioi 0,
          (1 - Real.exp (-x / 2)) * archDensity x) : ℝ) : ℂ) := by
    exact integral_ofReal
  have htailCast :
      (∫ x : ℝ in Ioi L,
        ((Real.exp (-x / 2) * archDensity x : ℝ) : ℂ)) =
        (((∫ x : ℝ in Ioi L,
          Real.exp (-x / 2) * archDensity x) : ℝ) : ℂ) := by
    exact integral_ofReal
  have hconstant :
      ((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) +
          (2 : ℂ) * (∫ x : ℝ in Ioi 0,
            (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) +
          (2 : ℂ) * (∫ x : ℝ in Ioi L,
            ((Real.exp (-x / 2) * archDensity x : ℝ) : ℂ)) =
        -((2 * wCorrection L : ℝ) : ℂ) := by
    rw [hreferenceCast, htailCast]
    have hreal := congrArg (fun r : ℝ => (r : ℂ))
      (mu_zero_reference_tail_eq_neg_two_wCorrection hL)
    push_cast at hreal ⊢
    exact hreal
  change dictionaryArchRHS k = dictionaryArchPhysicalRHS k L
  calc
    dictionaryArchRHS k =
        (((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) * k 0) +
          (2 : ℂ) * ∫ x : ℝ in Ioi 0,
            (k 0 - k x) * (archDensity x : ℂ) := hgeneric
    _ = (((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) * k 0) +
          (2 : ℂ) *
            ((∫ x : ℝ in Ioi 0,
                (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) +
              ∫ x : ℝ in Ioi 0,
                ((Real.exp (-x / 2) : ℂ) - k x) *
                  (archDensity x : ℂ)) := by rw [honeSplit]
    _ = ((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) +
          (2 : ℂ) *
            ((∫ x : ℝ in Ioi 0,
                (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) +
              ∫ x : ℝ in Ioi 0,
                ((Real.exp (-x / 2) : ℂ) - k x) *
                  (archDensity x : ℂ)) := by rw [hk0, mul_one]
    _ = ((2 * Real.pi * Zeta23.mu 0 : ℝ) : ℂ) +
          (2 : ℂ) *
            ((∫ x : ℝ in Ioi 0,
                (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) +
              ((∫ x : ℝ in (0 : ℝ)..L,
                  ((Real.exp (-x / 2) : ℂ) - k x) *
                    (archDensity x : ℂ)) +
                ∫ x : ℝ in Ioi L,
                  ((Real.exp (-x / 2) : ℂ) - k x) *
                    (archDensity x : ℂ))) := by rw [heminusSplit]
    _ = -((2 * wCorrection L : ℝ) : ℂ) +
          (2 : ℂ) * (∫ x : ℝ in (0 : ℝ)..L,
            ((Real.exp (-x / 2) : ℂ) - k x) *
              (archDensity x : ℂ)) := by
      rw [htailValue]
      linear_combination hconstant
    _ = (-2 : ℂ) * (∫ x : ℝ in (0 : ℝ)..L,
          (k x - (Real.exp (-x / 2) : ℂ)) *
            (archDensity x : ℂ)) -
          ((2 * wCorrection L : ℝ) : ℂ) * k 0 := by
      rw [hfiniteNeg, hk0]
      ring
    _ = dictionaryArchPhysicalRHS k L := by
      change
        (-2 : ℂ) * (∫ x : ℝ in (0 : ℝ)..L,
          (k x - (Real.exp (-x / 2) : ℂ)) *
            (archDensity x : ℂ)) -
          ((2 * wCorrection L : ℝ) : ℂ) * k 0 =
        (-2 : ℂ) * (∫ x : ℝ in (0 : ℝ)..L,
          (k x - k 0 * (Real.exp (-x / 2) : ℂ)) *
            (archDensity x : ℂ)) -
          ((2 * wCorrection L : ℝ) : ℂ) * k 0
      rw [hk0]
      simp only [one_mul, mul_one]

end Zeta23.CCM
