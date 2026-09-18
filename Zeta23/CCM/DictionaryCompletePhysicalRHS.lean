import Zeta23.CCM.DictionaryMixedPairing
import Zeta23.CCM.DictionaryArchSourceBridge
import Zeta23.CCM.DictionaryArchSourceIntegrability
import Zeta23.CCM.DictionaryArchFourier
import Zeta23.CCM.CanonicalSourceMomentAtoms

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction FourierTransform Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: complete physical RHS

This module exposes the theorem-authoritative literature RHS of a zero-centered
mixed finite-dictionary test as one exact physical-space expression.  No new
explicit-formula normalization is introduced.

The pole and archimedean integrals are deliberately kept as two terms.  Their
integrands combine algebraically to the kernel
`exp (-x/2) + exp (x/2) - archDensity x = 2*cosh(x/2) - archDensity x`,
but the separated form avoids adding an unnecessary interval-integrability
obligation to the representation theorem.
-/

/-- The positive-half-line pole weight after even folding. -/
def completeSourcePoleWeight (x : ℝ) : ℝ :=
  Real.exp (-x / 2) + Real.exp (x / 2)

/-- Exact physical-space expression for one zero-centered mixed dictionary test. -/
def dictionaryCompletePhysicalRHS
    (k : ℝ → ℂ) (L : ℝ) : ℂ :=
  (∫ x in (0 : ℝ)..L,
      k x * (completeSourcePoleWeight x : ℂ))
    -
  (∫ x in (0 : ℝ)..L,
      k x * (archDensity x : ℂ))
    -
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      primeSourceWeight q * k (Real.log q)

/-- Every dictionary basis transform is integrable on the real paper frequency. -/
theorem integrable_paperFT_dictionaryBasisTest
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable (fun r : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (r : ℂ)) := by
  by_cases hnm : n = m
  · subst m
    exact Zeta23.EF.integrable_paperFT_ofReal
      (integrable_fourier_dictionaryBasisTest_diag hL n)
  · let c : ℂ := ((n - m : ℤ) : ℂ)
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast hnmZ
    have hN := Zeta23.EF.integrable_paperFT_ofReal
      (integrable_fourier_dictionarySourceTest hL n)
    have hM := Zeta23.EF.integrable_paperFT_ofReal
      (integrable_fourier_dictionarySourceTest hL m)
    have hsub : Integrable (fun r : ℝ =>
        Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ) -
          Zeta23.paperFT (dictionarySourceTest m L) (r : ℂ)) :=
      hN.sub hM
    have hscaled := hsub.const_mul c⁻¹
    refine hscaled.congr ?_
    filter_upwards with r
    have hdisp :=
      paperFT_dictionaryBasisTest_displacement_eq_sourceTest_sub
        hL hnm r
    change
      Zeta23.paperFT (dictionaryBasisTest n m L) (r : ℂ) =
        c⁻¹ *
          (Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ) -
            Zeta23.paperFT (dictionarySourceTest m L) (r : ℂ))
    calc
      Zeta23.paperFT (dictionaryBasisTest n m L) (r : ℂ) =
          c⁻¹ * (c *
            Zeta23.paperFT (dictionaryBasisTest n m L) (r : ℂ)) := by
              field_simp [hc]
      _ = c⁻¹ *
          (Zeta23.paperFT (dictionarySourceTest n L) (r : ℂ) -
            Zeta23.paperFT (dictionarySourceTest m L) (r : ℂ)) := by
              rw [hdisp]

/-- Every dictionary basis test has an integrable Mathlib Fourier transform. -/
theorem integrable_fourier_dictionaryBasisTest
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable (𝓕 (dictionaryBasisTest n m L)) :=
  integrable_fourier_of_integrable_paperFT
    (integrable_paperFT_dictionaryBasisTest hL n m)

/-- Every basis test has an integrable `paperFT * (mu-mu(0))` density. -/
theorem integrable_paperFT_dictionaryBasisTest_mul_mu_sub_mu_zero
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable (fun tau : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) *
        ((Zeta23.mu tau - Zeta23.mu 0 : ℝ) : ℂ)) := by
  have hfull := integrable_paperFT_dictionaryBasisTest_mul_mu hL n m
  have hpaper := integrable_paperFT_dictionaryBasisTest hL n m
  have hconst : Integrable (fun tau : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (tau : ℂ) *
        (Zeta23.mu 0 : ℂ)) :=
    hpaper.mul_const _
  have hsub := hfull.sub hconst
  refine hsub.congr ?_
  filter_upwards with tau
  push_cast
  ring

/-- The mixed dictionary transform is integrable on the real paper frequency. -/
theorem integrable_paperFT_dictionaryMixedTest
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun r : ℝ =>
      Zeta23.paperFT (dictionaryMixedTest N x y L) (r : ℂ)) := by
  have hfun :
      (fun r : ℝ =>
        Zeta23.paperFT (dictionaryMixedTest N x y L) (r : ℂ)) =
      fun r : ℝ => ∑ i, ∑ j,
        star (x i) *
          Zeta23.paperFT
            (dictionaryBasisTest
              (centeredIndex N i) (centeredIndex N j) L) (r : ℂ) *
          y j := by
    funext r
    exact paperFT_dictionaryMixedTest_eq_basis_sum N x y hL (r : ℂ)
  rw [hfun]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact
    ((integrable_paperFT_dictionaryBasisTest hL
      (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _

/-- The mixed dictionary test has an integrable Mathlib Fourier transform. -/
theorem integrable_fourier_dictionaryMixedTest
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable (𝓕 (dictionaryMixedTest N x y L)) :=
  integrable_fourier_of_integrable_paperFT
    (integrable_paperFT_dictionaryMixedTest N x y hL)

/-- The mixed dictionary has an integrable `paperFT * (mu-mu(0))` density. -/
theorem integrable_paperFT_dictionaryMixedTest_mul_mu_sub_mu_zero
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun tau : ℝ =>
      Zeta23.paperFT (dictionaryMixedTest N x y L) (tau : ℂ) *
        ((Zeta23.mu tau - Zeta23.mu 0 : ℝ) : ℂ)) := by
  have hpaper (tau : ℝ) :
      Zeta23.paperFT (dictionaryMixedTest N x y L) (tau : ℂ) =
        ∑ i, ∑ j,
          star (x i) *
            Zeta23.paperFT
              (dictionaryBasisTest
                (centeredIndex N i) (centeredIndex N j) L)
              (tau : ℂ) * y j :=
    paperFT_dictionaryMixedTest_eq_basis_sum N x y hL (tau : ℂ)
  rw [show
    (fun tau : ℝ =>
      Zeta23.paperFT (dictionaryMixedTest N x y L) (tau : ℂ) *
        ((Zeta23.mu tau - Zeta23.mu 0 : ℝ) : ℂ)) =
      fun tau : ℝ => ∑ i, ∑ j,
        star (x i) *
          (Zeta23.paperFT
            (dictionaryBasisTest
              (centeredIndex N i) (centeredIndex N j) L)
            (tau : ℂ) *
              ((Zeta23.mu tau - Zeta23.mu 0 : ℝ) : ℂ)) *
          y j by
      funext tau
      rw [hpaper tau]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact
    ((integrable_paperFT_dictionaryBasisTest_mul_mu_sub_mu_zero hL
      (centeredIndex N i) (centeredIndex N j)).const_mul _).mul_const _

/-- Restrict the mixed archimedean density integral to its finite aperture. -/
theorem integral_dictionaryMixedTest_mul_archDensity_Ioi_eq_interval
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    (∫ z : ℝ in Ioi 0,
        dictionaryMixedTest N x y L z * (archDensity z : ℂ)) =
      ∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z * (archDensity z : ℂ) := by
  let f : ℝ → ℂ := fun z =>
    dictionaryMixedTest N x y L z * (archDensity z : ℂ)
  have hsupport :
      (∫ z : ℝ in Ici 0, f z) = ∫ z : ℝ in Icc 0 L, f z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ici Icc_subset_Ici_self
    intro z hz
    have hz0 : 0 ≤ z := hz.1
    have hzL : L < z := by
      have hnle : ¬z ≤ L := by
        intro hzle
        exact hz.2 ⟨hz0, hzle⟩
      exact lt_of_not_ge hnle
    have habs : L < |z| := by simpa [abs_of_nonneg hz0] using hzL
    unfold f
    rw [dictionaryMixedTest_eq_zero_of_lt_abs N x y L z habs, zero_mul]
  change (∫ z : ℝ in Ioi 0, f z) = ∫ z : ℝ in (0 : ℝ)..L, f z
  calc
    (∫ z : ℝ in Ioi 0, f z) = ∫ z : ℝ in Ici 0, f z :=
      integral_Ici_eq_integral_Ioi.symm
    _ = ∫ z : ℝ in Icc 0 L, f z := hsupport
    _ = ∫ z : ℝ in Ioc 0 L, f z := integral_Icc_eq_integral_Ioc
    _ = ∫ z : ℝ in (0 : ℝ)..L, f z :=
      (intervalIntegral.integral_of_le hL.le).symm

/-- Zero-centered mixed tests have the exact finite-aperture archimedean density form. -/
theorem dictionaryArchRHS_dictionaryMixedTest_eq_neg_two_density_integral_of_zero
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hzero : dictionaryMixedTest N x y L 0 = 0) :
    dictionaryArchRHS (dictionaryMixedTest N x y L) =
      (-2 : ℂ) * ∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z * (archDensity z : ℂ) := by
  have hk := continuous_dictionaryMixedTest N x y hL
  have hki : Integrable (dictionaryMixedTest N x y L) :=
    hk.integrable_of_hasCompactSupport
      (dictionaryMixedTest_hasCompactSupport N x y L)
  have hFk := integrable_fourier_dictionaryMixedTest N x y hL
  have heven : ∀ z : ℝ,
      dictionaryMixedTest N x y L (-z) =
        dictionaryMixedTest N x y L z :=
    fun z => dictionaryMixedTest_neg N x y L z
  have hmu :=
    integrable_paperFT_dictionaryMixedTest_mul_mu_sub_mu_zero N x y hL
  calc
    dictionaryArchRHS (dictionaryMixedTest N x y L) =
        (-2 : ℂ) * ∫ z : ℝ in Ioi 0,
          dictionaryMixedTest N x y L z * (archDensity z : ℂ) :=
      dictionaryArchRHS_eq_neg_two_mul_archDensity_integral_of_zero
        hk hki hFk heven hmu hzero
    _ = (-2 : ℂ) * ∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z * (archDensity z : ℂ) := by
      rw [integral_dictionaryMixedTest_mul_archDensity_Ioi_eq_interval
        N x y hL]

/-- Half of the prime channel is the single positive-log finite sample sum. -/
theorem half_dictionaryPrimeRHS_dictionaryMixedTest_eq_samples
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (_hL : 0 < L) :
    (1 / 2 : ℂ) *
        dictionaryPrimeRHS (dictionaryMixedTest N x y L) =
      -(∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          primeSourceWeight q *
            dictionaryMixedTest N x y L (Real.log q)) := by
  rw [dictionaryPrimeRHS_eq_finset
    (dictionaryMixedTest_tsupport_subset N x y L)]
  simp_rw [dictionaryMixedTest_neg]
  have hsum :
      (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        ((Λ q / Real.sqrt q : ℝ) : ℂ) *
          (dictionaryMixedTest N x y L (Real.log q) +
            dictionaryMixedTest N x y L (Real.log q))) =
      2 * (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          dictionaryMixedTest N x y L (Real.log q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    unfold primeSourceWeight
    ring
  rw [hsum]
  ring

/-- Half of the pole channel is the folded positive-half aperture integral. -/
theorem half_dictionaryPoleRHS_dictionaryMixedTest_eq_interval
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    (1 / 2 : ℂ) *
        dictionaryPoleRHS (dictionaryMixedTest N x y L) =
      ∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z *
          (completeSourcePoleWeight z : ℂ) := by
  let k : ℝ → ℂ := dictionaryMixedTest N x y L
  let G : ℝ → ℂ := fun z =>
    k z * ((Real.exp (-|z| / 2) + Real.exp (|z| / 2) : ℝ) : ℂ)
  have hk : Continuous k := continuous_dictionaryMixedTest N x y hL
  have hkc : HasCompactSupport k :=
    dictionaryMixedTest_hasCompactSupport N x y L
  have hA : Integrable (fun z : ℝ =>
      k z * (Real.exp (-|z| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB : Integrable (fun z : ℝ =>
      k z * (Real.exp (|z| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hpole := dictionaryPoleRHS_eq_spatial_weights hk hkc
  have hsum :
      dictionaryPoleRHS k = ∫ z : ℝ, G z := by
    rw [hpole, ← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with z
    dsimp [G]
    push_cast
    ring
  have hGsupp : Function.support G ⊆ Icc (-L) L := by
    intro z hz
    apply dictionaryMixedTest_support_subset N x y L
    intro hkz
    apply hz
    simp [G, k, hkz]
  rw [show dictionaryPoleRHS (dictionaryMixedTest N x y L) =
      ∫ z : ℝ, G z by simpa [k] using hsum]
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc
    (by linarith : -L ≤ L) hGsupp]
  have hGcont : Continuous G := by
    dsimp [G, k]
    exact (continuous_dictionaryMixedTest N x y hL).mul (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hGcont.intervalIntegrable (-L) 0)
    (hGcont.intervalIntegrable 0 L)
  rw [← hsplit]
  have hleft :
      (∫ z in -L..(0 : ℝ), G z) =
        ∫ z in (0 : ℝ)..L, G (-z) := by
    have h := intervalIntegral.integral_comp_neg
      (a := (0 : ℝ)) (b := L) G
    simpa using h.symm
  rw [hleft]
  have hevenG : ∀ z : ℝ, G (-z) = G z := by
    intro z
    dsimp [G, k]
    rw [dictionaryMixedTest_neg]
    simp [abs_neg]
  have hleftEq :
      (∫ z in (0 : ℝ)..L, G (-z)) =
        ∫ z in (0 : ℝ)..L, G z := by
    apply intervalIntegral.integral_congr
    intro z hz
    exact hevenG z
  rw [hleftEq]
  have hpos :
      (∫ z in (0 : ℝ)..L, G z) =
        ∫ z in (0 : ℝ)..L,
          dictionaryMixedTest N x y L z *
            (completeSourcePoleWeight z : ℂ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hL.le] at hz
    have hz0 : 0 ≤ z := hz.1
    dsimp [G, k, completeSourcePoleWeight]
    rw [abs_of_nonneg hz0]
  rw [hpos]
  ring

/-- Exact complete physical-space RHS for a zero-centered mixed dictionary test. -/
theorem half_literatureRHS_dictionaryMixedTest_eq_completePhysicalRHS_of_zero
    (N : ℕ)
    (x y : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hzero : dictionaryMixedTest N x y L 0 = 0) :
    (1 / 2 : ℂ) *
        Zeta23.EF.literatureRHS (dictionaryMixedTest N x y L) =
      dictionaryCompletePhysicalRHS
        (dictionaryMixedTest N x y L) L := by
  rw [literatureRHS_eq_dictionaryChannels]
  have hpole :=
    half_dictionaryPoleRHS_dictionaryMixedTest_eq_interval N x y hL
  have hprime :=
    half_dictionaryPrimeRHS_dictionaryMixedTest_eq_samples N x y hL
  have harch :=
    dictionaryArchRHS_dictionaryMixedTest_eq_neg_two_density_integral_of_zero
      N x y hL hzero
  unfold dictionaryCompletePhysicalRHS
  calc
    (1 / 2 : ℂ) *
        (dictionaryPoleRHS (dictionaryMixedTest N x y L) +
          dictionaryPrimeRHS (dictionaryMixedTest N x y L) +
          dictionaryArchRHS (dictionaryMixedTest N x y L)) =
      (1 / 2 : ℂ) * dictionaryPoleRHS (dictionaryMixedTest N x y L) +
        (1 / 2 : ℂ) * dictionaryPrimeRHS (dictionaryMixedTest N x y L) +
        (1 / 2 : ℂ) * dictionaryArchRHS (dictionaryMixedTest N x y L) := by
          ring
    _ =
      (∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z *
          (completeSourcePoleWeight z : ℂ)) +
      (-(∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          dictionaryMixedTest N x y L (Real.log q))) +
      (-(∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z * (archDensity z : ℂ))) := by
          rw [hpole, hprime, harch]
          ring
    _ =
      (∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z *
          (completeSourcePoleWeight z : ℂ))
        -
      (∫ z : ℝ in (0 : ℝ)..L,
        dictionaryMixedTest N x y L z * (archDensity z : ℂ))
        -
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          dictionaryMixedTest N x y L (Real.log q) := by
          ring

end Zeta23.CCM

#print axioms Zeta23.CCM.half_literatureRHS_dictionaryMixedTest_eq_completePhysicalRHS_of_zero
