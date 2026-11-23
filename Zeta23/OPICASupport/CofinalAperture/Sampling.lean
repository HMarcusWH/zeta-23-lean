import Zeta23.OPICASupport.SamplingDensity.DistinctGrowthFromFraction
import Zeta23.OPICASupport.FourierEnergy.BoundaryFlatStrictEnergy
import Zeta23.ExceptionalZero.ZetaRealStripNonvanishing
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Cofinal aperture sampling without positive distinct-density

The exceptional apertures for a countable family of nonzero complex
frequencies form a countable set. For actual zeta zeros, countability is
provided by finite windows, nonzero gamma by real-strip nonvanishing, and
infinitude by the accepted Riemann--von Mangoldt theorem. No positive
distinct-fraction theorem, C1, RH, or energy sign is used.

A single good positive aperture works for every finite cutoff. Thus the
literal variable cutoff `ceil(L^4)` involves no circular choice of samples.
This does not assert that every aperture is good.
-/

noncomputable section

open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound20
open Filter
open scoped Topology

namespace Zeta23.OPICARound21.CofinalAperture

def goodApertures {ι : Type*} (z : ι → ℂ) : Set ℝ :=
  (⋃ i, {L : ℝ | Complex.exp (Complex.I * z i * (L : ℂ)) = 1})ᶜ

theorem resonance_apertures_countable {z : ℂ} (hz : z ≠ 0) :
    {L : ℝ | Complex.exp (Complex.I * z * (L : ℂ)) = 1}.Countable := by
  have hinj : Function.Injective (fun L : ℝ => Complex.I * z * (L : ℂ)) := by
    intro L M h
    exact Complex.ofReal_injective
      (mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero hz) h)
  simpa only [Set.preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq] using
    (Complex.countable_preimage_exp.mpr (Set.countable_singleton (1 : ℂ))).preimage hinj

theorem countable_bad_apertures {ι : Type*} [Countable ι]
    (z : ι → ℂ) (hz : ∀ i, z i ≠ 0) : (goodApertures z)ᶜ.Countable := by
  simpa only [goodApertures, compl_compl] using
    (Set.countable_iUnion (fun i => resonance_apertures_countable (hz i)))

theorem good_apertures_dense {ι : Type*} [Countable ι]
    (z : ι → ℂ) (hz : ∀ i, z i ≠ 0) : Dense (goodApertures z) := by
  simpa only [compl_compl] using (countable_bad_apertures z hz).dense_compl ℝ

theorem exists_nonresonant_aperture_in_interval {ι : Type*} [Countable ι]
    (z : ι → ℂ) (hz : ∀ i, z i ≠ 0) {A B : ℝ} (hAB : A < B) :
    ∃ L : ℝ, A < L ∧ L < B ∧
      ∀ i, Complex.exp (Complex.I * z i * (L : ℂ)) ≠ 1 := by
  obtain ⟨L, hgood, hL⟩ := (good_apertures_dense z hz).exists_mem_open
    isOpen_Ioo (Set.nonempty_Ioo.mpr hAB)
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro i hi
  exact hgood (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- Local finiteness on arbitrary real windows gives countability of the
actual complex points, without any statement about distinct ordinates. -/
theorem zeroConfig_carrier_countable (Z : ZeroConfig) : Z.carrier.Countable := by
  apply (Set.countable_iUnion
    (fun n : ℕ => (Z.finite_window (-(n : ℝ)) (n : ℝ)).countable)).mono
  intro ρ hρ
  obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
  apply Set.mem_iUnion.mpr
  refine ⟨n, hρ, ?_, ?_⟩
  · linarith [neg_abs_le ρ.im]
  · exact (le_abs_self ρ.im).trans hn.le

/-- Unbounded weighted counts force infinitely many distinct points because
a finite carrier has no points in sufficiently high windows. No positive
distinct-density estimate is used. -/
theorem zeroConfig_carrier_infinite_of_riemannVonMangoldt
    (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) : Z.carrier.Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := (hfinite.image Complex.im).bddAbove
  have hN := (Assembly.tendsto_N_atTop Z hRvM).eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨T, hN, hT⟩ := (hN.and (eventually_gt_atTop M)).exists
  have hwindow : Z.window T (2 * T) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have hbound : ρ.im ≤ M := hM (Set.mem_image_of_mem Complex.im hρ.1)
    exact (not_lt_of_ge hbound) (hT.trans hρ.2.1)
  have hzero : Z.N T (2 * T) = 0 := by simp [ZeroConfig.N, hwindow]
  norm_num [hzero] at hN

theorem actual_zero_carrier_infinite : zetaZeroConfig.carrier.Infinite :=
  zeroConfig_carrier_infinite_of_riemannVonMangoldt zetaZeroConfig
    actual_zeta_riemannVonMangoldt

theorem actual_gamma_ne_zero (ρ : zetaZeroConfig.carrier) : gammaOf (ρ : ℂ) ≠ 0 := by
  intro h
  have hs : (ρ : ℂ) - 1 / 2 = 0 := by
    simpa only [gammaOf, div_mul_cancel₀ _ Complex.I_ne_zero, zero_mul] using
      congrArg (fun w : ℂ => w * Complex.I) h
  have hρ : (ρ : ℂ) = 1 / 2 := sub_eq_zero.mp hs
  apply zetaZeroCarrier_im_ne_zero ρ
  rw [hρ]
  norm_num

theorem actual_good_apertures_dense :
    Dense (goodApertures (fun ρ : zetaZeroConfig.carrier => gammaOf (ρ : ℂ))) := by
  let : Countable zetaZeroConfig.carrier := (zeroConfig_carrier_countable zetaZeroConfig).to_subtype
  exact good_apertures_dense _ actual_gamma_ne_zero

theorem exists_actual_nonresonant_aperture_in_interval
    {A B : ℝ} (hAB : A < B) :
    ∃ L : ℝ, A < L ∧ L < B ∧
      ∀ ρ : zetaZeroConfig.carrier,
        Complex.exp (Complex.I * gammaOf (ρ : ℂ) * (L : ℂ)) ≠ 1 := by
  let : Countable zetaZeroConfig.carrier := (zeroConfig_carrier_countable zetaZeroConfig).to_subtype
  exact exists_nonresonant_aperture_in_interval _ actual_gamma_ne_zero hAB

theorem actual_samples_at_good_aperture {L : ℝ}
    (hgood : ∀ ρ : zetaZeroConfig.carrier,
      Complex.exp (Complex.I * gammaOf (ρ : ℂ) * (L : ℂ)) ≠ 1) (n : ℕ) :
    ∃ ρ : Fin n → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j)) ∧
      ∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1 := by
  let e := Set.Infinite.natEmbedding zetaZeroConfig.carrier actual_zero_carrier_infinite
  let ρ : Fin n → zetaZeroConfig.carrier := fun j => e j
  refine ⟨ρ, ?_, fun j => hgood (ρ j)⟩
  intro i j hij
  apply Fin.val_injective
  apply e.injective
  apply Subtype.ext
  exact gammaOf_injective hij

/-- The aperture is selected once before the universal cutoff quantifier. -/
theorem exists_interval_aperture_all_cutoff_samples
    {A B : ℝ} (hAB : A < B) :
    ∃ L : ℝ, A < L ∧ L < B ∧ ∀ K : ℕ, NonresonantActualZeroSamples L K := by
  obtain ⟨L, hLA, hLB, hgood⟩ := exists_actual_nonresonant_aperture_in_interval hAB
  exact ⟨L, hLA, hLB, fun K => actual_samples_at_good_aperture hgood (2 * K - 2)⟩

theorem exists_interval_aperture_all_cutoff_fourier_sampling
    {A B : ℝ} (hA : 0 ≤ A) (hAB : A < B) :
    ∃ L : ℝ, A < L ∧ L < B ∧ ∀ K : ℕ,
      ∃ ρ : Fin (2 * K - 2) → zetaZeroConfig.carrier,
        Function.Injective (fun j => gammaOf (ρ j)) ∧
        (∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1) ∧
        Function.Injective
          (fun u : {u : Fin (2 * K + 1) → ℂ // BoundaryFlatCoefficients K u} =>
            fun j => paperFT (localizedFiniteVector L K u.val) (gammaOf (ρ j))) := by
  obtain ⟨L, hLA, hLB, hsamples⟩ := exists_interval_aperture_all_cutoff_samples hAB
  refine ⟨L, hLA, hLB, ?_⟩
  intro K
  rcases hsamples K with ⟨ρ, hρ, hexp⟩
  exact ⟨ρ, hρ, hexp, boundaryFlat_paperFT_sampling_injective (hA.trans_lt hLA) K
    (fun j => gammaOf (ρ j)) hρ hexp (by simp)⟩

/-- Sampling at the literal native quartic cutoff, cofinally in positive
aperture, without any fixed-L density claim or energy-sign assertion. -/
theorem cofinal_literal_quartic_samples (A : ℝ) :
    ∃ L : ℝ, A < L ∧ 0 < L ∧
      NonresonantActualZeroSamples L (Nat.ceil (L ^ 4)) := by
  obtain ⟨L, hLA, _, hsamples⟩ := exists_interval_aperture_all_cutoff_samples
    (show max A 0 < max A 0 + 1 by linarith)
  exact ⟨L, (le_max_left A 0).trans_lt hLA,
    (le_max_right A 0).trans_lt hLA, hsamples (Nat.ceil (L ^ 4))⟩

end Zeta23.OPICARound21.CofinalAperture
