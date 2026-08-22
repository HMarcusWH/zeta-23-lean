import Zeta23.CCM.DictionaryTentDecay
import Zeta23.WeilEF.ZeroSummability

noncomputable section

namespace Zeta23.CCM

open Complex Set Filter

/-!
# Zero-side summability of the canonical dictionary tent

The only new analytic input is the critical-strip quadratic decay proved in
`DictionaryTentDecay`.  Zero counting and the weighted comparison series are
reused verbatim from `Zeta23.WeilEF.ZeroSummability`.

This is an absolute-convergence theorem only.  It does not extend `EF_lit` to
the nonsmooth tent and does not identify the zero sum with `literatureRHS`.
-/

/-- Generic zero-configuration version: local zero counting plus the strip
condition and tent quadratic decay imply absolute convergence of the tent zero
sum. -/
theorem dictionaryTent_zero_sum_summable_gen
    (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * Zeta23.paperFT (dictionaryTent L) (gammaOf ρ)) := by
  classical
  set A : ℝ := 2 * (1 + Real.exp (L / 2)) / L with hA
  set C : ℝ := 2 * A with hC
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    positivity
  have hC_nonneg : 0 ≤ C := by
    rw [hC]
    positivity
  have hg := (Zeta23.WeilEF.zero_sum_inv_sq_gen Z hA₀ hloc').mul_left C
  refine Summable.of_norm_bounded_eventually hg ?_

  -- The only possible failure of the `1/‖γ‖²` comparison is confined to a
  -- finite ordinate window, exactly as in the inherited C_c² proof.
  have hfin : (Z.window (-1) 1).Finite := Z.finite_window _ _
  have hSfin : ((fun ρ : Z.carrier => (ρ : ℂ)) ⁻¹' (Z.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
  simp only [Set.mem_compl_iff, Set.mem_preimage, ZeroConfig.window, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_le] at hρ
  have hρmem : (ρ : ℂ) ∈ Z.carrier := ρ.2

  have him : 1 ≤ |(ρ : ℂ).im| := by
    by_contra h
    rw [not_le, abs_lt] at h
    exact absurd (hρ hρmem h.1) (not_lt.mpr h.2.le)
  have hz1 : 1 ≤ ‖gammaOf (ρ : ℂ)‖ :=
    him.trans (Zeta23.WeilEF.abs_im_le_norm_gammaOf _)
  have hz0 : gammaOf (ρ : ℂ) ≠ 0 := fun h => by
    rw [h, norm_zero] at hz1
    linarith
  have hstrip := Z.strip _ hρmem
  have himγ : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
    Zeta23.WeilEF.abs_gammaOf_im_le hstrip
  have hdecay := norm_paperFT_dictionaryTent_mul_sq_le hL (gammaOf (ρ : ℂ)) himγ
  have hnsq : Complex.normSq (gammaOf (ρ : ℂ)) = ‖gammaOf (ρ : ℂ)‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  have hzsqpos : 0 < ‖gammaOf (ρ : ℂ)‖ ^ 2 := by
    positivity
  have hraw :
      ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖
        ≤ A / ‖gammaOf (ρ : ℂ)‖ ^ 2 := by
    rw [le_div_iff₀ hzsqpos]
    simpa [hA] using hdecay
  have h2 :
      1 / ‖gammaOf (ρ : ℂ)‖ ^ 2
        ≤ 2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    rw [hnsq, div_le_iff₀ (by positivity)]
    have hpos : 0 < 1 + ‖gammaOf (ρ : ℂ)‖ ^ 2 := by positivity
    rw [show 2 * (1 / (1 + ‖gammaOf (ρ : ℂ)‖ ^ 2)) *
          ‖gammaOf (ρ : ℂ)‖ ^ 2 =
          2 * ‖gammaOf (ρ : ℂ)‖ ^ 2 /
            (1 + ‖gammaOf (ρ : ℂ)‖ ^ 2) by ring,
      le_div_iff₀ hpos]
    nlinarith
  have hFT :
      ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖
        ≤ C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    calc
      ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖
          ≤ A / ‖gammaOf (ρ : ℂ)‖ ^ 2 := hraw
      _ = A * (1 / ‖gammaOf (ρ : ℂ)‖ ^ 2) := by ring
      _ ≤ A * (2 * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
        mul_le_mul_of_nonneg_left h2 hA_nonneg
      _ = C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        rw [hC]
        ring

  rw [norm_mul, Complex.norm_natCast]
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  calc
    (Z.mult ρ : ℝ) * ‖Zeta23.paperFT (dictionaryTent L) (gammaOf (ρ : ℂ))‖
        ≤ (Z.mult ρ : ℝ) *
            (C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul_of_nonneg_left hFT hm
    _ = C * ((Z.mult (ρ : ℂ) : ℝ) /
          (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
          ring

/-- Concrete zeta instance, derived from the inherited local zero count. -/
theorem dictionaryTent_zero_sum_summable
    (hs : ZetaSeam) {L : ℝ} (hL : 0 < L) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT (dictionaryTent L) (gammaOf ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  exact dictionaryTent_zero_sum_summable_gen
    (zetaZeros hs) hA₀ (fun t => by rw [zetaZeros_N]; exact hloc t) hL

/-- The theorem-authoritative #39 analytic package.  This bundles the exact
removable-node value, the exact nonzero transform, critical-strip quadratic
decay and zeta zero-side absolute summability.  It deliberately does not state
an explicit-formula identity. -/
theorem dictionaryTent_analytic_package
    (hs : ZetaSeam) {L : ℝ} (hL : 0 < L) :
    Zeta23.paperFT (dictionaryTent L) 0 = (L : ℂ) ∧
    (∀ z : ℂ, z ≠ 0 →
      Zeta23.paperFT (dictionaryTent L) z =
        2 * (1 - Complex.cos ((L : ℂ) * z)) / ((L : ℂ) * z ^ 2)) ∧
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖Zeta23.paperFT (dictionaryTent L) z‖ * ‖z‖ ^ 2
        ≤ 2 * (1 + Real.exp (L / 2)) / L) ∧
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT (dictionaryTent L) (gammaOf ρ)) := by
  refine ⟨paperFT_dictionaryTent_zero hL, ?_, ?_, dictionaryTent_zero_sum_summable hs hL⟩
  · intro z hz
    exact paperFT_dictionaryTent_of_ne_zero hL hz
  · intro z hz
    exact norm_paperFT_dictionaryTent_mul_sq_le hL z hz

end Zeta23.CCM
