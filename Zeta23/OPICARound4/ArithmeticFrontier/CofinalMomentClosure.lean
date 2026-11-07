import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

/-!
# Contract (C1) as a conditional consumer of Mathlib's `RiemannHypothesis`

The premise `CofinalMomentSliceVanishingErrorBounds` is an OPEN arithmetic
supplier. This module proves only the reduction: the bound, at the same
aperture, cutoff, parity, carrier and norm as the existing negative witnesses,
contradicts an off-line zero. The supplier is not assumed anywhere else and
no closure of Step 4 follows from this file.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero OPICARound3 Filter

/-- (C1) excludes every off-line zero of the actual zero configuration. -/
theorem no_off_line_zero_of_cofinal_moment_slice_bounds
    (h : CofinalMomentSliceVanishingErrorBounds) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  by_contra hoff
  obtain ⟨d, hd, hev⟩ := eventually_no_moment_slice_lower_bound_below_margin ρ hoff
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / d) T)
  have hNd : 1 / d < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNT : T < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hNd
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  obtain ⟨L, hLN, hbound⟩ := h N hN1
  have hsmall : 1 / (N : ℝ) < d := by
    rw [div_lt_iff₀ hd] at hNd
    rw [div_lt_iff₀ hNpos]
    linarith
  exact hT L (by linarith) (1 / (N : ℝ)) hsmall hbound

/-- **Conditional reduction (C1) → RH.** The arithmetic premise remains OPEN. -/
theorem riemannHypothesis_of_cofinal_moment_slice_bounds
    (h : CofinalMomentSliceVanishingErrorBounds) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hm : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  exact no_off_line_zero_of_cofinal_moment_slice_bounds h ⟨s, hm⟩

/-- Contrapositive form: one actual off-line zero refutes (C1). This records the
exact strength of the premise; it is not evidence for or against it. -/
theorem not_cofinal_moment_slice_bounds_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ¬ CofinalMomentSliceVanishingErrorBounds :=
  fun h => hoff (no_off_line_zero_of_cofinal_moment_slice_bounds h ρ)

/-- A supplier that also fixes the parity in advance is a special case. -/
theorem cofinal_moment_slice_bounds_of_even
    (h : ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ) + 2 ≤ L ∧
      EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (1 / (n : ℝ))) :
    CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  obtain ⟨L, hL, he⟩ := h n hn
  exact ⟨L, hL, Or.inl he⟩

theorem cofinal_moment_slice_bounds_of_odd
    (h : ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ) + 2 ≤ L ∧
      OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) (1 / (n : ℝ))) :
    CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  obtain ⟨L, hL, ho⟩ := h n hn
  exact ⟨L, hL, Or.inr ho⟩

/-- A real-tolerance sequence tending to zero along apertures escaping every
bounded set also supplies (C1); no rate is required. -/
theorem cofinal_moment_slice_bounds_of_tendsto
    (L ε : ℕ → ℝ) (hL : Tendsto L atTop atTop) (hε : Tendsto ε atTop (nhds 0))
    (hb : ∀ m, MomentSliceLowerBound (L m) (originalDetectorQuarticCutoff (L m)) (ε m)) :
    CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hev : ∀ᶠ m in atTop, (n : ℝ) + 2 ≤ L m ∧ ε m < 1 / (n : ℝ) :=
    (hL.eventually (eventually_ge_atTop ((n : ℝ) + 2))).and
      (hε.eventually (gt_mem_nhds (by positivity)))
  obtain ⟨m, hm1, hm2⟩ := hev.exists
  exact ⟨L m, hm1, (hb m).mono hm2.le⟩

end Zeta23.OPICARound4.ArithmeticFrontier
