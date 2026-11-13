import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure

/-!
# Arbitrary fixed depth at every late aperture, and cofinal semiboundedness

The existing relative-margin theorem `recentered_negative_phase_eventually_relative_margin`
states only that some positive margin exists. This module reproves it with the
explicit margin `-W/4`, where `W` is the real Weil energy of the fixed smooth
phase, from the same public ingredients (recentering, the finite Weil error
budget and physical mass control). Combined with the exponential depth of the
fixed smooth phases themselves, it gives:

* (AD) under an off-line zero, for every `M` there is one threshold after which
  **both** moment slices contain a nonzero vector with energy below
  `-M ‖u‖²`, at every aperture;
* (SB) a single floor `C`, chosen before all horizons, holding on one parity's
  whole slice at cofinally many apertures (parity may change between
  apertures) implies Mathlib's `RiemannHypothesis`.

The order is `M`, then two fixed phases, then the threshold, then every larger
aperture; `M` does not depend on the aperture. The premise (SB) is an OPEN
arithmetic supplier, and nothing here supplies it.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero OPICARound3 Filter

/-- The recentered quartic phase energy with its constant exposed: eventually the
native energy is below `W / (2 n²)`, where `W < 0` is the fixed smooth energy and
`n` the fixed trial normalization. Same proof as
`recentered_negative_phase_eventually_quartic`, with the margin made explicit. -/
theorem recentered_phase_energy_lt_explicit {σ a : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hneg : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
      (fixedOriginalSincPhaseTrial σ a)).re < 0) :
    ∀ᶠ L : ℝ in atTop, ∃ hL : 2 ≤ L,
      (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith)))
        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith))).re <
        (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
          (fixedOriginalSincPhaseTrial σ a)).re / (2 * fixedOriginalSincTrialNormalization ^ 2) := by
  let W := (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
    (fixedOriginalSincPhaseTrial σ a)).re
  let n := fixedOriginalSincTrialNormalization
  have hW : W < 0 := hneg
  have hn : 0 < n := fixedOriginalSincTrialNormalization_pos
  have hlim := originalDetectorFinitePhaseWeilErrorBudget_mul_exp_tendsto_zero 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < -W/2 by linarith))
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (fixedOriginalSincTrialAperture a), hsmall] with L hL hLa he
  refine ⟨hL, ?_⟩
  have hleft : 1+UniversalSinc.fixedScale ≤ L/2-a := by
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter] at hLa
    linarith
  have hright : L/2-a+UniversalSinc.fixedScale ≤ L-1 := by
    have ha0 := UniversalSinc.fixedScale_pos.trans ha
    linarith
  have hb := recenteredFinitePhase_Weil_error hL hleft hright hσ
  rw [recenteredSmoothPhase_fixed_energy] at hb
  have hr := (Complex.re_le_norm
    (zetaZeroConfig.W (recenteredFiniteHard σ L (L/2-a) (by linarith))
      (recenteredFiniteHard σ L (L/2-a) (by linarith)) -
      zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
        (fixedOriginalSincPhaseTrial σ a))).trans hb
  rw [Complex.sub_re, recenteredFiniteHard_Weil_eq_native hL] at hr
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  rw [lt_div_iff₀ (by positivity)]
  dsimp only [W, n] at hr he hn2 ⊢
  nlinarith

/-- **Explicit relative margin.** Eventually the recentered phase vector is nonzero
and its native energy is below `(W / 4) ‖v‖²`; the margin `-W/4` depends only on
the fixed smooth phase, not on the aperture. -/
theorem recentered_phase_relative_margin_explicit {σ a : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hneg : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
      (fixedOriginalSincPhaseTrial σ a)).re < 0) :
    ∀ᶠ L : ℝ in atTop, ∃ hL : 2 ≤ L,
      originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith) ≠ 0 ∧
      (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith)))
        (originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith))).re <
        ((zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
          (fixedOriginalSincPhaseTrial σ a)).re / 4) *
          ‖originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith)‖ ^ 2 := by
  have henergy := recentered_phase_energy_lt_explicit hσ ha hneg
  obtain ⟨T, hT, hmass⟩ := exists_recentered_mass_control_threshold
  filter_upwards [henergy, eventually_ge_atTop T,
    eventually_ge_atTop (fixedOriginalSincTrialAperture a)] with L henergy hLT hLa
  obtain ⟨hL, henergy⟩ := henergy
  have hleft : 1+UniversalSinc.fixedScale ≤ L/2-a := by
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter] at hLa
    linarith
  have hright : L/2-a+UniversalSinc.fixedScale ≤ L-1 := by
    have ha0 := UniversalSinc.fixedScale_pos.trans ha
    linarith
  have hasep : UniversalSinc.fixedScale < L/2-(L/2-a) := by convert ha using 1; ring
  have hm := (hmass L (L/2-a) σ hL hLT hσ hasep hleft hright).2
  set W := (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
    (fixedOriginalSincPhaseTrial σ a)).re with hWdef
  set n := fixedOriginalSincTrialNormalization with hndef
  have hn : 0 < n := fixedOriginalSincTrialNormalization_pos
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hW : W < 0 := hneg
  have hv : originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith) ≠ 0 := by
    intro hz
    rw [hz, map_zero, inner_zero_right] at henergy
    norm_num at henergy
    have : W / (2 * n ^ 2) < 0 := div_neg_of_neg_of_pos hW (by positivity)
    linarith
  refine ⟨hL, hv, ?_⟩
  set v := originalDetectorFinitePhaseVector σ L (L/2-a) (by linarith)
  have hm2 : n ^ 2 * ‖v‖ ^ 2 < 2 := by linarith
  have hgoal : W / (2 * n ^ 2) ≤ (W / 4) * ‖v‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖v‖]
  exact henergy.trans_le hgoal

/-- A fixed smooth phase of either sign with Weil energy below any prescribed
level `-4M`, at a separation beyond the fixed scale. This uses the actual
exponential depth of the fixed phases; the separation depends on `M`. -/
theorem exists_fixed_phase_below (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (M : ℝ) :
    ∃ a : ℝ, UniversalSinc.fixedScale < a ∧
      (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
        (fixedOriginalSincPhaseTrial σ a)).re < -4 * M := by
  set β := |(ρ : ℂ).re - 1 / 2| / 2 with hβdef
  have hδ : 0 < |(ρ : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβρ : β < |(ρ : ℂ).re - 1 / 2| := by rw [hβdef]; linarith
  set R := max (2 * UniversalSinc.fixedScale + 2 * fixedOriginalSincLobeCenter)
    (Real.log (max (4 * M) 1) / β) with hRdef
  obtain ⟨a, hlate, _, _, hdepth⟩ :=
    exists_fixedOriginalSincPhaseTrial_depth_of_off_line_zero ρ hβ hβρ hσ R
  have hRA : R < fixedOriginalSincTrialAperture a := (le_max_left R 4).trans_lt hlate
  have ha : UniversalSinc.fixedScale < a := by
    have hh := (le_max_left (2 * UniversalSinc.fixedScale + 2 * fixedOriginalSincLobeCenter)
      (Real.log (max (4 * M) 1) / β)).trans_lt hRA
    dsimp [fixedOriginalSincTrialAperture] at hh
    linarith
  refine ⟨a, ha, ?_⟩
  rw [← fixedOriginalSincPhaseTrial_Weil_eq_native] at hdepth
  have hlogA : Real.log (max (4 * M) 1) / β < fixedOriginalSincTrialAperture a :=
    (le_max_right _ _).trans_lt hRA
  have hlog : Real.log (max (4 * M) 1) < β * fixedOriginalSincTrialAperture a := by
    rw [div_lt_iff₀ hβ] at hlogA
    linarith
  have hexp : max (4 * M) 1 < Real.exp (β * fixedOriginalSincTrialAperture a) := by
    calc max (4 * M) 1 = Real.exp (Real.log (max (4 * M) 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ < Real.exp (β * fixedOriginalSincTrialAperture a) := Real.exp_lt_exp.mpr hlog
  have h4M : 4 * M ≤ max (4 * M) 1 := le_max_left _ _
  linarith

/-- **(AD) All-late arbitrary fixed depth.** Under an off-line zero, for every `M`
there is one threshold after which both exact moment slices contain a nonzero
vector with native energy below `-M ‖u‖²`, at every aperture. -/
theorem eventually_both_moment_slices_below (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1 / 2) (M : ℝ) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      (∃ u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),
        u ≠ 0 ∧ u ∈ evenMomentSlice L (originalDetectorQuarticCutoff L) ∧
        evenNativeEnergy L (originalDetectorQuarticCutoff L) u < -M * ‖u‖ ^ 2) ∧
      (∃ v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L),
        v ≠ 0 ∧ v ∈ oddMomentSlice L (originalDetectorQuarticCutoff L) ∧
        oddNativeEnergy L (originalDetectorQuarticCutoff L) v < -M * ‖v‖ ^ 2) := by
  -- Work with `max M 1 > 0` so that both fixed energies are negative.
  obtain ⟨ae', hae', he'⟩ := exists_fixed_phase_below ρ hoff (Or.inl rfl) (max M 1)
  obtain ⟨ao', hao', ho'⟩ := exists_fixed_phase_below ρ hoff (Or.inr rfl) (max M 1)
  have hM1 : 1 ≤ max M 1 := le_max_right _ _
  have hMM : M ≤ max M 1 := le_max_left _ _
  have hen : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial 1 ae')
      (fixedOriginalSincPhaseTrial 1 ae')).re < 0 := by linarith
  have hon : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial (-1) ao')
      (fixedOriginalSincPhaseTrial (-1) ao')).re < 0 := by linarith
  have hE := recentered_phase_relative_margin_explicit (Or.inl rfl) hae' hen
  have hO := recentered_phase_relative_margin_explicit (Or.inr rfl) hao' hon
  filter_upwards [hE, hO] with L hE hO
  obtain ⟨hL, hve, hEe⟩ := hE
  obtain ⟨_, hvo, hOe⟩ := hO
  refine ⟨hL, ?_, ?_⟩
  · refine ⟨originalDetectorFiniteEvenPhase (L/2-ae') hL, ?_,
      (mem_evenMomentSlice_iff _ _ _).mpr (originalDetectorFiniteEvenPhase_moment_four _ hL), ?_⟩
    · intro hz
      apply hve
      exact congrArg (fun w : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L) =>
        w.val.val) hz
    · unfold evenNativeEnergy
      rw [inner_poleNeutralEvenCompressedCanonical_self]
      change _ < -M * ‖originalDetectorFinitePhaseVector 1 L (L/2-ae') (by linarith)‖ ^ 2
      refine hEe.trans_le ?_
      have hn := sq_nonneg ‖originalDetectorFinitePhaseVector 1 L (L/2-ae') (by linarith)‖
      have hcoef : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial 1 ae')
          (fixedOriginalSincPhaseTrial 1 ae')).re / 4 ≤ -M := by linarith
      exact mul_le_mul_of_nonneg_right hcoef hn
  · refine ⟨originalDetectorFiniteOddPhase (L/2-ao') hL, ?_,
      (mem_oddMomentSlice_iff _ _ _).mpr
        ⟨originalDetectorFiniteOddPhase_moment_three _ hL,
          originalDetectorFiniteOddPhase_moment_five _ hL⟩, ?_⟩
    · intro hz
      apply hvo
      exact congrArg (fun w : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L) =>
        w.val.val) hz
    · unfold oddNativeEnergy
      rw [inner_poleNeutralOddCompressedCanonical_self]
      change _ < -M * ‖originalDetectorFinitePhaseVector (-1) L (L/2-ao') (by linarith)‖ ^ 2
      refine hOe.trans_le ?_
      have hn := sq_nonneg ‖originalDetectorFinitePhaseVector (-1) L (L/2-ao') (by linarith)‖
      have hcoef : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial (-1) ao')
          (fixedOriginalSincPhaseTrial (-1) ao')).re / 4 ≤ -M := by linarith
      exact mul_le_mul_of_nonneg_right hcoef hn

/-- **Contract (SB).** One floor `C ≥ 0`, chosen before every horizon, holding on
one parity's entire slice at cofinally many apertures; the parity may change
between apertures but never between vectors. This proposition is OPEN. -/
def CofinalMomentSliceSemibounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, ∃ L : ℝ, max R 2 < L ∧
    MomentSliceLowerBound L (originalDetectorQuarticCutoff L) C

/-- (SB) excludes every off-line zero of the actual zero configuration. -/
theorem no_off_line_zero_of_cofinal_semibounded (h : CofinalMomentSliceSemibounded) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  by_contra hoff
  obtain ⟨C, hC, hcof⟩ := h
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_both_moment_slices_below ρ hoff (C + 1))
  obtain ⟨L, hLR, hb⟩ := hcof T
  have hTL : T ≤ L := le_trans (le_max_left _ _) hLR.le
  obtain ⟨_, ⟨u, hu0, hus, hue⟩, ⟨v, hv0, hvs, hve⟩⟩ := hT L hTL
  rcases hb with he | ho
  · have hl := he u hus
    have hn : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
    nlinarith
  · have hl := ho v hvs
    have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
    nlinarith

/-- **Conditional reduction (SB) → RH.** The arithmetic premise remains OPEN. -/
theorem riemannHypothesis_of_cofinal_moment_slice_semibounded
    (h : CofinalMomentSliceSemibounded) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hm : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  exact no_off_line_zero_of_cofinal_semibounded h ⟨s, hm⟩

/-- (C1) is a special case of (SB) with floor `1`: the vanishing-error contract
is the stronger premise, and (SB) does not require the floor to shrink. -/
theorem cofinal_semibounded_of_cofinal_moment_slice_bounds
    (h : CofinalMomentSliceVanishingErrorBounds) : CofinalMomentSliceSemibounded := by
  refine ⟨1, zero_le_one, fun R => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 2)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  obtain ⟨L, hLN, hb⟩ := h N hN1
  refine ⟨L, by linarith, hb.mono ?_⟩
  rw [div_le_one hNpos]
  exact_mod_cast hN1

/-- Contrapositive: one actual off-line zero refutes (SB) for every floor. -/
theorem not_cofinal_moment_slice_semibounded_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ¬ CofinalMomentSliceSemibounded :=
  fun h => hoff (no_off_line_zero_of_cofinal_semibounded h ρ)

end Zeta23.OPICARound4.ArithmeticFrontier
