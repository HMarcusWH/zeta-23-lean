import Zeta23.ExceptionalZero.Step123CompleteOutput
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure

/-!
A strict generated-witness handoff for the native C1 obstruction.

Each complete output stores its own negative smooth source trial. At a common
late aperture recenter those same trials in the corresponding physical
moment slices. This consumes the witnessed separation and original trial
depth. The padded output vector, ground eigenvector and recentered trial
are different objects.
-/

set_option autoImplicit false

noncomputable section

open Filter
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier

namespace Zeta23.RHReference

theorem generated_pair_eventually_refutes_slice_bounds
    {ρ : zetaZeroConfig.carrier} {βe βo Re Ro : ℝ}
    (even : GeneratedStep123CompleteOutput ρ βe .even Re)
    (odd : GeneratedStep123CompleteOutput ρ βo .odd Ro) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ L : ℝ in atTop, ∀ ε : ℝ, ε < d →
      ¬ MomentSliceLowerBound L (originalDetectorQuarticCutoff L) ε := by
  let ae := even.generated.sourceData.separation
  let ao := odd.generated.sourceData.separation
  have he := even.generated.sourceData.original_depth
  have ho := odd.generated.sourceData.original_depth
  change (zetaZeroConfig.W (fixedOriginalSincPhaseTrial 1 ae)
     (fixedOriginalSincPhaseTrial 1 ae)).re ≤
       -4 * Real.exp (βe * fixedOriginalSincTrialAperture ae) at he
  change (zetaZeroConfig.W (fixedOriginalSincPhaseTrial (-1) ao)
     (fixedOriginalSincPhaseTrial (-1) ao)).re ≤
       -4 * Real.exp (βo * fixedOriginalSincTrialAperture ao) at ho
  obtain ⟨de, hde, hE⟩ := recentered_negative_phase_eventually_relative_margin
    (Or.inl rfl) even.generated.sourceData.separation_gt_scale
    (he.trans_lt (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)))
  obtain ⟨dO, hdo, hO⟩ := recentered_negative_phase_eventually_relative_margin
    (Or.inr rfl) odd.generated.sourceData.separation_gt_scale
    (ho.trans_lt (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)))
  refine ⟨min de dO, lt_min hde hdo, ?_⟩
  filter_upwards [hE, hO] with L hE hO
  obtain ⟨hL, huNZ, huE⟩ := hE
  obtain ⟨_, hvNZ, hvE⟩ := hO
  intro ε hε hb
  rcases hb with hBe | hBo
  · let u := originalDetectorFiniteEvenPhase (L / 2 - ae) hL
    have hn : u ≠ 0 := by
      intro hz
      apply huNZ
      exact congrArg (fun w : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L) =>
        w.val.val) hz
    have hm := (mem_evenMomentSlice_iff L (originalDetectorQuarticCutoff L) u).2
      (originalDetectorFiniteEvenPhase_moment_four _ hL)
    have hl := hBe u hm
    have hu : evenNativeEnergy L (originalDetectorQuarticCutoff L) u < -de * ‖u‖ ^ 2 := by
      unfold evenNativeEnergy
      rw [inner_poleNeutralEvenCompressedCanonical_self]
      exact huE
    have hstrict : ε < de := hε.trans_le (min_le_left _ _)
    have hsq : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hn) 2
    nlinarith [mul_pos (sub_pos.mpr hstrict) hsq]
  · let v := originalDetectorFiniteOddPhase (L / 2 - ao) hL
    have hn : v ≠ 0 := by
      intro hz
      apply hvNZ
      exact congrArg (fun w : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L) =>
        w.val.val) hz
    have hm := (mem_oddMomentSlice_iff L (originalDetectorQuarticCutoff L) v).2
      ⟨originalDetectorFiniteOddPhase_moment_three _ hL,
       originalDetectorFiniteOddPhase_moment_five _ hL⟩
    have hl := hBo v hm
    have hv : oddNativeEnergy L (originalDetectorQuarticCutoff L) v < -dO * ‖v‖ ^ 2 := by
      unfold oddNativeEnergy
      rw [inner_poleNeutralOddCompressedCanonical_self]
      exact hvE
    have hstrict : ε < dO := hε.trans_le (min_le_right _ _)
    have hsq : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hn) 2
    nlinarith [mul_pos (sub_pos.mpr hstrict) hsq]

theorem generated_pair_excludes_c1
    {ρ : zetaZeroConfig.carrier} {βe βo Re Ro : ℝ}
    (even : GeneratedStep123CompleteOutput ρ βe .even Re)
    (odd : GeneratedStep123CompleteOutput ρ βo .odd Ro)
    (hC1 : CofinalMomentSliceVanishingErrorBounds) : False := by
  obtain ⟨d, hd, hev⟩ := generated_pair_eventually_refutes_slice_bounds even odd
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / d) T)
  have hNd : 1 / d < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNT : T < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hNd
  obtain ⟨L, hLN, hbound⟩ := hC1 N (by exact_mod_cast hNpos)
  have hsmall : 1 / (N : ℝ) < d := by
    rw [div_lt_iff₀ hd] at hNd
    rw [div_lt_iff₀ hNpos]
    linarith
  exact hT L (by linarith) (1 / (N : ℝ)) hsmall hbound


/-- Conditional C1 consumer that uses the actual generated trial objects. -/
theorem riemannHypothesis_of_c1_through_generated_pair
    (hC1 : CofinalMomentSliceVanishingErrorBounds) : RiemannHypothesis := by
  intro s hz htriv hs1
  by_contra hoff
  have hcarrier : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  let ρ : zetaZeroConfig.carrier := ⟨s, hcarrier⟩
  let β := |s.re - 1 / 2| / 2
  have hgap : 0 < |s.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβρ : β < |(ρ : ℂ).re - 1 / 2| := by
    change |s.re - 1 / 2| / 2 < |s.re - 1 / 2|
    linarith
  obtain ⟨even⟩ := exists_generatedStep123CompleteOutput ρ hβ hβρ .even 0
  obtain ⟨odd⟩ := exists_generatedStep123CompleteOutput ρ hβ hβρ .odd 0
  exact generated_pair_excludes_c1 even odd hC1

end Zeta23.RHReference

#print axioms Zeta23.RHReference.generated_pair_eventually_refutes_slice_bounds
#print axioms Zeta23.RHReference.generated_pair_excludes_c1
#print axioms Zeta23.RHReference.riemannHypothesis_of_c1_through_generated_pair
