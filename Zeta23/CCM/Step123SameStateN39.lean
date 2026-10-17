import Zeta23.CCM.Step123OutputData

/-!
# N39: the actual native original interior does not vanish

The source producer proves a negative self-Weil value for the original
smooth trial before finite transport.  `Step123NativeOutput.ofRetained`
preserves that same-source proof as `original_depth`.

If the actual original interior vanished almost everywhere, its exact
physical response pairing with the unchanged smooth source would vanish:
the source is supported strictly inside the aperture.  The retained
original depth contradicts this.  No zero parameter, closing law, global
exterior L2 property, selected-ground substitution or second choice is used.

The same packet also exposes the literal causal exterior coordinates
`t ↦ R(-t)` and `t ↦ R(L+t)`, both with the open-positive-time indicator.
Their values at t=0 vanish because the interior owns the physical seams.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- The producer's original smooth negative depth is preserved at the
same separation as the stored finite detector, in the rho-free packet. -/
theorem Step123NativeOutput.originalWeilEnergy_neg
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    (zetaZeroConfig.W out.originalTrial out.originalTrial).re < 0 := by
  have h := out.original_depth
  have hexp := Real.exp_pos (β * fixedOriginalSincTrialAperture a)
  change (zetaZeroConfig.W
    (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a)
    (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a)).re < 0
  linarith

/-- The actual original interior of the stored native packet is nonzero
as an almost-everywhere class.  The exact pairing uses the original
smooth source, not the selected finite ground. -/
theorem Step123NativeOutput.originalInterior_not_ae_zero
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ¬ (out.smoothOriginal.interior =ᵐ[volume] (0 : ℝ → ℂ)) := by
  intro hzero
  let phase := nativeOriginalDetectorPhaseSign σ
  let L := fixedOriginalSincTrialAperture a
  let f := fixedOriginalSincPhaseTrial phase a
  have hasep : UniversalSinc.fixedScale < a := by
    have h4 := out.aperture_gt_four
    unfold fixedOriginalSincTrialAperture fixedOriginalSincLobeCenter at h4
    have hs : UniversalSinc.fixedScale = 1 / 4096 := rfl
    rw [hs] at h4 ⊢
    linarith
  have hsupport : tsupport f ⊆ Icc 1 (L - 1) :=
    fixedOriginalSincPhaseTrial_support hasep phase
  have hpair_zero :
      (fun x : ℝ => nativeWeilResponse f x * conj (f x)) =ᵐ[volume]
        (0 : ℝ → ℂ) := by
    filter_upwards [hzero] with x hxzero
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · have hinterior : out.smoothOriginal.interior x =
          nativeWeilResponse f x := by
        rw [out.smoothOriginal.interior_eq]
        change (Icc (0 : ℝ) L).indicator (nativeWeilResponse f) x = _
        exact Set.indicator_of_mem hx _
      have hresponse : nativeWeilResponse f x = 0 := by
        rw [← hinterior]
        exact hxzero
      simp only [hresponse, zero_mul, Pi.zero_apply]
    · have hfx : f x = 0 := by
        by_contra hne
        have hs := hsupport (subset_closure hne)
        apply hx
        constructor <;> linarith [hs.1, hs.2]
      simp only [hfx, map_zero, mul_zero, Pi.zero_apply]
  have hW : zetaZeroConfig.W f f = 0 := by
    calc
      zetaZeroConfig.W f f =
          ∫ x : ℝ, nativeWeilResponse f x * conj (f x) :=
        nativeWeilResponse_pairing
          (fixedOriginalSincPhaseTrial_contDiff phase a)
          (fixedOriginalSincPhaseTrial_hasCompactSupport phase a)
          (fixedOriginalSincPhaseTrial_contDiff phase a).continuous
          (fixedOriginalSincPhaseTrial_hasCompactSupport phase a)
      _ = ∫ x : ℝ, (0 : ℝ → ℂ) x := integral_congr_ae hpair_zero
      _ = 0 := by simp
  have hnegative : (zetaZeroConfig.W f f).re < 0 := out.originalWeilEnergy_neg
  rw [hW] at hnegative
  norm_num at hnegative

/-- In particular, the actual native original interior is not the zero
function.  Its proof uses the retained original-depth theorem. -/
theorem Step123NativeOutput.originalInterior_ne_zero
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.smoothOriginal.interior ≠ (0 : ℝ → ℂ) := by
  intro hzero
  apply out.originalInterior_not_ae_zero
  exact Filter.Eventually.of_forall (fun x => congrFun hzero x)

/-- The actual original left exterior in causal time, with t=0 owned by
the original interior. This is a view of the same stored response. -/
def Step123NativeOutput.originalLeftCausalTail
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : ℝ → ℂ :=
  fun t => out.smoothOriginal.left (-t)

/-- The actual original right exterior in causal time, with t=0 owned by
the original interior. No exterior L2 property is asserted. -/
def Step123NativeOutput.originalRightCausalTail
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : ℝ → ℂ :=
  fun t => out.smoothOriginal.right (fixedOriginalSincTrialAperture a + t)

theorem Step123NativeOutput.originalLeftCausalTail_eq_indicator
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.originalLeftCausalTail =
      (Ioi (0 : ℝ)).indicator (fun t => out.smoothOriginal.response (-t)) := by
  funext t
  unfold Step123NativeOutput.originalLeftCausalTail
  rw [out.smoothOriginal.left_eq, out.smoothOriginal.response_eq]
  change (Iio (0 : ℝ)).indicator
      (originalSmoothWeilResponse (nativeOriginalDetectorPhaseSign σ) a) (-t) =
    (Ioi (0 : ℝ)).indicator
      (fun t => originalSmoothWeilResponse (nativeOriginalDetectorPhaseSign σ) a (-t)) t
  by_cases ht : 0 < t
  · have hn : -t ∈ Iio (0 : ℝ) := by change -t < 0; linarith
    rw [Set.indicator_of_mem hn, Set.indicator_of_mem ht]
  · have hn : -t ∉ Iio (0 : ℝ) := by change ¬ -t < 0; linarith
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem ht]

theorem Step123NativeOutput.originalRightCausalTail_eq_indicator
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.originalRightCausalTail =
      (Ioi (0 : ℝ)).indicator
        (fun t => out.smoothOriginal.response (fixedOriginalSincTrialAperture a + t)) := by
  funext t
  unfold Step123NativeOutput.originalRightCausalTail
  rw [out.smoothOriginal.right_eq, out.smoothOriginal.response_eq]
  change (Ioi (fixedOriginalSincTrialAperture a)).indicator
      (originalSmoothWeilResponse (nativeOriginalDetectorPhaseSign σ) a)
        (fixedOriginalSincTrialAperture a + t) =
    (Ioi (0 : ℝ)).indicator
      (fun t => originalSmoothWeilResponse (nativeOriginalDetectorPhaseSign σ) a
        (fixedOriginalSincTrialAperture a + t)) t
  by_cases ht : 0 < t
  · have hn : fixedOriginalSincTrialAperture a + t ∈
        Ioi (fixedOriginalSincTrialAperture a) := by
      change fixedOriginalSincTrialAperture a < fixedOriginalSincTrialAperture a + t
      linarith
    rw [Set.indicator_of_mem hn, Set.indicator_of_mem ht]
  · have hn : fixedOriginalSincTrialAperture a + t ∉
        Ioi (fixedOriginalSincTrialAperture a) := by
      change ¬ fixedOriginalSincTrialAperture a < fixedOriginalSincTrialAperture a + t
      linarith
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem ht]

/-- Both original exterior tails are exactly zero at nonpositive causal
time, including the seams t=0. -/
theorem Step123NativeOutput.originalCausalTails_zero_of_nonpos
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) {t : ℝ} (ht : t ≤ 0) :
    out.originalLeftCausalTail t = 0 ∧ out.originalRightCausalTail t = 0 := by
  have hn : t ∉ Ioi (0 : ℝ) := not_lt_of_ge ht
  constructor
  · rw [out.originalLeftCausalTail_eq_indicator]
    exact Set.indicator_of_notMem hn _
  · rw [out.originalRightCausalTail_eq_indicator]
    exact Set.indicator_of_notMem hn _

/-- Exact physical reconstruction from the same two causal tail views
and the stored interior, with the interior owning both endpoints. -/
theorem Step123NativeOutput.originalResponse_causalTail_reconstruction
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (x : ℝ) :
    out.smoothOriginal.response x = out.originalLeftCausalTail (-x) +
      out.smoothOriginal.interior x +
        out.originalRightCausalTail (x - fixedOriginalSincTrialAperture a) := by
  change out.smoothOriginal.response x = out.smoothOriginal.left (-(-x)) +
    out.smoothOriginal.interior x +
      out.smoothOriginal.right
        (fixedOriginalSincTrialAperture a + (x - fixedOriginalSincTrialAperture a))
  rw [neg_neg, show fixedOriginalSincTrialAperture a +
      (x - fixedOriginalSincTrialAperture a) = x by ring]
  exact out.smoothOriginal.reconstruction x

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeOutput.originalWeilEnergy_neg
#print axioms Zeta23.CCM.Step123NativeOutput.originalInterior_not_ae_zero
#print axioms Zeta23.CCM.Step123NativeOutput.originalInterior_ne_zero
#print axioms Zeta23.CCM.Step123NativeOutput.originalLeftCausalTail_eq_indicator
#print axioms Zeta23.CCM.Step123NativeOutput.originalRightCausalTail_eq_indicator
#print axioms Zeta23.CCM.Step123NativeOutput.originalCausalTails_zero_of_nonpos
#print axioms Zeta23.CCM.Step123NativeOutput.originalResponse_causalTail_reconstruction
