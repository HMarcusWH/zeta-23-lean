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

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeOutput.originalWeilEnergy_neg
#print axioms Zeta23.CCM.Step123NativeOutput.originalInterior_not_ae_zero
#print axioms Zeta23.CCM.Step123NativeOutput.originalInterior_ne_zero
