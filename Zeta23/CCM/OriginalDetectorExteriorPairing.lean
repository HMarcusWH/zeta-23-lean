import Zeta23.CCM.NativeOriginalExteriorHistory

/-!
# Actual original exterior + nonzero interior in every compact mixed test

The original Weil response is physically continuous but its raw exterior
tails need not be globally L2.  Every compact continuous physical test
has a finite pairing with each indicated region separately, and the
three regional pairings sum to the exact original full mixed pairing.

This keeps both endpoint ownership and the actual interior response;
it never infers global exterior decay, contact, or kernel nullity.
-/
noncomputable section
open MeasureTheory Set
namespace Zeta23.CCM

private theorem originalRegion_pair_integrable
    {r g : ℝ → ℂ} (hr : Continuous r) (hg : Continuous g)
    (hgc : HasCompactSupport g) (S : Set ℝ) (hS : MeasurableSet S) :
    Integrable (fun x : ℝ => S.indicator r x * g x) := by
  have htotal : Integrable (fun x : ℝ => r x * g x) :=
    (hr.mul hg).integrable_of_hasCompactSupport hgc.mul_left
  have heq :
      (fun x : ℝ => S.indicator r x * g x) =
        S.indicator (fun x : ℝ => r x * g x) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  rw [heq]
  exact htotal.indicator hS

/-- The actual three-way exterior/interior partition, paired against
an arbitrary compact continuous complex test. No unproved vanishing of
the middle interval is needed. -/
theorem originalSmoothWeilResponse_compactPairing_split
    (σ a : ℝ)
    (hL : 0 ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, originalSmoothWeilResponse σ a x * g x) =
      (∫ x : ℝ, originalSmoothWeilLeftExterior σ a x * g x) +
        (∫ x : ℝ, originalSmoothWeilInteriorHistory σ a x * g x) +
        (∫ x : ℝ, originalSmoothWeilRightExterior σ a x * g x) := by
  let R := originalSmoothWeilResponse σ a
  have hR : Continuous R :=
    nativeWeilResponse_continuous
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_contDiff σ a)
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_hasCompactSupport σ a)
  have hleft : Integrable (fun x : ℝ =>
      originalSmoothWeilLeftExterior σ a x * g x) := by
    change Integrable
      (fun x : ℝ => (Iio (0 : ℝ)).indicator R x * g x)
    exact originalRegion_pair_integrable hR hg hgc _ measurableSet_Iio
  have hmiddle : Integrable (fun x : ℝ =>
      originalSmoothWeilInteriorHistory σ a x * g x) := by
    change Integrable
      (fun x : ℝ =>
        (Icc (0 : ℝ) (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)).indicator R x * g x)
    exact originalRegion_pair_integrable hR hg hgc _ measurableSet_Icc
  have hright : Integrable (fun x : ℝ =>
      originalSmoothWeilRightExterior σ a x * g x) := by
    change Integrable
      (fun x : ℝ =>
        (Ioi (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)).indicator R x * g x)
    exact originalRegion_pair_integrable hR hg hgc _ measurableSet_Ioi
  have hpoint (x : ℝ) :
      originalSmoothWeilResponse σ a x * g x =
        (originalSmoothWeilLeftExterior σ a x * g x +
         originalSmoothWeilInteriorHistory σ a x * g x) +
          originalSmoothWeilRightExterior σ a x * g x := by
    rw [originalSmoothWeilResponse_reconstruction σ a hL x]
    ring
  calc
    (∫ x : ℝ, originalSmoothWeilResponse σ a x * g x) =
      ∫ x : ℝ, (originalSmoothWeilLeftExterior σ a x * g x +
        originalSmoothWeilInteriorHistory σ a x * g x) +
        originalSmoothWeilRightExterior σ a x * g x := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
    _ = _ := by
      have houter := integral_add (hleft.add hmiddle) hright
  have hinner := integral_add hleft hmiddle
  have hcombine := houter.trans
    (congrArg (fun z : ℂ => z +
      ∫ x : ℝ, originalSmoothWeilRightExterior σ a x * g x) hinner)
  simpa only [Pi.add_apply] using hcombine

end Zeta23.CCM

#print axioms Zeta23.CCM.originalSmoothWeilResponse_compactPairing_split
