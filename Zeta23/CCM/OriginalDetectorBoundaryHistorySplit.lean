import Zeta23.CCM.NativeOriginalExteriorHistory

/-!
# Exact original right-boundary convolution and nonzero interior history

For an actual compact continuous probe K supported in [-b,b], the
original smooth Weil response R is convolved at x=L-b+s, s>=0.
The unique physical transition at integration variable y=s-b
separates right exterior R|_(L,infinity) from the genuine, generally
NONZERO interior R|_[0,L]. No continuous-contact or vanishing-normal
hypothesis is inserted, and no global exterior L2 assertion is made.

This is the compact boundary decomposition needed for the native
original history; the full signed four-prime histories and common
finite arithmetic cutoff are constructed in NativeOriginalExteriorHistory.
-/

noncomputable section
open MeasureTheory Set
namespace Zeta23.CCM

/-- A pointwise compact-source boundary cut. The right exterior comes
from y<s-b; the original interior comes from y>=s-b. Endpoints are
owned by the interior. -/
theorem originalSmoothRightBoundary_pointwise_cut
    (σ a b s : ℝ) (K : ℝ → ℂ)
    (hKs : tsupport K ⊆ Icc (-b) b)
    (hb : 0 ≤ b)
    (hL : 2 * b ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    (hs : 0 ≤ s) (y : ℝ) :
    let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
    let z := L - b + s - y
    K y * originalSmoothWeilRightExterior σ a z =
      (Iio (s - b)).indicator
        (fun t : ℝ => K t * originalSmoothWeilResponse σ a
          (L - b + s - t)) y ∧
    K y * originalSmoothWeilInteriorHistory σ a z =
      (Ici (s - b)).indicator
        (fun t : ℝ => K t * originalSmoothWeilResponse σ a
          (L - b + s - t)) y := by
  dsimp only
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let z := L - b + s - y
  by_cases hk : y ∈ Icc (-b) b
  · have hz0 : 0 ≤ z := by
      dsimp [z]
      linarith [hk.2, hs, hL]
    by_cases hy : y < s - b
    · have hzR : z ∈ Ioi L := by
        change L < z
        dsimp [z]
        linarith
      have hzNot : z ∉ Icc (0 : ℝ) L := by
        intro h
        exact (not_lt_of_ge h.2) hzR
      have hyR : y ∈ Iio (s - b) := hy
      have hyNotI : y ∉ Ici (s - b) := not_le_of_gt hy
      constructor
      · simp [originalSmoothWeilRightExterior,
          Set.indicator_of_mem hzR, Set.indicator_of_mem hyR, z, L]
      · simp [originalSmoothWeilInteriorHistory,
          Set.indicator_of_notMem hzNot, Set.indicator_of_notMem hyNotI, z, L]
    · have hzL : z ≤ L := by
        dsimp [z]
        linarith
      have hzIn : z ∈ Icc (0 : ℝ) L := ⟨hz0, hzL⟩
      have hzNotR : z ∉ Ioi L := not_lt_of_ge hzL
      have hyNotR : y ∉ Iio (s - b) := hy
      have hyInI : y ∈ Ici (s - b) := le_of_not_gt hy
      constructor
      · simp [originalSmoothWeilRightExterior,
          Set.indicator_of_notMem hzNotR, Set.indicator_of_notMem hyNotR, z, L]
      · simp [originalSmoothWeilInteriorHistory,
          Set.indicator_of_mem hzIn, Set.indicator_of_mem hyInI, z, L]
  · have hzero : K y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hm => hk (hKs hm))
    constructor <;> simp [hzero]

/-- Fully source-bound convolution split. Both integrals exist because
the probe is continuous with compact support and the actual original
response is continuous; no L2 requirement is placed on exterior tails. -/
theorem originalSmoothRightBoundary_convolution_split
    (σ a b s : ℝ) (K : ℝ → ℂ)
    (hK : Continuous K)
    (hKs : tsupport K ⊆ Icc (-b) b)
    (hb : 0 ≤ b)
    (hL : 2 * b ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    (hs : 0 ≤ s) :
    let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
    (∫ y : ℝ, K y * originalSmoothWeilResponse σ a (L - b + s - y)) =
      (∫ y : ℝ, K y * originalSmoothWeilRightExterior σ a (L - b + s - y)) +
        (∫ y : ℝ, K y * originalSmoothWeilInteriorHistory σ a
          (L - b + s - y)) := by
  dsimp only
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  have hcR : Continuous (originalSmoothWeilResponse σ a) :=
    nativeWeilResponse_continuous
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_contDiff σ a)
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_hasCompactSupport σ a)
  have hc : Continuous (fun y : ℝ => K y *
      originalSmoothWeilResponse σ a (L - b + s - y)) :=
    hK.mul (hcR.comp (by fun_prop))
  have hkCompact : HasCompactSupport K :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport K) hKs
  have hfull : Integrable (fun y : ℝ => K y *
      originalSmoothWeilResponse σ a (L - b + s - y)) :=
    hc.integrable_of_hasCompactSupport hkCompact.mul_left
  have hcut (y : ℝ) :=
    originalSmoothRightBoundary_pointwise_cut σ a b s K hKs hb hL hs y
  have hRi : Integrable (fun y : ℝ => K y *
      originalSmoothWeilRightExterior σ a (L - b + s - y)) := by
    have heq :
        (fun y : ℝ => K y *
          originalSmoothWeilRightExterior σ a (L - b + s - y)) =
        (Iio (s - b)).indicator (fun y : ℝ => K y *
          originalSmoothWeilResponse σ a (L - b + s - y)) := by
      funext y
      exact (hcut y).1
    rw [heq]
    exact hfull.indicator measurableSet_Iio
  have hIi : Integrable (fun y : ℝ => K y *
      originalSmoothWeilInteriorHistory σ a (L - b + s - y)) := by
    have heq :
        (fun y : ℝ => K y *
          originalSmoothWeilInteriorHistory σ a (L - b + s - y)) =
        (Ici (s - b)).indicator (fun y : ℝ => K y *
          originalSmoothWeilResponse σ a (L - b + s - y)) := by
      funext y
      exact (hcut y).2
    rw [heq]
    exact hfull.indicator measurableSet_Ici
  have hp (y : ℝ) : K y * originalSmoothWeilResponse σ a (L - b + s - y) =
      K y * originalSmoothWeilRightExterior σ a (L - b + s - y) +
        K y * originalSmoothWeilInteriorHistory σ a (L - b + s - y) := by
    rw [(hcut y).1, (hcut y).2]
    by_cases hy : y < s - b
    · have hR : y ∈ Iio (s - b) := hy
      have hI : y ∉ Ici (s - b) := not_le_of_gt hy
      simp [Set.indicator_of_mem hR, Set.indicator_of_notMem hI]
    · have hR : y ∉ Iio (s - b) := hy
      have hI : y ∈ Ici (s - b) := le_of_not_gt hy
      simp [Set.indicator_of_notMem hR, Set.indicator_of_mem hI]
  calc
    (∫ y : ℝ, K y * originalSmoothWeilResponse σ a (L - b + s - y)) =
      ∫ y : ℝ, (K y * originalSmoothWeilRightExterior σ a
          (L - b + s - y)) +
          (K y * originalSmoothWeilInteriorHistory σ a
          (L - b + s - y)) := by
        apply integral_congr_ae
        filter_upwards with y
        exact hp y
    _ = _ := integral_add hRi hIi

end Zeta23.CCM

#print axioms Zeta23.CCM.originalSmoothRightBoundary_pointwise_cut
#print axioms Zeta23.CCM.originalSmoothRightBoundary_convolution_split
