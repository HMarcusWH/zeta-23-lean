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
    constructor
    · rw [hzero, zero_mul]
      by_cases hy : y ∈ Iio (s - b)
      · simp [Set.indicator_of_mem hy, hzero]
      · simp [Set.indicator_of_notMem hy]
    · rw [hzero, zero_mul]
      by_cases hy : y ∈ Ici (s - b)
      · simp [Set.indicator_of_mem hy, hzero]
      · simp [Set.indicator_of_notMem hy]

/-- An operator-free decomposition of the line integral at a single
physical transition. This abstract proof must run before any actual
Weil-source normalization or input-state definitions are unfolded. -/
private theorem originalBoundary_integral_partition (W : ℝ → ℂ)
    (hW : Integrable W) (c : ℝ) :
    (∫ y : ℝ, W y) =
      (∫ y : ℝ, (Iio c).indicator W y) +
        (∫ y : ℝ, (Ici c).indicator W y) := by
  have hleft : Integrable ((Iio c).indicator W) :=
    hW.indicator measurableSet_Iio
  have hright : Integrable ((Ici c).indicator W) :=
    hW.indicator measurableSet_Ici
  have hpoint (y : ℝ) :
      W y = (Iio c).indicator W y + (Ici c).indicator W y := by
    by_cases hy : y < c
    · have hl : y ∈ Iio c := hy
      have hr : y ∉ Ici c := not_le_of_gt hy
      simp only [Set.indicator_of_mem hl, Set.indicator_of_notMem hr, add_zero]
    · have hl : y ∉ Iio c := hy
      have hr : y ∈ Ici c := le_of_not_gt hy
      simp only [Set.indicator_of_notMem hl, Set.indicator_of_mem hr, zero_add]
  calc
    (∫ y : ℝ, W y) =
      ∫ y : ℝ, (Iio c).indicator W y + (Ici c).indicator W y := by
      apply integral_congr_ae
      filter_upwards with y
      exact hpoint y
    _ = _ := integral_add hleft hright

/-- Abstract, fully proved indicator interface. In particular it
does not normalize the native Weil response, select a contact, or
assume any vanishing interior; callers must PROVE both exact cuts. -/
private theorem originalBoundary_integral_partition_of_cuts
    (W E I : ℝ → ℂ) (t : ℝ)
    (hW : Integrable W)
    (hE : E = (Iio t).indicator W)
    (hI : I = (Ici t).indicator W) :
    (∫ y : ℝ, W y) = (∫ y : ℝ, E y) + (∫ y : ℝ, I y) := by
  rw [hE, hI]
  exact originalBoundary_integral_partition W hW t

/-! The source-specific pointwise theorem above supplies both exact cuts;
we do not elaborate a second higher-order generic convolution theorem. -/

/-- Continuous response paired with a compact continuous probe is integrable. -/
private theorem originalBoundary_compact_integrable
    (R K : ℝ → ℂ) (c : ℝ)
    (hR : Continuous R) (hK : Continuous K)
    (hKc : HasCompactSupport K) :
    Integrable (fun y : ℝ => K y * R (c - y)) := by
  have hc : Continuous (fun y : ℝ => K y * R (c - y)) :=
    hK.mul (hR.comp (by fun_prop))
  exact hc.integrable_of_hasCompactSupport hKc.mul_left

/-- Actual original Weil response at the true physical aperture:
the generic continuous-source theorem specializes WITHOUT normalizing
the Weil kernels inside the proof. This keeps the generally nonzero
original interior and all four signed prime histories unchanged. -/
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
  have hR : Continuous (originalSmoothWeilResponse σ a) :=
    nativeWeilResponse_continuous
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_contDiff σ a)
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_hasCompactSupport σ a)
  let W : ℝ → ℂ := fun y => K y * originalSmoothWeilResponse σ a
    (L - b + s - y)
  let E : ℝ → ℂ := fun y => K y * originalSmoothWeilRightExterior σ a
    (L - b + s - y)
  let I : ℝ → ℂ := fun y => K y * originalSmoothWeilInteriorHistory σ a
    (L - b + s - y)
  have hKc : HasCompactSupport K :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport K) hKs
  have hWi : Integrable W :=
    originalBoundary_compact_integrable (originalSmoothWeilResponse σ a) K
      (L - b + s) hR hK hKc
  have hE : E = (Iio (s - b)).indicator W := by
    funext y
    exact (originalSmoothRightBoundary_pointwise_cut σ a b s K
      hKs hb hL hs y).1
  have hI : I = (Ici (s - b)).indicator W := by
    funext y
    exact (originalSmoothRightBoundary_pointwise_cut σ a b s K
      hKs hb hL hs y).2
  change (∫ y : ℝ, W y) = (∫ y : ℝ, E y) + (∫ y : ℝ, I y)
  exact originalBoundary_integral_partition_of_cuts
    W E I (s - b) hWi hE hI

end Zeta23.CCM

#print axioms Zeta23.CCM.originalSmoothRightBoundary_pointwise_cut
#print axioms Zeta23.CCM.originalSmoothRightBoundary_convolution_split
