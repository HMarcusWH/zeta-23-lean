import Zeta23.CCM.OriginalDetectorNativeForcing

/-!
# Original-detector native exterior and interior history

This is an exact partition of the *actual original detector's* response,
not a selected-ground replacement and not a free C-Schur witness.
The original interior history is retained as a separate function and is
not assumed to vanish.  Only local interior L2 is asserted; neither
exterior tail is silently assigned global L2 membership.

The complete M21 packet needs additional source-specific history and
normal/Galerkin fields.  This module is its first concrete piece.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.CCM

def originalDetectorNativeResponse (σ : ReversalParity) (L : ℝ) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) : ℝ → ℂ :=
  nativeWeilResponse
    (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p))

def originalDetectorNativeLeftExterior (σ : ReversalParity) (L : ℝ) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) : ℝ → ℂ :=
  (Iio (0 : ℝ)).indicator (originalDetectorNativeResponse σ L Kd p)

def originalDetectorNativeInteriorHistory (σ : ReversalParity) (L : ℝ) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) : ℝ → ℂ :=
  (Icc (0 : ℝ) L).indicator (originalDetectorNativeResponse σ L Kd p)

def originalDetectorNativeRightExterior (σ : ReversalParity) (L : ℝ) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) : ℝ → ℂ :=
  (Ioi L).indicator (originalDetectorNativeResponse σ L Kd p)

/-- The disjoint seam convention is left x<0, interior 0≤x≤L,
right x>L.  The interior is preserved in the full reconstruction. -/
theorem originalDetectorNativeResponse_reconstruction
    (σ : ReversalParity) (L : ℝ) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) (hL : 0 ≤ L) (x : ℝ) :
    originalDetectorNativeResponse σ L Kd p x =
      originalDetectorNativeLeftExterior σ L Kd p x +
      originalDetectorNativeInteriorHistory σ L Kd p x +
      originalDetectorNativeRightExterior σ L Kd p x := by
  let f := originalDetectorNativeResponse σ L Kd p
  change f x = (Iio (0 : ℝ)).indicator f x +
      (Icc (0 : ℝ) L).indicator f x + (Ioi L).indicator f x
  by_cases hx0 : x < 0
  · have hl : x ∈ Iio (0 : ℝ) := hx0
    have hm : x ∉ Icc (0 : ℝ) L := by
      intro h
      exact (not_lt_of_ge h.1) hx0
    have hr : x ∉ Ioi L := by
      intro h
      linarith
    simp [Set.indicator_of_mem hl, Set.indicator_of_not_mem hm,
      Set.indicator_of_not_mem hr]
  · by_cases hxL : x ≤ L
    · have hl : x ∉ Iio (0 : ℝ) := hx0
      have hm : x ∈ Icc (0 : ℝ) L := ⟨le_of_not_gt hx0, hxL⟩
      have hr : x ∉ Ioi L := not_lt_of_ge hxL
      simp [Set.indicator_of_not_mem hl, Set.indicator_of_mem hm,
        Set.indicator_of_not_mem hr]
    · have hl : x ∉ Iio (0 : ℝ) := hx0
      have hm : x ∉ Icc (0 : ℝ) L := by
        intro h
        exact hxL h.2
      have hr : x ∈ Ioi L := lt_of_not_ge hxL
      simp [Set.indicator_of_not_mem hl, Set.indicator_of_not_mem hm,
        Set.indicator_of_mem hr]

/-- Only the physically justified local L2 assertion. -/
theorem originalDetectorNativeInteriorHistory_memLp_two (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) :
    MemLp (originalDetectorNativeInteriorHistory σ L Kd p) 2 volume := by
  have hpLegal : canonicalNativeCoefficientInclusion σ L Kd p ∈
      euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L Kd p
  have hpC : ContDiff ℝ 2
      (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) :=
    contDiff_localizedFiniteVector_of_boundaryFlat Kd _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat Kd _).mp hpLegal)
  have hpS : HasCompactSupport
      (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) :=
    localizedFiniteVector_hasCompactSupport L Kd _
  exact nativeWeilResponse_indicator_memLp_two hpC hpS 0 L

/-- Store every piece of one original response rather than independently
choosing a local or exterior surrogate. -/
structure OriginalDetectorNativeExteriorHistory (σ : ReversalParity) (L : ℝ)
    (Kd : ℕ) (p : nativePoleNeutralParitySpace σ L Kd) where
  response : ℝ → ℂ
  response_eq : response = originalDetectorNativeResponse σ L Kd p
  leftExterior : ℝ → ℂ
  left_eq : leftExterior = originalDetectorNativeLeftExterior σ L Kd p
  interiorHistory : ℝ → ℂ
  interior_eq : interiorHistory = originalDetectorNativeInteriorHistory σ L Kd p
  rightExterior : ℝ → ℂ
  right_eq : rightExterior = originalDetectorNativeRightExterior σ L Kd p
  reconstruct : ∀ x, response x =
    leftExterior x + interiorHistory x + rightExterior x

def originalDetectorNativeExteriorHistory (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) :
    OriginalDetectorNativeExteriorHistory σ L Kd p where
  response := originalDetectorNativeResponse σ L Kd p
  response_eq := rfl
  leftExterior := originalDetectorNativeLeftExterior σ L Kd p
  left_eq := rfl
  interiorHistory := originalDetectorNativeInteriorHistory σ L Kd p
  interior_eq := rfl
  rightExterior := originalDetectorNativeRightExterior σ L Kd p
  right_eq := rfl
  reconstruct := originalDetectorNativeResponse_reconstruction σ L Kd p hL.le

/-- The retained state uses its *original detector*, not its separately
selected ground, to construct the exterior/history record. -/
def originalDetectorRetainedExteriorHistory (σ : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (state : DetectorRetainedSchurState σ L Kd D hL) :
    OriginalDetectorNativeExteriorHistory σ L Kd state.detector :=
  originalDetectorNativeExteriorHistory σ hL Kd state.detector

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorNativeResponse_reconstruction
#print axioms Zeta23.CCM.originalDetectorNativeInteriorHistory_memLp_two
