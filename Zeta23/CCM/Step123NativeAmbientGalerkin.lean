import Zeta23.CCM.Step123OutputData
import Zeta23.CCM.CanonicalPhysicalTrialRealization
import Zeta23.CCM.NativeWeilResponse

/-!
# Actual selected-ground ambient, legal, normal and outer Galerkin data

The selected ground and its lambda-shifted neutral equation remain
separate from the ORIGINAL detector and its -eta-shifted Schur loss.
The ambient response is the real Weil Arch+Pole-Prime response with both
arithmetic translations, restricted only on the physical aperture.
No full-line response L2 or zero outer residual is asserted.

Legal projection, pole-normal difference and outer Galerkin residual
are separate objects rather than renamed versions of one another.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- Physical boundary-flat legal carrier, not the larger unrestricted
Euclidean coefficient space and not the pole-neutral compression. -/
def canonicalLegalPhysicalIsometry {L : ℝ} (hL : 0 < L) (K : ℕ) :
    euclideanBoundaryFlatSubspace K →ₗᵢ[ℂ] CanonicalPhysicalL2 :=
  (canonicalPhysicalIsometry hL K).comp
    (euclideanBoundaryFlatSubspace K).subtypeₗᵢ

def canonicalLegalPhysicalProjection {L : ℝ} (hL : 0 < L) (K : ℕ) :
    CanonicalPhysicalL2 →L[ℂ] euclideanBoundaryFlatSubspace K :=
  ((canonicalLegalPhysicalIsometry hL K).toContinuousLinearMap :
    euclideanBoundaryFlatSubspace K →L[ℂ] CanonicalPhysicalL2).adjoint

theorem canonicalLegalPhysicalProjection_orthogonal {L : ℝ}
    (hL : 0 < L) (K : ℕ) (v : euclideanBoundaryFlatSubspace K)
    (g : CanonicalPhysicalL2) :
    inner ℂ (canonicalLegalPhysicalIsometry hL K v)
      (g - canonicalLegalPhysicalIsometry hL K
        (canonicalLegalPhysicalProjection hL K g)) = 0 := by
  have hAdj : inner ℂ (canonicalLegalPhysicalIsometry hL K v) g =
      inner ℂ v (canonicalLegalPhysicalProjection hL K g) := by
    rw [canonicalLegalPhysicalProjection, ContinuousLinearMap.adjoint_inner_right]
  have hIso : inner ℂ (canonicalLegalPhysicalIsometry hL K v)
      (canonicalLegalPhysicalIsometry hL K
        (canonicalLegalPhysicalProjection hL K g)) =
      inner ℂ v (canonicalLegalPhysicalProjection hL K g) :=
    (canonicalLegalPhysicalIsometry hL K).inner_map_map _ _
  rw [inner_sub_right, hAdj, hIso, sub_self]

def Step123NativeOutput.selectedPhysicalSource
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : ℝ → ℂ :=
  let state := out.retained.state
  finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) state.selection.cutoff
    (canonicalNativeCoefficientInclusion state.selectedParity
      (fixedOriginalSincTrialAperture a) state.selection.cutoff state.selectedGround)

theorem Step123NativeOutput.selectedPhysicalSource_contDiff
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ContDiff ℝ 2 out.selectedPhysicalSource := by
  let state := out.retained.state
  have hlegal :
      canonicalNativeCoefficientInclusion state.selectedParity
        (fixedOriginalSincTrialAperture a) state.selection.cutoff
        state.selectedGround ∈
      euclideanBoundaryFlatSubspace state.selection.cutoff := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal state.selectedParity
      (fixedOriginalSincTrialAperture a) state.selection.cutoff state.selectedGround
  exact contDiff_localizedFiniteVector_of_boundaryFlat state.selection.cutoff _
    out.aperture_pos
    ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat
      state.selection.cutoff _).mp hlegal)

theorem Step123NativeOutput.selectedPhysicalSource_compact
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    HasCompactSupport out.selectedPhysicalSource :=
  localizedFiniteVector_hasCompactSupport
    (fixedOriginalSincTrialAperture a)
    out.retained.state.selection.cutoff _

/-- A genuine local physical L2 response, with no assertion that
either infinite exterior tail is globally square integrable. -/
def Step123NativeOutput.selectedNativeResponseL2
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  (nativeWeilResponse_indicator_memLp_two
    out.selectedPhysicalSource_contDiff
    out.selectedPhysicalSource_compact
    0 (fixedOriginalSincTrialAperture a)).toLp
    ((Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)).indicator
      (nativeWeilResponse out.selectedPhysicalSource))

/-- The actual legal projected component of the selected ground's
physical response (before pole-normal removal). -/
def Step123NativeOutput.selectedLegalProjectedResponse
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  canonicalLegalPhysicalIsometry out.aperture_pos
    out.retained.state.selection.cutoff
    (canonicalLegalPhysicalProjection out.aperture_pos
      out.retained.state.selection.cutoff out.selectedNativeResponseL2)

/-- The actual neutral projected component, using the selected
parity and the selected lambda cutoff, not the original detector. -/
def Step123NativeOutput.selectedNeutralProjectedResponse
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  let state := out.retained.state
  canonicalNativePhysicalIsometry state.selectedParity out.aperture_pos
    state.selection.cutoff
    (canonicalNativePhysicalProjection state.selectedParity out.aperture_pos
      state.selection.cutoff out.selectedNativeResponseL2)

/-- Legal minus neutral = actual normal component, not a priori zero. -/
def Step123NativeOutput.selectedPoleNormalResidual
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  out.selectedLegalProjectedResponse - out.selectedNeutralProjectedResponse

/-- The physical response minus its LEGAL finite projection. -/
def Step123NativeOutput.selectedOuterGalerkinResidual
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  out.selectedNativeResponseL2 - out.selectedLegalProjectedResponse

theorem Step123NativeOutput.selectedOuterGalerkin_orthogonal
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : euclideanBoundaryFlatSubspace out.retained.state.selection.cutoff) :
    inner ℂ
      (canonicalLegalPhysicalIsometry out.aperture_pos
        out.retained.state.selection.cutoff v)
      out.selectedOuterGalerkinResidual = 0 :=
  canonicalLegalPhysicalProjection_orthogonal out.aperture_pos
    out.retained.state.selection.cutoff v out.selectedNativeResponseL2

/-- Three disjoint accounting terms with exact recombination; the
normal and outer terms are never silently discarded. -/
theorem Step123NativeOutput.selectedResponse_decomposition
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.selectedNativeResponseL2 =
      out.selectedNeutralProjectedResponse +
        out.selectedPoleNormalResidual +
        out.selectedOuterGalerkinResidual := by
  unfold Step123NativeOutput.selectedPoleNormalResidual
    Step123NativeOutput.selectedOuterGalerkinResidual
  abel

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalLegalPhysicalProjection_orthogonal
#print axioms Zeta23.CCM.Step123NativeOutput.selectedOuterGalerkin_orthogonal
#print axioms Zeta23.CCM.Step123NativeOutput.selectedResponse_decomposition
