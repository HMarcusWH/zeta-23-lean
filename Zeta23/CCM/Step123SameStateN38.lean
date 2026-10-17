import Zeta23.CCM.Step123NativeAmbientGalerkin
import Zeta23.CCM.OriginalDetectorNativeForcing
import Zeta23.CCM.CanonicalPoleNeutralNormals

/-!
# N38: the ORIGINAL detector's legal, neutral, normal and outer response

Every object below is computed from the stored original detector at its own
quartic carrier Kd and original parity.  The physical response is the literal
Weil response restricted to the aperture; its exterior is not assumed to be
globally square integrable.  The legal projection, its pole-normal difference
from neutral compression, and the outer Galerkin residual remain distinct.
Their exact recombination and orthogonality do not assert any term vanishes.

The final bridge projects the same response plus eta times the same physical
detector onto the actual predecessor.  It identifies this projection with the
stored forcing at the original shift -eta, independently of the selected
ground's lambda shift.  No RH or Step 4 antecedent is proved here.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

private def n38_nativeLegalView (σ : ReversalParity) (L : ℝ) (K : ℕ) :
    nativePoleNeutralParitySpace σ L K → euclideanParityBoundaryFlatSubspace σ K := by
  cases σ
  · exact fun p => p.val
  · exact fun p => p.val

private theorem n38_nativeLegalView_ambient (σ : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace σ L K) :
    canonicalNativeCoefficientInclusion σ L K p =
      (n38_nativeLegalView σ L K p : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  cases σ <;> rfl

private theorem n38_parityLegal_mem_legal (σ : ReversalParity) (K : ℕ)
    (p : euclideanParityBoundaryFlatSubspace σ K) :
    (p : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈ euclideanBoundaryFlatSubspace K := by
  cases σ
  · exact (mem_euclideanBoundaryFlatSubspace_iff K _).mpr
      ((mem_euclideanEvenBoundaryFlatSubspace_iff K _).mp p.property).1
  · exact (mem_euclideanBoundaryFlatSubspace_iff K _).mpr
      ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp p.property).1

/-- The complete legal boundary conditions annihilate all three boundary normals. -/
private theorem n38_power_mem_legalOrthogonal (K r : ℕ) (hr : r < 3) :
    centeredPowerVector K r ∈ (euclideanBoundaryFlatSubspace K)ᗮ := by
  rw [(euclideanBoundaryFlatSubspace K).mem_orthogonal]
  intro x hx
  rw [inner_eq_zero_symm, inner_centeredPowerVector]
  have hf := (mem_boundaryFlatSubspace_iff K _).mp
    ((mem_euclideanBoundaryFlatSubspace_iff K x).mp hx)
  interval_cases r
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2

/-- Compression of the actual parity-preserving matrix loses only the
boundary normals, which are orthogonal to the FULL legal carrier. -/
private theorem n38_parityCompressionResidual_mem_legalOrthogonal
    (σ : ReversalParity) (L : ℝ) (K : ℕ)
    (p : euclideanParityBoundaryFlatSubspace σ K) :
    (canonicalSourceMatrix L K).toEuclideanLin p -
      (parityCompressedCanonical σ L K p : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        (euclideanBoundaryFlatSubspace K)ᗮ := by
  cases σ with
  | even =>
    have h := evenCompressionResidual_mem_evenNormalSubspace L K p
    have hle : evenNormalSubspace K ≤ (euclideanBoundaryFlatSubspace K)ᗮ := by
      apply sup_le
      · exact (Submodule.span_singleton_le_iff_mem).mpr
          (n38_power_mem_legalOrthogonal K 0 (by omega))
      · exact (Submodule.span_singleton_le_iff_mem).mpr
          (n38_power_mem_legalOrthogonal K 2 (by omega))
    exact hle h
  | odd =>
    let y := (canonicalSourceMatrix L K).toEuclideanLin p
    let q := (oddCompressedCanonical L K p : EuclideanSpace ℂ (Fin (2 * K + 1)))
    have ho : y - q ∈ (euclideanOddBoundaryFlatSubspace K)ᗮ :=
      (euclideanOddBoundaryFlatSubspace K).sub_starProjection_mem_orthogonal y
    have hp : (p : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        euclideanOddCoefficientSubspace K :=
      ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp p.property).2
    have hy : y ∈ euclideanOddCoefficientSubspace K :=
      canonicalSourceMatrix_toEuclideanLin_mem_oddCoefficient L K hp
    have hq : q ∈ euclideanOddCoefficientSubspace K :=
      ((mem_euclideanOddBoundaryFlatSubspace_iff K _).mp
        (oddCompressedCanonical L K p).property).2
    have hn : y - q ∈ oddNormalSubspace K := by
      rw [← oddBoundaryFlat_normal_eq_oddNormalSubspace]
      exact ⟨ho, (euclideanOddCoefficientSubspace K).sub_mem hy hq⟩
    have hle : oddNormalSubspace K ≤ (euclideanBoundaryFlatSubspace K)ᗮ :=
      (Submodule.span_singleton_le_iff_mem).mpr
        (n38_power_mem_legalOrthogonal K 1 (by omega))
    exact hle hn

/-- The actual elementary-pole normal in the original legal parity. -/
def canonicalParityPoleLegalNormal (σ : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace σ K := by
  cases σ
  · exact canonicalPoleEvenLegalNormal L K
  · exact canonicalPoleOddLegalNormal L K

def canonicalParityPolePhysicalNormal (σ : ReversalParity) {L : ℝ}
    (hL : 0 < L) (K : ℕ) : CanonicalPhysicalL2 :=
  canonicalPhysicalIsometry hL K (canonicalParityPoleLegalNormal σ L K)

private theorem n38_parityPoleResidual_line (σ : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace σ L K) :
    ∃ c : ℂ,
      (parityCompressedCanonical σ L K (n38_nativeLegalView σ L K p) :
          EuclideanSpace ℂ (Fin (2 * K + 1))) -
        canonicalNativeCoefficientInclusion σ L K
          (nativePoleNeutralParityCanonical σ L K p) =
      c • (canonicalParityPoleLegalNormal σ L K :
        EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  cases σ with
  | even =>
    refine ⟨poleNeutralEvenOutputCoefficient L K p, ?_⟩
    exact congrArg (fun z : euclideanEvenBoundaryFlatSubspace K =>
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))))
      (poleNeutralEvenOutputResidual_eq_normal L K p)
  | odd =>
    let g := canonicalPoleOddLegalNormal L K
    let y := oddCompressedCanonical L K p.val
    refine ⟨inner ℂ g y / inner ℂ g g, ?_⟩
    have h : y - (poleNeutralOddCompressedCanonical L K p :
        euclideanOddBoundaryFlatSubspace K) =
        (inner ℂ g y / inner ℂ g g) • g := by
      rw [coe_poleNeutralOddCompressedCanonical,
        Submodule.coe_orthogonalProjectionOnto_apply]
      have hp : (poleNeutralOddSubspace L K).starProjection =
          ((ℂ ∙ canonicalPoleOddLegalNormal L K)ᗮ).starProjection := by
        rw [poleNeutralOddSubspace_eq_orthogonal_normal]
      rw [hp, Submodule.starProjection_orthogonal_val, sub_sub_cancel,
        Submodule.starProjection_singleton ℂ]
      simp only [g, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
    exact congrArg (fun z : euclideanOddBoundaryFlatSubspace K =>
      (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) h

/-- The actual finite physical source of the ORIGINAL stored detector. -/
def Step123NativeOutput.originalDetectorPhysicalSource
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : ℝ → ℂ :=
  finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      out.retained.state.detector)

theorem Step123NativeOutput.originalDetectorPhysicalSource_contDiff
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ContDiff ℝ 2 out.originalDetectorPhysicalSource := by
  let Kd := originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)
  have hlegal : canonicalNativeCoefficientInclusion σ
      (fixedOriginalSincTrialAperture a) Kd out.retained.state.detector ∈
      euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ _ Kd out.retained.state.detector
  exact contDiff_localizedFiniteVector_of_boundaryFlat Kd _ out.aperture_pos
    ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat Kd _).mp hlegal)

theorem Step123NativeOutput.originalDetectorPhysicalSource_compact
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    HasCompactSupport out.originalDetectorPhysicalSource :=
  localizedFiniteVector_hasCompactSupport (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) _

theorem Step123NativeOutput.physicalFiniteImage_ae_originalDetector
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.physicalFiniteImage =ᵐ[volume] out.originalDetectorPhysicalSource :=
  canonicalNativePhysicalIsometry_ae σ out.aperture_pos _ out.retained.state.detector

/-- Only the aperture restriction is made into an L2 vector. -/
def Step123NativeOutput.originalDetectorNativeResponseL2
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  (nativeWeilResponse_indicator_memLp_two
    out.originalDetectorPhysicalSource_contDiff
    out.originalDetectorPhysicalSource_compact 0
    (fixedOriginalSincTrialAperture a)).toLp
    ((Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)).indicator
      (nativeWeilResponse out.originalDetectorPhysicalSource))

theorem Step123NativeOutput.originalDetectorNativeResponseL2_ae
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.originalDetectorNativeResponseL2 =ᵐ[volume]
      (Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)).indicator
        (nativeWeilResponse out.originalDetectorPhysicalSource) :=
  MemLp.coeFn_toLp _

/-- Phi_legal^* of the actual original response, before neutral compression. -/
def Step123NativeOutput.originalDetectorLegalResponseCoordinate
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    euclideanBoundaryFlatSubspace
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) :=
  canonicalLegalPhysicalProjection out.aperture_pos _ out.originalDetectorNativeResponseL2

def Step123NativeOutput.originalDetectorLegalProjectedResponse
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  canonicalLegalPhysicalIsometry out.aperture_pos _
    out.originalDetectorLegalResponseCoordinate

theorem canonicalLegalPhysicalProjection_inner {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanBoundaryFlatSubspace K) (g : CanonicalPhysicalL2) :
    inner ℂ v (canonicalLegalPhysicalProjection hL K g) =
      ∫ x : ℝ, conj (finitePhysicalSynthesis L K v x) * g x := by
  letI : CompleteSpace (euclideanBoundaryFlatSubspace K) :=
    FiniteDimensional.complete ℂ (euclideanBoundaryFlatSubspace K)
  rw [canonicalLegalPhysicalProjection, ContinuousLinearMap.adjoint_inner_right,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [canonicalPhysicalIsometry_ae hL K v] with x hx
  change inner ℂ (canonicalPhysicalIsometry hL K v x) (g x) = _
  rw [hx]
  simp only [RCLike.inner_apply, mul_comm]

/-- The FULL legal response coordinate is determined against all legal tests. -/
theorem Step123NativeOutput.originalDetectorLegalResponseCoordinate_inner
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : euclideanBoundaryFlatSubspace
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))) :
    inner ℂ v out.originalDetectorLegalResponseCoordinate =
      inner ℂ (v : EuclideanSpace ℂ
        (Fin (2 * originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) + 1)))
        ((canonicalSourceMatrix (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))).toEuclideanLin
          (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
            (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
            out.retained.state.detector)) := by
  let L := fixedOriginalSincTrialAperture a
  let Kd := originalDetectorQuarticCutoff L
  have hv : ContDiff ℝ 2 (finitePhysicalSynthesis L Kd v) :=
    contDiff_localizedFiniteVector_of_boundaryFlat Kd _ out.aperture_pos
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat Kd _).mp v.property)
  have hp : canonicalNativeCoefficientInclusion σ L Kd out.retained.state.detector ∈
      euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L Kd out.retained.state.detector
  rw [Step123NativeOutput.originalDetectorLegalResponseCoordinate,
    canonicalLegalPhysicalProjection_inner]
  calc
    _ = ∫ x : ℝ, nativeWeilResponse out.originalDetectorPhysicalSource x *
        conj (finitePhysicalSynthesis L Kd v x) := by
      apply integral_congr_ae
      filter_upwards [out.originalDetectorNativeResponseL2_ae] with x hx
      rw [hx]
      by_cases hm : x ∈ Icc (0 : ℝ) L
      · rw [Set.indicator_of_mem hm, mul_comm]
      · rw [Set.indicator_of_notMem hm]
        have hz : finitePhysicalSynthesis L Kd v x = 0 := by
          unfold finitePhysicalSynthesis
          rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hm]
        simp only [hz, map_zero, mul_zero]
    _ = zetaZeroConfig.W out.originalDetectorPhysicalSource
        (finitePhysicalSynthesis L Kd v) :=
      (nativeWeilResponse_pairing out.originalDetectorPhysicalSource_contDiff
        out.originalDetectorPhysicalSource_compact hv.continuous
        (localizedFiniteVector_hasCompactSupport L Kd _)).symm
    _ = _ := canonicalPhysicalSynthesis_mixed_Weil out.aperture_pos Kd _ _ hp v.property

/-- The full legal projection has the original parity.  It equals the
actual parity-compressed canonical output, with no opposite-parity part. -/
theorem Step123NativeOutput.originalDetectorLegalResponseCoordinate_eq_parityCompressed
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    (out.originalDetectorLegalResponseCoordinate : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) + 1))) =
      (parityCompressedCanonical σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        (n38_nativeLegalView σ (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
          out.retained.state.detector) : EuclideanSpace ℂ
            (Fin (2 * originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) + 1))) := by
  let L := fixedOriginalSincTrialAperture a
  let Kd := originalDetectorQuarticCutoff L
  let p := n38_nativeLegalView σ L Kd out.retained.state.detector
  let q := parityCompressedCanonical σ L Kd p
  let qlegal : euclideanBoundaryFlatSubspace Kd :=
    ⟨q, n38_parityLegal_mem_legal σ Kd q⟩
  have heq : out.originalDetectorLegalResponseCoordinate = qlegal := by
    apply ext_inner_left ℂ
    intro v
    have hmatrix := out.originalDetectorLegalResponseCoordinate_inner v
    rw [n38_nativeLegalView_ambient] at hmatrix
    rw [hmatrix]
    have horth := n38_parityCompressionResidual_mem_legalOrthogonal σ L Kd p
    have hz := ((euclideanBoundaryFlatSubspace Kd).mem_orthogonal _).mp horth
      (v : EuclideanSpace ℂ (Fin (2 * Kd + 1))) v.property
    rw [inner_sub_right] at hz
    exact sub_eq_zero.mp hz
  exact congrArg (fun z : euclideanBoundaryFlatSubspace Kd =>
    (z : EuclideanSpace ℂ (Fin (2 * Kd + 1)))) heq

theorem Step123NativeOutput.originalDetectorLegalResponseCoordinate_mem_parity
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    (out.originalDetectorLegalResponseCoordinate : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) + 1))) ∈
      euclideanParityBoundaryFlatSubspace σ
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) := by
  rw [out.originalDetectorLegalResponseCoordinate_eq_parityCompressed]
  exact (parityCompressedCanonical σ _ _ _).property

/-- The neutral coordinate uses the original parity and detector cutoff. -/
def Step123NativeOutput.originalDetectorNeutralResponseCoordinate
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) :=
  canonicalNativePhysicalProjection σ out.aperture_pos _
    out.originalDetectorNativeResponseL2

def Step123NativeOutput.originalDetectorNeutralProjectedResponse
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  canonicalNativePhysicalIsometry σ out.aperture_pos _
    out.originalDetectorNeutralResponseCoordinate

/-- Legal minus neutral, distinct from the exterior and outer residuals. -/
def Step123NativeOutput.originalDetectorPoleNormalResidual
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  out.originalDetectorLegalProjectedResponse - out.originalDetectorNeutralProjectedResponse

/-- The actual local response minus its legal finite projection. -/
def Step123NativeOutput.originalDetectorOuterGalerkinResidual
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  out.originalDetectorNativeResponseL2 - out.originalDetectorLegalProjectedResponse

theorem Step123NativeOutput.originalDetectorOuterGalerkin_orthogonal
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : euclideanBoundaryFlatSubspace
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))) :
    inner ℂ (canonicalLegalPhysicalIsometry out.aperture_pos _ v)
      out.originalDetectorOuterGalerkinResidual = 0 :=
  canonicalLegalPhysicalProjection_orthogonal out.aperture_pos _ v
    out.originalDetectorNativeResponseL2

/-- Normal removal is orthogonal on the ORIGINAL neutral carrier. -/
theorem Step123NativeOutput.originalDetectorPoleNormal_orthogonal
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))) :
    inner ℂ (canonicalNativePhysicalIsometry σ out.aperture_pos _ v)
      out.originalDetectorPoleNormalResidual = 0 := by
  let Kd := originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)
  have hlegal : canonicalNativeCoefficientInclusion σ
      (fixedOriginalSincTrialAperture a) Kd v ∈ euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ _ Kd v
  let vlegal : euclideanBoundaryFlatSubspace Kd :=
    ⟨canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) Kd v,
      hlegal⟩
  have ho := out.originalDetectorOuterGalerkin_orthogonal vlegal
  have hn := canonicalNativePhysicalProjection_orthogonal σ out.aperture_pos Kd v
    out.originalDetectorNativeResponseL2
  change inner ℂ (canonicalNativePhysicalIsometry σ out.aperture_pos Kd v)
    (out.originalDetectorNativeResponseL2 - out.originalDetectorLegalProjectedResponse) = 0 at ho
  change inner ℂ (canonicalNativePhysicalIsometry σ out.aperture_pos Kd v)
    (out.originalDetectorNativeResponseL2 - out.originalDetectorNeutralProjectedResponse) = 0 at hn
  change inner ℂ (canonicalNativePhysicalIsometry σ out.aperture_pos Kd v)
    (out.originalDetectorLegalProjectedResponse - out.originalDetectorNeutralProjectedResponse) = 0
  rw [inner_sub_right] at ho hn ⊢
  exact sub_eq_zero.mpr ((sub_eq_zero.mp ho).symm.trans (sub_eq_zero.mp hn))

theorem Step123NativeOutput.originalDetectorResponse_decomposition
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.originalDetectorNativeResponseL2 =
      out.originalDetectorNeutralProjectedResponse +
        out.originalDetectorPoleNormalResidual + out.originalDetectorOuterGalerkinResidual := by
  unfold Step123NativeOutput.originalDetectorPoleNormalResidual
    Step123NativeOutput.originalDetectorOuterGalerkinResidual
  abel

/-- The physical neutral compression is the actual canonical operator on p. -/
theorem Step123NativeOutput.originalDetectorNeutralResponseCoordinate_eq
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.originalDetectorNeutralResponseCoordinate =
      nativePoleNeutralParityCanonical σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector := by
  apply ext_inner_left ℂ
  intro v
  rw [Step123NativeOutput.originalDetectorNeutralResponseCoordinate,
    canonicalNativePhysicalProjection_inner]
  calc
    _ = ∫ x : ℝ, nativeWeilResponse out.originalDetectorPhysicalSource x *
        conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
          (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
            (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) v) x) := by
      apply integral_congr_ae
      filter_upwards [out.originalDetectorNativeResponseL2_ae] with x hx
      rw [hx]
      by_cases hm : x ∈ Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)
      · rw [Set.indicator_of_mem hm, mul_comm]
      · rw [Set.indicator_of_notMem hm]
        have hv : finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
            (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
            (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
              (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) v) x = 0 := by
          unfold finitePhysicalSynthesis
          rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hm]
        simp only [hv, map_zero, mul_zero]
    _ = _ := originalDetector_nativeWeil_mixed σ out.aperture_pos _
      out.retained.state.detector v

/-- The removed response is on the TRUE elementary-pole normal line.
The full legal projection has already been proved to retain the original
parity, so no opposite-parity legal component is hidden in this identity. -/
theorem Step123NativeOutput.originalDetectorPoleNormal_eq_smul_poleNormal
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ∃ c : ℂ, out.originalDetectorPoleNormalResidual =
      c • canonicalParityPolePhysicalNormal σ out.aperture_pos
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) := by
  obtain ⟨c, hc⟩ := n38_parityPoleResidual_line σ
    (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    out.retained.state.detector
  refine ⟨c, ?_⟩
  change canonicalPhysicalIsometry out.aperture_pos _
      (out.originalDetectorLegalResponseCoordinate : EuclideanSpace ℂ _) -
    canonicalPhysicalIsometry out.aperture_pos _
      (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) _
        out.originalDetectorNeutralResponseCoordinate) =
    c • canonicalPhysicalIsometry out.aperture_pos _
      (canonicalParityPoleLegalNormal σ (fixedOriginalSincTrialAperture a) _)
  rw [out.originalDetectorLegalResponseCoordinate_eq_parityCompressed,
    out.originalDetectorNeutralResponseCoordinate_eq, ← map_sub, hc, map_smul]

/-- The predecessor adjoint acts on the same physical realization. -/
theorem canonicalNativePhysicalProjection_predecessor_eq
    (σ : ReversalParity) {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL) (g : CanonicalPhysicalL2) :
    canonicalNativePhysicalProjection σ hL (s.cutoff - 1) g =
      (nativeDetectorPredecessorEmbedding σ s).toLinearMap.adjoint
        (canonicalNativePhysicalProjection σ hL Kd g) := by
  apply ext_inner_left ℂ
  intro v
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ v (canonicalNativePhysicalProjection σ hL (s.cutoff - 1) g) =
    inner ℂ (nativeDetectorPredecessorEmbedding σ s v)
      (canonicalNativePhysicalProjection σ hL Kd g)
  rw [canonicalNativePhysicalProjection, canonicalNativePhysicalProjection,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    canonicalNativePhysicalIsometry_predecessor]

/-- Original shift -eta means the local physical forcing contains +eta p. -/
def Step123NativeOutput.originalDetectorShiftedPhysicalResponse
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  out.originalDetectorNativeResponseL2 +
    (out.retained.state.selection.eta : ℂ) • out.physicalFiniteImage

theorem Step123NativeOutput.originalDetectorShiftedResponseCoordinate_eq
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    canonicalNativePhysicalProjection σ out.aperture_pos
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      out.originalDetectorShiftedPhysicalResponse =
      nativePoleNeutralParityShifted σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        (-out.retained.state.selection.eta) out.retained.state.detector := by
  rw [Step123NativeOutput.originalDetectorShiftedPhysicalResponse, map_add, map_smul]
  change out.originalDetectorNeutralResponseCoordinate +
    (out.retained.state.selection.eta : ℂ) •
      canonicalNativePhysicalProjection σ out.aperture_pos _
        (canonicalNativePhysicalIsometry σ out.aperture_pos _
          out.retained.state.detector) = _
  rw [canonicalNativePhysicalProjection_synthesis,
    out.originalDetectorNeutralResponseCoordinate_eq]
  simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Complex.ofReal_neg, neg_smul, sub_neg_eq_add]

/-- The physical predecessor projection is literally the stored b_eta. -/
theorem Step123NativeOutput.n38_originalDetector_predecessorForcing_eq
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    canonicalNativePhysicalProjection σ out.aperture_pos
      (out.retained.state.selection.cutoff - 1)
      out.originalDetectorShiftedPhysicalResponse = out.retained.predecessorForcing := by
  rw [canonicalNativePhysicalProjection_predecessor_eq σ out.retained.state.selection,
    out.originalDetectorShiftedResponseCoordinate_eq, out.retained.forcing_eq]
  rfl

/-- All N38 identities are derived on one original detector, with no supplied bridge. -/
structure Step123NativeOutput.OriginalDetectorAmbientResiduals
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Prop where
  physical_response_ae :
    out.originalDetectorNativeResponseL2 =ᵐ[volume]
      (Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)).indicator
        (nativeWeilResponse out.originalDetectorPhysicalSource)
  exact_recombination :
    out.originalDetectorNativeResponseL2 =
      out.originalDetectorNeutralProjectedResponse +
        out.originalDetectorPoleNormalResidual + out.originalDetectorOuterGalerkinResidual
  full_legal_projection_preserves_original_parity :
    (out.originalDetectorLegalResponseCoordinate : EuclideanSpace ℂ
      (Fin (2 * originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) + 1))) ∈
      euclideanParityBoundaryFlatSubspace σ
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
  true_pole_normal_line :
    ∃ c : ℂ, out.originalDetectorPoleNormalResidual =
      c • canonicalParityPolePhysicalNormal σ out.aperture_pos
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
  outer_orthogonal_to_legal :
    ∀ v : euclideanBoundaryFlatSubspace
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)),
      inner ℂ (canonicalLegalPhysicalIsometry out.aperture_pos _ v)
        out.originalDetectorOuterGalerkinResidual = 0
  normal_orthogonal_to_neutral :
    ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)),
      inner ℂ (canonicalNativePhysicalIsometry σ out.aperture_pos _ v)
        out.originalDetectorPoleNormalResidual = 0
  actual_operator_coordinate :
    out.originalDetectorNeutralResponseCoordinate =
      nativePoleNeutralParityCanonical σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector
  actual_predecessor_forcing :
    canonicalNativePhysicalProjection σ out.aperture_pos
      (out.retained.state.selection.cutoff - 1)
      out.originalDetectorShiftedPhysicalResponse = out.retained.predecessorForcing

theorem Step123NativeOutput.n38_forcing_ambient_residuals
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : out.OriginalDetectorAmbientResiduals where
  physical_response_ae := out.originalDetectorNativeResponseL2_ae
  exact_recombination := out.originalDetectorResponse_decomposition
  full_legal_projection_preserves_original_parity :=
    out.originalDetectorLegalResponseCoordinate_mem_parity
  true_pole_normal_line := out.originalDetectorPoleNormal_eq_smul_poleNormal
  outer_orthogonal_to_legal := out.originalDetectorOuterGalerkin_orthogonal
  normal_orthogonal_to_neutral := out.originalDetectorPoleNormal_orthogonal
  actual_operator_coordinate := out.originalDetectorNeutralResponseCoordinate_eq
  actual_predecessor_forcing := out.n38_originalDetector_predecessorForcing_eq

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorPhysicalSource_contDiff
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorPhysicalSource_compact
#print axioms Zeta23.CCM.Step123NativeOutput.physicalFiniteImage_ae_originalDetector
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorNativeResponseL2_ae
#print axioms Zeta23.CCM.canonicalLegalPhysicalProjection_inner
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorLegalResponseCoordinate_inner
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorLegalResponseCoordinate_eq_parityCompressed
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorLegalResponseCoordinate_mem_parity
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorOuterGalerkin_orthogonal
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorPoleNormal_orthogonal
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorResponse_decomposition
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorNeutralResponseCoordinate_eq
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorPoleNormal_eq_smul_poleNormal
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_predecessor_eq
#print axioms Zeta23.CCM.Step123NativeOutput.originalDetectorShiftedResponseCoordinate_eq
#print axioms Zeta23.CCM.Step123NativeOutput.n38_originalDetector_predecessorForcing_eq
#print axioms Zeta23.CCM.Step123NativeOutput.n38_forcing_ambient_residuals
