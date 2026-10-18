import Zeta23.CCM.Step123SameStateN39
import Zeta23.CCM.Step123NativeSourceSpectralEvidence
import Zeta23.CCM.Step123OriginalBoundaryEvidence
import Zeta23.CCM.Step123PhysicalImageIdentity
import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.CCM.UniversalSincPhysicalBounds
import Zeta23.CCM.OriginalDetectorPaddedPhaseScalar
import Zeta23.CCM.OriginalDetectorOddPaddingIdentity
import Zeta23.CCM.OriginalDetectorPaddedFinitePositivity
import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageC4
import Zeta23.CCM.NativeAdjointResidual
import Zeta23.CCM.NativeCompletedInputZetaLaplace
import Zeta23.ExceptionalZero.NativeActualInputZeroJets

/-!
# Typed per-field consumer of 34 Step 1-3 contract fields on ONE stored packet

`Step123NativeFieldRecord out` is a `Prop`-valued record indexed only by one
stored native packet `out : Step123NativeOutput β σ a`.  It is rho-free.  It
has one field for each of the 34 contract ids

  N01-N13, N15-N20, N22, N24-N35, N39, N40

of `OUTPUT_FIELD_CONTRACT.json`.  Each field states the contract content
instantiated on the packet's own objects: the aperture
`fixedOriginalSincTrialAperture a`, the cutoff
`originalDetectorQuarticCutoff L`, the stored original detector
`out.retained.state.detector`, the stored selection (`cutoff`, `eta`, `lam`),
`out.selectedGround`, `out.originalTrial`, `out.physicalFiniteImage`,
`out.smoothOriginal`, `out.arithmeticData`, `out.rangeData` and the phase sign
`nativeOriginalDetectorPhaseSign σ`.  Source-only fields are stated for the
fixed source objects, and the packet views of them are bound to them.

`Step123NativeFieldRecord.fromNative` fills every field from existing
theorems, with small glue proofs, and with no hypothesis beyond `out`.

What this record does NOT do:

* it does not contain the six same-state fields N14, N21, N23, N36, N37, N38
  (they are built elsewhere);
* it does not contain the generated, zero-indexed extension G01-G04;
* it is not an independent semantic review of any field;
* it proves no A-X, B-Y or C-Schur closing law, no D2 statement, and not the
  Riemann hypothesis.  The claim cap remains RH_OPEN.

Known limits of individual fields (see their docstrings):

* N39 keeps the actual original interior and proves it is not almost
  everywhere zero using the producer's retained original negative depth;
* the absence clauses of N20 ("no transferred trial moments") and N24 ("not
  both deep") hold by construction of the stored types and are not separate
  propositions;
* N22 is stated for every vector of the even neutral carrier at the stored
  (L, K); its specialization to the stored selected ground is branch data (N21)
  and is not repeated here;
* N34 quantifies over actual off-line zeros only through a universally
  quantified, hypothesis-free lower bound; the record itself stays rho-free.

The original detector and the selected ground, the original phase and the
selected parity, the legal and the neutral carriers, `lam` and `-eta`, the
depth `D` and any opposite-parity gap, forward contraction and a stable
inverse, finite iteration and range membership are kept as distinct objects.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-! ### Glue lemmas -/

/-- A core packet is the deterministic packet of its own state. -/
private theorem step123NativeCorePacket_eq_ofState
    {σ : ReversalParity} {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (P : Step123NativeCorePacket σ L Kd D hL) :
    P = Step123NativeCorePacket.ofState σ P.state := by
  cases P with
  | mk state f hf h hh =>
    subst hf
    subst hh
    rfl

/-- The coefficient vector of a native parity vector lies in its own
parity boundary-flat carrier. -/
private theorem canonicalNativeCoefficientInclusion_mem_parity
    (σ : ReversalParity) (L : ℝ) (K : ℕ) (p : nativePoleNeutralParitySpace σ L K) :
    canonicalNativeCoefficientInclusion σ L K p ∈ euclideanParityBoundaryFlatSubspace σ K := by
  cases σ
  · exact p.val.property
  · exact p.val.property

private theorem phaseSign_cases (σ : ReversalParity) :
    (σ = ReversalParity.even ∧ nativeOriginalDetectorPhaseSign σ = 1) ∨
      (σ = ReversalParity.odd ∧ nativeOriginalDetectorPhaseSign σ = -1) := by
  cases σ
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private theorem phaseSign_pm (σ : ReversalParity) :
    nativeOriginalDetectorPhaseSign σ = 1 ∨ nativeOriginalDetectorPhaseSign σ = -1 := by
  cases σ
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem phaseSign_mul_self (σ : ReversalParity) :
    (nativeOriginalDetectorPhaseSign σ : ℂ) * (nativeOriginalDetectorPhaseSign σ : ℂ) = 1 := by
  cases σ <;> norm_num [nativeOriginalDetectorPhaseSign]

/-- Both elementary-pole transform values of the original trial vanish
whenever they vanish for the fixed kernel. -/
private theorem fixedOriginalSincPhaseTrial_paperFT_eq_zero (sg a : ℝ) {z : ℂ}
    (hz : Zeta23.paperFT fixedOriginalSincKernel z = 0) :
    Zeta23.paperFT (fixedOriginalSincPhaseTrial sg a) z = 0 := by
  have hk : ContDiff ℝ 2 fixedOriginalSincKernel :=
    (contDiff_originalSincTest UniversalSinc.fixedScale_pos).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hkc : HasCompactSupport fixedOriginalSincKernel :=
    hasCompactSupport_originalSincTest UniversalSinc.fixedScale_pos
  unfold fixedOriginalSincPhaseTrial
  rw [paperFT_translateRight, paperFT_twoTranslateCombination hk hkc,
    paperFT_translateRight, hz]
  simp

private theorem step123_aperture_two_le {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : 2 ≤ fixedOriginalSincTrialAperture a := by
  linarith [out.aperture_gt_four]

private theorem step123_separation_gt_scale {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : UniversalSinc.fixedScale < a := by
  have h4 := out.aperture_gt_four
  unfold fixedOriginalSincTrialAperture fixedOriginalSincLobeCenter at h4
  have hs : UniversalSinc.fixedScale = 1 / 4096 := rfl
  rw [hs] at h4 ⊢
  linarith

/-- The stored detector's coefficient vector is the literal padded unit vector. -/
private theorem step123_detector_coefficients {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector =
      originalDetectorPaddedFinitePhaseUnitVector (nativeOriginalDetectorPhaseSign σ)
        (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter out.aperture_pos := by
  rw [out.detector_source_eq]
  exact originalDetectorPaddedNativeUnit_eq_unitCoefficients σ _ _

/-- Global hard C4 of the physical synthesis of the normalized padded phase
vector: its endpoint moments of order below six vanish and the finite Fourier
function is L-periodic, so the zero extension is C4. -/
private theorem paddedUnit_physical_contDiff_four (sg c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ContDiff ℝ 4 (finitePhysicalSynthesis L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePhaseUnitVector sg L c (by linarith))) := by
  have hLp : 0 < L := by linarith
  let Kd := originalDetectorQuarticCutoff L
  let u := (EuclideanSpace.equiv (Fin (2 * Kd + 1)) ℂ)
    (originalDetectorPaddedFinitePhaseUnitVector sg L c hLp)
  have h0 : ∀ r : ℕ, r < 6 → iteratedDeriv r (localizedFiniteFunction L Kd u) 0 = 0 := by
    intro r hr
    rw [padded_localizedFiniteFunction_iteratedDeriv_zero_eq_moment]
    rw [originalDetectorPaddedFinitePhaseUnitVector_moment_zero_lt_six sg c hL hr, mul_zero]
  have hper : (fun z => localizedFiniteFunction L Kd u (z + L)) =
      localizedFiniteFunction L Kd u := by
    funext z
    exact localizedFiniteFunction_add_period L Kd u z hLp.ne'
  change ContDiff ℝ 4 (localizedFiniteVector L Kd u)
  rw [localizedFiniteVector_eq_indicator]
  apply padded_contDiff_nat_indicator_Icc_of_iteratedDeriv_endpoint_zero hLp 4
  · unfold localizedFiniteFunction
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_localizedMode L _).of_le le_top)
  · intro r hr
    refine ⟨h0 r (by omega), ?_⟩
    have hshift := congrFun (iteratedDeriv_comp_add_const r (localizedFiniteFunction L Kd u) L) 0
    rw [hper, zero_add] at hshift
    rw [← hshift]
    exact h0 r (by omega)

/-! ### The record -/

/-- Typed per-field consumer of the 34 contract fields N01-N13, N15-N20, N22,
N24-N35, N39, N40 on ONE stored native packet.  It is rho-free and is indexed
only by the stored packet. -/
structure Step123NativeFieldRecord {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Prop where
  /-- N01 `source.scale`: s0 = 1/4096, and every source view uses that scale. -/
  n01_source_scale :
    UniversalSinc.fixedScale = 1 / 4096 ∧ 0 < UniversalSinc.fixedScale ∧
    nativeOriginalSource = universalSincSecondSource UniversalSinc.fixedScale ∧
    fixedOriginalSincKernel = universalSincKernel UniversalSinc.fixedScale ∧
    fixedOriginalSincLobeCenter = 1 + UniversalSinc.fixedScale
  /-- N02 `source.q_k_j`: q = q_{s0}, k = P q, j = P² q as actual physical
  functions (k and j are real-valued, and the native source is j). -/
  n02_source_q_k_j :
    universalSincSource UniversalSinc.fixedScale =
        UniversalSinc.originalDensityCandidate UniversalSinc.fixedScale ∧
    (∀ (f : ℝ → ℂ) (x : ℝ),
        universalSincDifferential f x = deriv (deriv f) x - (1 / 4 : ℂ) * f x) ∧
    universalSincKernel UniversalSinc.fixedScale =
        universalSincDifferential
          (fun x => (universalSincSource UniversalSinc.fixedScale x : ℂ)) ∧
    universalSincSecondKernel UniversalSinc.fixedScale =
        universalSincDifferential (universalSincKernel UniversalSinc.fixedScale) ∧
    (∀ x : ℝ, universalSincKernel UniversalSinc.fixedScale x =
        ((deriv (deriv (universalSincSource UniversalSinc.fixedScale)) x -
          (1 / 4 : ℝ) * universalSincSource UniversalSinc.fixedScale x : ℝ) : ℂ)) ∧
    (∀ x : ℝ, universalSincSecondKernel UniversalSinc.fixedScale x =
        (nativeOriginalSource x : ℂ)) ∧
    nativeOriginalSource = fun x => (universalSincSecondKernel UniversalSinc.fixedScale x).re
  /-- N03 `source.properties`: support, realness, evenness, positivity of q,
  mass one, smoothness, exact transforms of q, k and j. -/
  n03_source_properties :
    ((∀ x : ℝ, 0 ≤ universalSincSource UniversalSinc.fixedScale x) ∧
      tsupport (universalSincSource UniversalSinc.fixedScale) ⊆
        Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale ∧
      Function.Even (universalSincSource UniversalSinc.fixedScale) ∧
      (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 ∧
      Zeta23.paperFT
        (fun x : ℝ => (universalSincSource UniversalSinc.fixedScale x : ℂ)) =
        UniversalSinc.product UniversalSinc.fixedScale) ∧
    ContDiff ℝ (⊤ : ℕ∞) (universalSincSource UniversalSinc.fixedScale) ∧
    ContDiff ℝ (⊤ : ℕ∞) (universalSincKernel UniversalSinc.fixedScale) ∧
    ContDiff ℝ (⊤ : ℕ∞) (universalSincSecondKernel UniversalSinc.fixedScale) ∧
    tsupport (universalSincKernel UniversalSinc.fixedScale) ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale ∧
    tsupport (universalSincSecondKernel UniversalSinc.fixedScale) ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale ∧
    (∀ x : ℝ, (universalSincKernel UniversalSinc.fixedScale x).im = 0 ∧
      (universalSincSecondKernel UniversalSinc.fixedScale x).im = 0) ∧
    Function.Even (universalSincKernel UniversalSinc.fixedScale) ∧
    Function.Even (universalSincSecondKernel UniversalSinc.fixedScale) ∧
    (∀ z : ℂ, Zeta23.paperFT (universalSincKernel UniversalSinc.fixedScale) z =
      -(z ^ 2 + 1 / 4) * UniversalSinc.product UniversalSinc.fixedScale z) ∧
    (∀ z : ℂ, Zeta23.paperFT (universalSincSecondKernel UniversalSinc.fixedScale) z =
      (z ^ 2 + 1 / 4) ^ 2 * UniversalSinc.product UniversalSinc.fixedScale z) ∧
    (∫ x : ℝ, universalSincSecondKernel UniversalSinc.fixedScale x) = (1 / 16 : ℂ) ∧
    (∫ x : ℝ, nativeOriginalSource x) = (1 / 16 : ℝ)
  /-- N04 `source.bounds`: source-only Gevrey constants, product decay,
  exact scaling, and the three-term kernel L2 identity. -/
  n04_source_bounds :
    (∃ C H : ℝ, 0 < C ∧ 0 < H ∧ ∀ (r : ℕ) (x : ℝ),
      ‖iteratedDeriv r (universalSincSource UniversalSinc.fixedScale) x‖ ≤
        C * H ^ r * (Nat.factorial r : ℝ) ^ 2) ∧
    (∀ x : ℝ, ‖UniversalSinc.product UniversalSinc.fixedScale (x : ℂ)‖ ≤
      2 * Real.exp (-(Real.log 2 / 2) * Real.sqrt (UniversalSinc.fixedScale * |x|))) ∧
    (∀ x : ℝ, universalSincSource UniversalSinc.fixedScale x =
      UniversalSinc.fixedScale⁻¹ *
        universalSincSource 1 (x / UniversalSinc.fixedScale)) ∧
    (∫ x : ℝ, ‖universalSincKernel UniversalSinc.fixedScale x‖ ^ 2) =
      (UniversalSinc.fixedScale ^ 5)⁻¹ *
          (∫ x : ℝ, (deriv (deriv (universalSincSource 1)) x) ^ 2) +
        (1 / 2 : ℝ) * (UniversalSinc.fixedScale ^ 3)⁻¹ *
          (∫ x : ℝ, (deriv (universalSincSource 1) x) ^ 2) +
        (1 / 16 : ℝ) * UniversalSinc.fixedScale⁻¹ *
          (∫ x : ℝ, (universalSincSource 1 x) ^ 2)
  /-- N05 `trial.index`: a; c = 1+s0; L = 2a+2c; the original sigma sign. -/
  n05_trial_index :
    fixedOriginalSincLobeCenter = 1 + UniversalSinc.fixedScale ∧
    fixedOriginalSincTrialAperture a = 2 * a + 2 * fixedOriginalSincLobeCenter ∧
    ((σ = ReversalParity.even ∧ nativeOriginalDetectorPhaseSign σ = 1) ∨
      (σ = ReversalParity.odd ∧ nativeOriginalDetectorPhaseSign σ = -1)) ∧
    0 < fixedOriginalSincTrialAperture a ∧ 4 < fixedOriginalSincTrialAperture a
  /-- N06 `trial.original`: the stored trial is the literal
  `fixedOriginalSincPhaseTrial (sign σ) a`, in unchanged physical coordinates. -/
  n06_trial_original :
    out.originalTrial = fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a ∧
    fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a =
      translateRight (twoTranslateCombination fixedOriginalSincKernel (2 * a)
        (fixedOriginalSincTrialNormalization : ℂ)
        ((nativeOriginalDetectorPhaseSign σ * fixedOriginalSincTrialNormalization : ℝ) : ℂ))
        fixedOriginalSincLobeCenter ∧
    fixedOriginalSincTrialNormalization =
      (Real.sqrt (2 * fixedOriginalSincKernelL2Mass))⁻¹ ∧
    (∀ x : ℝ, out.originalTrial x =
      (fixedOriginalSincTrialNormalization : ℂ) *
        (fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
          (nativeOriginalDetectorPhaseSign σ : ℂ) *
          fixedOriginalSincKernel
            (fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter))) ∧
    ContDiff ℝ 2 out.originalTrial ∧ HasCompactSupport out.originalTrial
  /-- N07 `trial.original_properties`: disjoint collars (a > s0), mass one,
  support in [1, L-1], both elementary poles, phase parity. -/
  n07_trial_original_properties :
    UniversalSinc.fixedScale < a ∧
    (∀ x : ℝ, fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) = 0 ∨
      fixedOriginalSincKernel
        (fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter) = 0) ∧
    (∫ x : ℝ, ‖out.originalTrial x‖ ^ 2) = 1 ∧
    tsupport out.originalTrial ⊆ Icc 1 (fixedOriginalSincTrialAperture a - 1) ∧
    (∫ x : ℝ, nativePoleExponential (1 / 2) x * out.originalTrial x) = 0 ∧
    (∫ x : ℝ, nativePoleExponential (-1 / 2) x * out.originalTrial x) = 0 ∧
    (∀ x : ℝ, out.originalTrial (fixedOriginalSincTrialAperture a - x) =
      (nativeOriginalDetectorPhaseSign σ : ℂ) * out.originalTrial x)
  /-- N08 `image.raw`: literal positive DC padding, the sin^8 window image,
  the P image, Kd = ceil L^4 and N = Kd - 4, at the packet's aperture. -/
  n08_image_raw :
    let L := fixedOriginalSincTrialAperture a
    let c := fixedOriginalSincLobeCenter
    let s := UniversalSinc.fixedScale
    originalDetectorQuarticCutoff L = Nat.ceil (L ^ 4) ∧
    originalDetectorRawCutoff L = originalDetectorQuarticCutoff L - 4 ∧
    0 < originalDetectorPositivePadding s L ∧
    (∀ n : ℤ, originalDetectorPaddedRawFourierCoeff s L c out.aperture_pos n =
      originalDetectorDividedLobeFourierCoeff s L c out.aperture_pos n +
        if n = 0 then (originalDetectorPositivePadding s L : ℂ) else 0) ∧
    (∀ x : ℝ, originalDetectorPaddedFiniteWindow L x =
      Complex.sin ((Real.pi : ℂ) * x / (L : ℂ)) ^ 8) ∧
    (∀ x : ℝ, originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos x =
      originalDetectorPaddedFiniteWindow L x *
        originalDetectorPaddedRawFourierPartialJet s L c out.aperture_pos 0 x) ∧
    (∀ n ∈ (originalDetectorPaddedFiniteWindowImageFinsupp s L c out.aperture_pos).support,
      n.natAbs ≤ originalDetectorQuarticCutoff L) ∧
    (∀ x : ℝ, localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFiniteWindowImageCoefficients s L c out.aperture_pos) x =
        originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos x) ∧
    localizedFiniteFunction L (originalDetectorQuarticCutoff L)
        (originalDetectorPaddedFinitePoleImageCoefficients s L c out.aperture_pos) =
      poleKilled (originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos) ∧
    originalDetectorPaddedFinitePhaseLeft L c out.aperture_pos =
      WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients s L c out.aperture_pos)
  /-- N09 `image.positive_primitive`: nonnegative original and even
  primitives; the positive pad cancels exactly and only in the odd phase. -/
  n09_image_positive_primitive :
    let L := fixedOriginalSincTrialAperture a
    let c := fixedOriginalSincLobeCenter
    let s := UniversalSinc.fixedScale
    (∀ x ∈ Icc (0 : ℝ) L,
      0 ≤ (originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos x).re) ∧
    (∀ x ∈ Icc (0 : ℝ) L,
      0 ≤ (originalDetectorPaddedFinitePhasePrimitive 1 s L c out.aperture_pos x).re) ∧
    (∀ x : ℝ, conj (originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos x) =
      originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos x) ∧
    (∀ x : ℝ, originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos x =
      originalDetectorFiniteWindowImage s L c out.aperture_pos x +
        (originalDetectorPositivePadding s L : ℂ) * originalDetectorFiniteWindow L x) ∧
    (∀ x : ℝ, originalDetectorPaddedFinitePhasePrimitive (-1) s L c out.aperture_pos x =
      originalDetectorFiniteWindowImage s L c out.aperture_pos x -
        originalDetectorFiniteWindowImage s L c out.aperture_pos (L - x)) ∧
    originalDetectorPaddedFinitePhaseVector (-1) L c out.aperture_pos =
      originalDetectorFinitePhaseVector (-1) L c out.aperture_pos ∧
    originalDetectorPaddedFinitePhaseUnitVector (-1) L c out.aperture_pos =
      originalDetectorFinitePhaseUnitVector (-1) L c out.aperture_pos
  /-- N10 `image.endpoint_jets`: primitive derivatives 0..7 vanish at both
  ends; P-image derivatives 0..5 vanish; global hard C4 of the P image and of
  the stored detector's physical synthesis. -/
  n10_image_endpoint_jets :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let c := fixedOriginalSincLobeCenter
    let s := UniversalSinc.fixedScale
    (∀ r : ℕ, r < 8 →
      iteratedDeriv r (originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos) 0 = 0 ∧
      iteratedDeriv r (originalDetectorPaddedFiniteWindowImage s L c out.aperture_pos) L = 0) ∧
    (∀ r : ℕ, r < 6 →
      iteratedDeriv r (localizedFiniteFunction L Kd
        (originalDetectorPaddedFinitePoleImageCoefficients s L c out.aperture_pos)) 0 = 0 ∧
      iteratedDeriv r (localizedFiniteFunction L Kd
        (originalDetectorPaddedFinitePoleImageCoefficients s L c out.aperture_pos)) L = 0) ∧
    ContDiff ℝ 4 (localizedFiniteVector L Kd
      (originalDetectorPaddedFinitePoleImageCoefficients s L c out.aperture_pos)) ∧
    (∀ r : ℕ, r < 6 → centeredMoment Kd r
      ((EuclideanSpace.equiv (Fin (2 * Kd + 1)) ℂ)
        (canonicalNativeCoefficientInclusion σ L Kd out.retained.state.detector)) = 0) ∧
    ContDiff ℝ 4 (finitePhysicalSynthesis L Kd
      (canonicalNativeCoefficientInclusion σ L Kd out.retained.state.detector))
  /-- N11 `image.native_p`: the stored detector is
  `nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter _`, whose
  coefficients are the normalized literal two-lobe padded phase vector. -/
  n11_image_native_p :
    let L := fixedOriginalSincTrialAperture a
    let c := fixedOriginalSincLobeCenter
    let sg := nativeOriginalDetectorPhaseSign σ
    out.retained.state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [out.aperture_gt_four]) ∧
    canonicalNativeCoefficientInclusion σ L (originalDetectorQuarticCutoff L)
        out.retained.state.detector =
      originalDetectorPaddedFinitePhaseUnitVector sg L c out.aperture_pos ∧
    originalDetectorPaddedFinitePhaseUnitVector sg L c out.aperture_pos =
      ((‖originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos‖⁻¹ : ℝ) : ℂ) •
        originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos ∧
    originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos =
      originalDetectorPaddedFinitePhaseLeft L c out.aperture_pos +
        (sg : ℂ) • originalDetectorPaddedFinitePhaseRight L c out.aperture_pos
  /-- N12 `image.unit_and_poles`: norm one; both actual profile functionals
  vanish; legal and own-parity neutral membership. -/
  n12_image_unit_and_poles :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    ‖p‖ = 1 ∧
    canonicalPoleEvenFunctional L Kd (nativePoleNeutralParityAmbient σ L Kd p) = 0 ∧
    canonicalPoleOddFunctional L Kd (nativePoleNeutralParityAmbient σ L Kd p) = 0 ∧
    nativePoleNeutralParityAmbient σ L Kd p ∈ euclideanBoundaryFlatSubspace Kd ∧
    canonicalNativeCoefficientInclusion σ L Kd p = nativePoleNeutralParityAmbient σ L Kd p ∧
    canonicalNativeCoefficientInclusion σ L Kd p ∈ euclideanParityBoundaryFlatSubspace σ Kd
  /-- N13 `image.physical_equality`: physical synthesis of N11 equals the
  actual true-normalized physical function; the L2 image is that function. -/
  n13_image_physical_equality :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    finitePhysicalSynthesis L Kd
        (canonicalNativeCoefficientInclusion σ L Kd out.retained.state.detector) =
      originalDetectorPaddedFinitePhysicalUnit (nativeOriginalDetectorPhaseSign σ) a
        out.aperture_pos ∧
    out.physicalFiniteImage =
      canonicalNativePhysicalIsometry σ out.aperture_pos Kd out.retained.state.detector ∧
    (out.physicalFiniteImage : ℝ → ℂ) =ᵐ[volume]
      originalDetectorPaddedFinitePhysicalUnit (nativeOriginalDetectorPhaseSign σ) a
        out.aperture_pos ∧
    ‖out.physicalFiniteImage‖ = 1
  /-- N15 `phase.full_matrices`: actual left/right vectors, full complex Gram
  and full 2x2 native energy, with the exact generalized Rayleigh identity. -/
  n15_phase_full_matrices :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let c := fixedOriginalSincLobeCenter
    let l := originalDetectorPaddedFinitePhaseLeft L c out.aperture_pos
    let r := originalDetectorPaddedFinitePhaseRight L c out.aperture_pos
    let A := (canonicalSourceMatrix L Kd).toEuclideanLin
    r = WithLp.toLp 2 (reverseCoefficients Kd
      (originalDetectorPaddedFinitePoleImageCoefficients UniversalSinc.fixedScale L c
        out.aperture_pos)) ∧
    originalDetectorPaddedFinitePhaseGram L c out.aperture_pos =
      !![inner ℂ l l, inner ℂ l r; inner ℂ r l, inner ℂ r r] ∧
    originalDetectorPaddedFinitePhaseNativeEnergy L c out.aperture_pos =
      !![inner ℂ (A l) l, inner ℂ (A l) r; inner ℂ (A r) l, inner ℂ (A r) r] ∧
    (∀ z : Fin 2 → ℂ,
      (inner ℂ (A (originalDetectorPaddedFinitePhasePlaneVector L c out.aperture_pos z))
        (originalDetectorPaddedFinitePhasePlaneVector L c out.aperture_pos z)).re /
        ‖originalDetectorPaddedFinitePhasePlaneVector L c out.aperture_pos z‖ ^ 2 =
      (originalDetectorPaddedFinitePhaseMatrixValue
        (originalDetectorPaddedFinitePhaseNativeEnergy L c out.aperture_pos) z).re /
      (originalDetectorPaddedFinitePhaseMatrixValue
        (originalDetectorPaddedFinitePhaseGram L c out.aperture_pos) z).re) ∧
    originalDetectorPaddedFinitePhaseVector (nativeOriginalDetectorPhaseSign σ) L c
        out.aperture_pos =
      originalDetectorPaddedFinitePhasePlaneVector L c out.aperture_pos
        ![1, (nativeOriginalDetectorPhaseSign σ : ℂ)]
  /-- N16 `phase.scalar_contract`: real circulancy, positive nu ± omega, and
  the exact scalar quotient, also for the stored detector's native energy. -/
  n16_phase_scalar_contract :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let c := fixedOriginalSincLobeCenter
    let sg := nativeOriginalDetectorPhaseSign σ
    let ν := originalDetectorPaddedPhaseNu L c out.aperture_pos
    let ω := originalDetectorPaddedPhaseOmega L c out.aperture_pos
    let d := originalDetectorPaddedPhaseD L c out.aperture_pos
    let e := originalDetectorPaddedPhaseC L c out.aperture_pos
    originalDetectorPaddedFinitePhaseGram L c out.aperture_pos =
      !![(ν : ℂ), (ω : ℂ); (ω : ℂ), (ν : ℂ)] ∧
    originalDetectorPaddedFinitePhaseNativeEnergy L c out.aperture_pos =
      !![(d : ℂ), (e : ℂ); (e : ℂ), (d : ℂ)] ∧
    0 < ν + ω ∧ 0 < ν - ω ∧
    ‖originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos‖ ^ 2 = 2 * (ν + sg * ω) ∧
    (inner ℂ ((canonicalSourceMatrix L Kd).toEuclideanLin
      (originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos))
      (originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos)).re =
        2 * (d + sg * e) ∧
    (inner ℂ ((canonicalSourceMatrix L Kd).toEuclideanLin
      (originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos))
      (originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos)).re /
        ‖originalDetectorPaddedFinitePhaseVector sg L c out.aperture_pos‖ ^ 2 =
      (d + sg * e) / (ν + sg * ω) ∧
    (inner ℂ (nativePoleNeutralParityCanonical σ L Kd out.retained.state.detector)
      out.retained.state.detector).re = (d + sg * e) / (ν + sg * ω)
  /-- N17 `retained.state`: ONE `DetectorRetainedSchurState` on N11, with its
  equality binding; every retained view is a projection of it. -/
  n17_retained_state :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    out.structuralData = out.retained ∧
    out.retained = Step123NativeCorePacket.ofState σ out.retained.state ∧
    out.retained.state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [out.aperture_gt_four]) ∧
    (inner ℂ (nativePoleNeutralParityCanonical σ L Kd out.retained.state.detector)
      out.retained.state.detector).re ≤ -Real.exp (β * L) ∧
    0 < Real.exp (β * L) ∧
    out.retained.predecessorForcing =
      originalDetectorNativeForcing σ out.retained.state.selection
        out.retained.state.detector ∧
    out.retained.nativeHistory = originalDetectorRetainedExteriorHistory σ out.retained.state ∧
    out.selectedGround = out.retained.state.selectedGround
  /-- N18 `retained.eta_lambda`: distinct eta and actual lambda; exact gap g
  and the predecessor inequalities. -/
  n18_retained_eta_lambda :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let D := Real.exp (β * L)
    let sel := out.retained.state.selection
    let g := nativeDeepThresholdGap D Kd
    sel.lam = poleNeutralGlobalRayleighBottom L sel.cutoff out.aperture_pos
      sel.cutoff_nonempty ∧
    3 ≤ sel.cutoff ∧ sel.cutoff ≤ Kd ∧
    D / 3 < sel.eta ∧ sel.eta < D / 2 ∧
    g = D / (12 * ((Kd - 1 : ℕ) : ℝ)) ∧ 0 < g ∧
    sel.lam ≤ -sel.eta - g ∧
    sel.lam ≠ -sel.eta ∧
    (∀ J : ℕ, (hJ : 3 ≤ J) → J < sel.cutoff →
      -sel.eta + g ≤ poleNeutralGlobalRayleighBottom L J out.aperture_pos hJ) ∧
    (∀ hprev : 3 ≤ sel.cutoff - 1,
      (-sel.eta + g ≤ poleNeutralEvenRayleighBottom L (sel.cutoff - 1) out.aperture_pos hprev) ∧
      (-sel.eta + g ≤ poleNeutralOddRayleighBottom L (sel.cutoff - 1) out.aperture_pos hprev)) ∧
    (sel.cutoff = 3 →
      Module.finrank ℂ (poleNeutralEvenSubspace L 2) = 0 ∧
        Module.finrank ℂ (poleNeutralOddSubspace L 2) = 0)
  /-- N19 `retained.inverses`: four actual inverses, 6(Kd-1)/D at lambda and
  12(Kd-1)/D at -eta, and the zero-space case. -/
  n19_retained_inverses :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let D := Real.exp (β * L)
    let sel := out.retained.state.selection
    let r := out.retained.state.inverses
    (∀ u, r.evenGround u = poleNeutralEvenShiftedCanonical L (sel.cutoff - 1) sel.lam u) ∧
    (∀ w, r.oddGround w = poleNeutralOddShiftedCanonical L (sel.cutoff - 1) sel.lam w) ∧
    (∀ u, r.evenDetector u = poleNeutralEvenShiftedCanonical L (sel.cutoff - 1) (-sel.eta) u) ∧
    (∀ w, r.oddDetector w = poleNeutralOddShiftedCanonical L (sel.cutoff - 1) (-sel.eta) w) ∧
    ‖r.evenGround.symm.toLinearMap.toContinuousLinearMap‖ ≤ 6 * ((Kd - 1 : ℕ) : ℝ) / D ∧
    ‖r.oddGround.symm.toLinearMap.toContinuousLinearMap‖ ≤ 6 * ((Kd - 1 : ℕ) : ℝ) / D ∧
    ‖r.evenDetector.symm.toLinearMap.toContinuousLinearMap‖ ≤ 12 * ((Kd - 1 : ℕ) : ℝ) / D ∧
    ‖r.oddDetector.symm.toLinearMap.toContinuousLinearMap‖ ≤ 12 * ((Kd - 1 : ℕ) : ℝ) / D ∧
    (∀ v, nativeDetectorPredecessorEquiv σ r v =
      nativePoleNeutralParityShifted σ L (sel.cutoff - 1) (-sel.eta) v) ∧
    (∀ v, nativeSelectedGroundPredecessorEquiv out.retained.state.selectedParity r v =
      nativePoleNeutralParityShifted out.retained.state.selectedParity L (sel.cutoff - 1)
        sel.lam v) ∧
    ‖(nativeDetectorPredecessorEquiv σ r).symm.toLinearMap.toContinuousLinearMap‖ ≤
      12 * ((Kd - 1 : ℕ) : ℝ) / D ∧
    ‖(nativeSelectedGroundPredecessorEquiv out.retained.state.selectedParity
        r).symm.toLinearMap.toContinuousLinearMap‖ ≤ 6 * ((Kd - 1 : ℕ) : ℝ) / D ∧
    (sel.cutoff = 3 →
      ‖r.evenGround.symm.toLinearMap.toContinuousLinearMap‖ = 0 ∧
      ‖r.oddGround.symm.toLinearMap.toContinuousLinearMap‖ = 0 ∧
      ‖r.evenDetector.symm.toLinearMap.toContinuousLinearMap‖ = 0 ∧
      ‖r.oddDetector.symm.toLinearMap.toContinuousLinearMap‖ = 0)
  /-- N20 `retained.ground`: selected parity, actual unit eigenvector at the
  actual lambda (the global bottom at the selected cutoff). -/
  n20_retained_ground :
    let L := fixedOriginalSincTrialAperture a
    let sel := out.retained.state.selection
    out.selectedGround = out.retained.state.selectedGround ∧
    ‖out.selectedGround‖ = 1 ∧
    nativePoleNeutralParityCanonical out.retained.state.selectedParity L sel.cutoff
        out.selectedGround = (sel.lam : ℂ) • out.selectedGround ∧
    sel.lam = poleNeutralGlobalRayleighBottom L sel.cutoff out.aperture_pos
      sel.cutoff_nonempty
  /-- N22 `retained.source_correction`: the actual normal coefficient alpha,
  the quadratic coefficient b, S0 = S - b alpha, Q_odd D v_even = -b g0, and
  the rank-one identity B0 D0 - D0 A0 = g0 S0 at the stored (L, K). -/
  n22_retained_source_correction :
    let L := fixedOriginalSincTrialAperture a
    let K := out.retained.state.selection.cutoff
    (∀ u : poleNeutralEvenSubspace L K,
      poleNeutralEvenOutputCoefficient L K u =
        inner ℂ (canonicalPoleEvenLegalNormal L K) (evenCompressedCanonical L K u.val) /
          inner ℂ (canonicalPoleEvenLegalNormal L K) (canonicalPoleEvenLegalNormal L K)) ∧
    canonicalPoleQuadraticNormalCoefficient L K =
      inner ℂ (centeredQuadraticNormal K) (canonicalPoleEvenProfileVector L K) /
        inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) ∧
    (∀ u : poleNeutralEvenSubspace L K,
      poleNeutralEvenOutputResidual L K u =
        poleNeutralEvenOutputCoefficient L K u • canonicalPoleEvenLegalNormal L K) ∧
    (∀ u : poleNeutralEvenSubspace L K,
      poleNeutralCorrectedCubicSource L K u =
        cubicDefectFunctional L K u.val -
          canonicalPoleQuadraticNormalCoefficient L K * poleNeutralEvenOutputCoefficient L K u) ∧
    (∀ u : poleNeutralEvenSubspace L K,
      poleNeutralCorrectedCubicFunctional L K u = poleNeutralCorrectedCubicSource L K u) ∧
    (Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
        (euclideanEvenToOddIndexLinearMap K (canonicalPoleEvenLegalNormal L K)) =
      -canonicalPoleQuadraticNormalCoefficient L K • poleNeutralCubicCompressionVector L K ∧
    RankOneIntertwining (E := poleNeutralEvenSubspace L K) (O := poleNeutralOddSubspace L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralOddCompressedCanonical L K)
      (poleNeutralIndexEquiv out.aperture_pos K
        (by have := out.retained.state.selection.cutoff_nonempty; omega))
      (poleNeutralCubicCompressionVector L K) (poleNeutralCorrectedCubicFunctional L K)
  /-- N24 `retained.admissible`: rho-free `AdmissibleDetectorSelector β L eta K`;
  both phases unit and nonzero; only the stored phase carries depth. -/
  n24_retained_admissible :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let c := fixedOriginalSincLobeCenter
    AdmissibleDetectorSelector β L out.retained.state.selection.eta
      out.retained.state.selection.cutoff ∧
    originalDetectorPaddedFinitePhaseVector 1 L c out.aperture_pos ≠ 0 ∧
    originalDetectorPaddedFinitePhaseVector (-1) L c out.aperture_pos ≠ 0 ∧
    ‖originalDetectorPaddedFinitePhaseUnitVector 1 L c out.aperture_pos‖ = 1 ∧
    ‖originalDetectorPaddedFinitePhaseUnitVector (-1) L c out.aperture_pos‖ = 1 ∧
    (inner ℂ (nativePoleNeutralParityCanonical σ L Kd out.retained.state.detector)
      out.retained.state.detector).re ≤ -Real.exp (β * L)
  /-- N25 `schur.detector`: full Kd-K+1 detector complement, shift -eta,
  completed square, loss > D/2. -/
  n25_schur_detector :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let D := Real.exp (β * L)
    let state := out.retained.state
    let J := nativeDetectorPredecessorEmbedding σ state.selection
    let T := nativePoleNeutralParityShifted σ L Kd (-state.selection.eta)
    let P := nativeDetectorPredecessorEquiv σ state.inverses
    let x := J.toLinearMap.adjoint state.detector
    let y := isometricDetectorComplementCoordinate J state.detector
    let z := x + isometricDetectorResponse J T P y
    Module.finrank ℂ (nativeDetectorComplement σ state.selection) =
      Kd - state.selection.cutoff + 1 ∧
    nativeDetectorSchurOperator σ state.inverses = isometricDetectorSchurOperator J T P ∧
    inner ℂ (T state.detector) state.detector =
      inner ℂ (P z) z + inner ℂ (nativeDetectorSchurOperator σ state.inverses y) y ∧
    y ≠ 0 ∧
    (inner ℂ (nativeDetectorSchurOperator σ state.inverses y) y).re ≤
      -(D - state.selection.eta) ∧
    (inner ℂ (nativeDetectorSchurOperator σ state.inverses y) y).re < -D / 2
  /-- N26 `schur.ground`: the one-shell selected-ground equation at lambda. -/
  n26_schur_ground :
    let L := fixedOriginalSincTrialAperture a
    let state := out.retained.state
    let gamma := state.selectedParity
    let J := nativeSelectedGroundPredecessorEmbedding gamma state.selection
    let T := nativePoleNeutralParityShifted gamma L state.selection.cutoff state.selection.lam
    let P := nativeSelectedGroundPredecessorEquiv gamma state.inverses
    let y := isometricDetectorComplementCoordinate J state.selectedGround
    let response := isometricDetectorResponse J T P y
    inner ℂ (nativePoleNeutralParityCanonical gamma L state.selection.cutoff
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff))
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff) -
      (state.selection.lam : ℂ) * inner ℂ
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff)
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff) =
      inner ℂ (P response) response
  /-- N27 `residual.neutral`: own-parity neutral residual of the stored
  detector at its own Rayleigh value, with exact variance. -/
  n27_residual_neutral :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    canonicalPoleNeutralTrialResidual σ L Kd p =
      nativePoleNeutralParityCanonical σ L Kd p -
        (canonicalPoleNeutralTrialRayleigh σ L Kd p : ℂ) • p ∧
    canonicalPoleNeutralTrialRayleigh σ L Kd p =
      (inner ℂ p (nativePoleNeutralParityCanonical σ L Kd p)).re ∧
    inner ℂ p (canonicalPoleNeutralTrialResidual σ L Kd p) = 0 ∧
    ‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (inner ℂ p (nativePoleNeutralParityCanonical σ L Kd
        (nativePoleNeutralParityCanonical σ L Kd p))).re -
      canonicalPoleNeutralTrialRayleigh σ L Kd p ^ 2
  /-- N28 `residual.gram`: every actual neutral native channel and the full
  complex off-diagonal Gram. -/
  n28_residual_gram :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    (∑ i, canonicalPoleNeutralTrialChannel σ L Kd i) = nativePoleNeutralParityCanonical σ L Kd ∧
    canonicalPoleNeutralTrialResidual σ L Kd p =
      ∑ i, nativeTrialResidual (canonicalPoleNeutralTrialChannel σ L Kd i) p ∧
    (∀ i j, canonicalPoleNeutralTrialChannelGram σ L Kd p i j =
      nativeTrialChannelGram (canonicalPoleNeutralTrialChannel σ L Kd) p i j) ∧
    ‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (∑ i, ∑ j, canonicalPoleNeutralTrialChannelGram σ L Kd p i j).re
  /-- N29 `native.X_U`: literal X = Π * j and U = (t N) * j, N * X = U, and the
  actual von Mangoldt coefficients; the packet's arithmetic view is (X, U). -/
  n29_native_X_U :
    out.arithmeticData = (nativeOriginalPrimeField, nativeOriginalIntegerDrive) ∧
    nativeOriginalPrimeField = nativePrimeField nativeOriginalSource ∧
    nativeOriginalIntegerDrive = nativeIntegerDriveField nativeOriginalSource ∧
    (∀ t : ℝ, nativePrimeField nativeOriginalSource t =
      ∑' n : ℕ, nativePrimeCoefficient n * nativeOriginalSource (t - Real.log n)) ∧
    (∀ t : ℝ, nativeIntegerDriveField nativeOriginalSource t =
      ∑' n : ℕ, nativeIntegerDriveCoefficient n * nativeOriginalSource (t - Real.log n)) ∧
    (∀ n : ℕ, nativePrimeCoefficient n = ArithmeticFunction.vonMangoldt n / Real.sqrt n) ∧
    (∀ n : ℕ, nativeIntegerDriveCoefficient n = Real.log n / Real.sqrt n) ∧
    (∀ n : ℕ, nativeIntegerCoefficient n = 1 / Real.sqrt n) ∧
    (∀ t : ℝ, nativeIntegerTranslateAction nativeOriginalPrimeField t =
      nativeOriginalIntegerDrive t) ∧
    (∀ n : ℕ, ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d = Real.log n) ∧
    (∀ f : ArithmeticFunction ℝ, (∀ n : ℕ, ∑ d ∈ n.divisors, f d = Real.log n) →
      f = ArithmeticFunction.vonMangoldt) ∧
    (∀ t : ℝ, nativeComplexPrimeField (fun u => ∫ x : ℝ,
        universalSincKernel UniversalSinc.fixedScale x *
          universalSincKernel UniversalSinc.fixedScale (u - x)) t =
      ∫ x : ℝ, UniversalSinc.originalDensityComplex UniversalSinc.fixedScale x *
        (nativeOriginalPrimeField (t - x) : ℂ))
  /-- N30 `native.input_decay`: the existing exponential-polynomial U and
  stable Y facts, plus the all-fixed-exponential-rate U bound from
  finite-order summation.  No double-exponential (A03) claim. -/
  n30_native_input_decay :
    out.arithmeticData.2 = nativeOriginalIntegerDrive ∧
    out.rangeData.1 = nativeCompletedInput ∧
    (∀ t : ℝ, 0 ≤ t → |nativeOriginalIntegerDrive t| ≤
      nativeOriginalDriveDecayConstant * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-(t / 2))) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |nativeOriginalIntegerDrive t| ≤
        C * (1 + t + UniversalSinc.fixedScale) * Real.exp (-((n : ℝ) - 1 / 2) * t)) ∧
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |nativeOriginalIntegerDrive t| ≤ C * Real.exp (-A * t)) ∧
    (∀ t : ℝ, t < 0 → nativeOriginalIntegerDrive t = 0) ∧
    Integrable nativeOriginalIntegerDrive ∧
    Integrable nativeCompletedInput ∧
    (∀ t : ℝ, t < 0 → nativeCompletedInput t = 0) ∧
    (∀ t : ℝ, |nativeCompletedInput t| ≤ nativeCompletedInputUniformBound) ∧
    (∀ ε : ℝ, 0 ≤ ε → MemLp (nativeDampedCompletedInput ε) 2 volume)
  /-- N31 `native.a_Y`: the actual floor kernel a, its mass < 605/621,
  Y = c * U, and a * X = Y pointwise (before any X L2 claim). -/
  n31_native_a_Y :
    out.rangeData = (nativeCompletedInput, nativeCompletionCorrection) ∧
    (∀ t : ℝ, nativePositiveCompletion t =
      if 0 ≤ t then
        Real.exp (-(3 * t / 2)) * (⌊Real.exp t⌋₊ : ℝ) *
          ((⌊Real.exp t⌋₊ : ℝ) + 1 - Real.exp t)
      else 0) ∧
    (∀ t : ℝ, 0 ≤ nativePositiveCompletion t) ∧
    (∫ t : ℝ, ‖nativePositiveCompletion t‖) < (605 / 621 : ℝ) ∧
    (∀ t : ℝ, nativeCompletionCorrection t =
      if 0 ≤ t then -Real.exp (-(t / 2)) + 2 * Real.exp (-(3 * t / 2)) else 0) ∧
    (∀ t : ℝ, nativeCompletedInput t =
      ∫ s : ℝ, nativeCompletionCorrection s * nativeOriginalIntegerDrive (t - s)) ∧
    (∀ t : ℝ, Integrable (fun s : ℝ => nativePositiveCompletion s *
      nativeOriginalPrimeField (t - s))) ∧
    (∀ t : ℝ, (∫ s : ℝ, nativePositiveCompletion s *
      nativeOriginalPrimeField (t - s)) = nativeCompletedInput t)
  /-- N32 `native.transforms`: physical Laplace transforms R·zeta for a and
  -R·zeta'·J for Y and U, J with one Q factor; the exceptional point
  w = 1/2 is treated separately. -/
  n32_native_transforms :
    (∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 →
      (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ)) =
        nativeCompletionRationalMultiplier w * riemannZeta (w + 1 / 2)) ∧
    nativePositiveCompletionLaplace (1 / 2 : ℂ) = 1 / 2 ∧
    (∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 →
      (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ)) =
        -deriv riemannZeta (w + 1 / 2) * nativeOriginalSourceLaplace w) ∧
    (∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 →
      (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeCompletedInput t : ℂ)) =
        nativeCompletionRationalMultiplier w * (-deriv riemannZeta (w + 1 / 2)) *
          nativeOriginalSourceLaplace w) ∧
    (∫ t : ℝ, Complex.exp (-(1 / 2 : ℂ) * (t : ℂ)) * (nativeCompletedInput t : ℂ)) = 0 ∧
    (∀ w : ℂ, nativeOriginalSourceLaplace w =
      ((Complex.I * w) ^ 2 + 1 / 4) ^ 2 *
        UniversalSinc.product UniversalSinc.fixedScale (Complex.I * w)) ∧
    (∀ w : ℂ, nativeCompletionRationalMultiplier w = (w - 1 / 2) / ((w + 1 / 2) * (w + 3 / 2)))
  /-- N33 `range.operator`: the actual full-line and causal L2 operators,
  the damped kernel, and the bounded norm; Y's causal L2 class. -/
  n33_range_operator :
    (∀ (ε : ℝ) (hε : 0 ≤ ε) (f : nativeCompletionCausalL2),
      (nativeDampedCompletionCausalL2Operator ε hε f : NativeCompletionL2) =
        ∫ t : ℝ, nativeDampedCompletionKernel ε t •
          nativeCompletionL2Delay t (f : NativeCompletionL2)) ∧
    (∀ ε t : ℝ, nativeDampedCompletionKernel ε t =
      Real.exp (-ε * t) * nativePositiveCompletion t) ∧
    (∀ ε t : ℝ, t < 0 → nativeDampedCompletionKernel ε t = 0) ∧
    (∀ ε : ℝ, 0 ≤ ε → (∫ t : ℝ, ‖nativeDampedCompletionKernel ε t‖) < (605 / 621 : ℝ)) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ‖nativeDampedCompletionL2Operator ε hε‖ < (605 / 621 : ℝ)) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε),
      ‖nativeDampedCompletionCausalL2Operator ε hε‖ < (605 / 621 : ℝ)) ∧
    IsClosed (nativeCompletionCausalL2 : Set NativeCompletionL2) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε),
      ((nativeCompletedInputCausalL2 ε hε : NativeCompletionL2) : ℝ → ℂ) =ᵐ[volume]
        nativeDampedCompletedInput ε) ∧
    (∀ ε t : ℝ, nativeDampedCompletedInput ε t =
      ((Real.exp (-ε * t) * out.rangeData.1 t : ℝ) : ℂ))
  /-- N34 `range.residual_iteration`: actual finite iterations, norm loss,
  invariant adjoint-kernel projection.  No zero limit is asserted; at any
  actual off-line zero the residual of Y stays bounded below. -/
  n34_range_residual_iteration :
    (∀ (ε : ℝ) (hε : 0 ≤ ε) (e : nativeCompletionCausalL2) (n : ℕ),
      nativeAdjointResidualIterate ε hε e (n + 1) =
        nativeAdjointResidualIterate ε hε e n -
          nativeDampedCompletionCausalL2Operator ε hε
            (nativeDampedCompletionCausalL2Adjoint ε hε
              (nativeAdjointResidualIterate ε hε e n))) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε) (e : nativeCompletionCausalL2),
      ‖nativeAdjointResidualStep ε hε e‖ ^ 2 ≤ ‖e‖ ^ 2 -
        (2 - (605 / 621 : ℝ) ^ 2) * ‖nativeDampedCompletionCausalL2Adjoint ε hε e‖ ^ 2) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε) (e : nativeCompletionCausalL2),
      Antitone (fun n => ‖nativeAdjointResidualIterate ε hε e n‖)) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε) (e : nativeCompletionCausalL2) (n : ℕ),
      nativeCompletionAdjointKernelProjection ε hε (nativeAdjointResidualIterate ε hε e n) =
        nativeCompletionAdjointKernelProjection ε hε e) ∧
    (∀ (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ),
      nativeCompletedInputResidualIterate ε hε n =
        nativeAdjointResidualIterate ε hε (nativeCompletedInputCausalL2 ε hε) n) ∧
    (∀ (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (n : ℕ),
      0 < ‖inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
          (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
            (nativeZeroJetDamping_pos ρ hoff).le)‖ / ‖nativeZeroJetAdjointWitness ρ hoff‖ ∧
        ‖inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
          (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
            (nativeZeroJetDamping_pos ρ hoff).le)‖ / ‖nativeZeroJetAdjointWitness ρ hoff‖ ≤
          ‖nativeCompletedInputResidualIterate (nativeZeroJetDamping ρ)
            (nativeZeroJetDamping_pos ρ hoff).le n‖)
  /-- N35 `forcing.direct`: the actual response of the stored detector's
  physical function, the direct predecessor projection, and its equality with
  the spectral form b_eta = P x + B y. -/
  n35_forcing_direct :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let state := out.retained.state
    let J := nativeDetectorPredecessorEmbedding σ state.selection
    let T := nativePoleNeutralParityShifted σ L Kd (-state.selection.eta)
    let P := nativeDetectorPredecessorEquiv σ state.inverses
    let x := J.toLinearMap.adjoint state.detector
    let y := isometricDetectorComplementCoordinate J state.detector
    out.retained.predecessorForcing =
      originalDetectorNativeForcing σ state.selection state.detector ∧
    originalDetectorNativeForcing σ state.selection state.detector =
      J.toLinearMap.adjoint (T state.detector) ∧
    originalDetectorNativeForcing σ state.selection state.detector =
      P x + isometricDetectorCoupling J T y ∧
    ∀ v : nativePoleNeutralParitySpace σ L (state.selection.cutoff - 1),
      inner ℂ v out.retained.predecessorForcing =
        (∫ z : ℝ,
          nativeWeilResponse (originalDetectorPaddedFinitePhysicalUnit
            (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos) z *
            conj (finitePhysicalSynthesis L Kd
              (canonicalNativeCoefficientInclusion σ L Kd (J v)) z)) +
          (state.selection.eta : ℂ) * inner ℂ (J v) state.detector
  /-- N39 `exterior.original`: the actual original response R_f, its interior,
  left and right causal exterior restrictions and reconstructions.  The
  interior is the genuine restriction and is nonzero even as an AE class.
  The literal left/right causal tails vanish at t=0; the interior owns
  both physical endpoints. -/
  n39_exterior_original :
    (¬ (out.smoothOriginal.interior =ᵐ[volume] (0 : ℝ → ℂ))) ∧
    out.originalLeftCausalTail =
      (Ioi (0 : ℝ)).indicator (fun t => out.smoothOriginal.response (-t)) ∧
    out.originalRightCausalTail =
      (Ioi (0 : ℝ)).indicator
        (fun t => out.smoothOriginal.response (fixedOriginalSincTrialAperture a + t)) ∧
    (∀ t : ℝ, t ≤ 0 →
      out.originalLeftCausalTail t = 0 ∧ out.originalRightCausalTail t = 0) ∧
    (∀ x : ℝ, out.smoothOriginal.response x = out.originalLeftCausalTail (-x) +
      out.smoothOriginal.interior x +
        out.originalRightCausalTail (x - fixedOriginalSincTrialAperture a)) ∧
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let sg := nativeOriginalDetectorPhaseSign σ
    let p := out.retained.state.detector
    out.originalExteriorView = out.smoothOriginal ∧
    out.smoothOriginal = OriginalNativeExteriorRecord.fromOriginalSource sg a out.aperture_pos ∧
    out.smoothOriginal.response = nativeWeilResponse out.originalTrial ∧
    out.smoothOriginal.left = (Iio (0 : ℝ)).indicator (nativeWeilResponse out.originalTrial) ∧
    out.smoothOriginal.interior =
      (Icc (0 : ℝ) L).indicator (nativeWeilResponse out.originalTrial) ∧
    out.smoothOriginal.right = (Ioi L).indicator (nativeWeilResponse out.originalTrial) ∧
    (∀ x : ℝ, out.smoothOriginal.response x =
      out.smoothOriginal.left x + out.smoothOriginal.interior x + out.smoothOriginal.right x) ∧
    MemLp out.smoothOriginal.interior 2 volume ∧
    (∀ x : ℝ, nativeWeilResponse out.originalTrial x =
      nativeWeilArchResponse out.originalTrial x + nativeWeilPoleResponse out.originalTrial x -
        originalSmoothFourPrimeHistories sg a x) ∧
    out.retained.nativeHistory.response = originalDetectorNativeResponse σ L Kd p ∧
    out.retained.nativeHistory.interiorHistory =
      originalDetectorNativeInteriorHistory σ L Kd p ∧
    (∀ x : ℝ, originalDetectorNativeResponse σ L Kd p x =
      originalDetectorNativeLeftExterior σ L Kd p x +
        originalDetectorNativeInteriorHistory σ L Kd p x +
        originalDetectorNativeRightExterior σ L Kd p x) ∧
    MemLp (originalDetectorNativeInteriorHistory σ L Kd p) 2 volume ∧
    (∀ x : ℝ, originalDetectorNativeResponse σ L Kd p x -
        originalSmoothWeilResponse sg a x =
      (nativeWeilArchResponse
          (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) x -
        nativeWeilArchResponse (fixedOriginalSincPhaseTrial sg a) x) +
      (nativeWeilPoleResponse
          (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) x -
        nativeWeilPoleResponse (fixedOriginalSincPhaseTrial sg a) x) -
      (nativeWeilPrimeResponse
          (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) x -
        originalSmoothFourPrimeHistories sg a x))
  /-- N40 `exterior.history`: compact boundary splitting with the literal
  interior history, and the exact common finite arithmetic cutoff. -/
  n40_exterior_history :
    let L := fixedOriginalSincTrialAperture a
    let c := fixedOriginalSincLobeCenter
    let sg := nativeOriginalDetectorPhaseSign σ
    (∀ (b t0 : ℝ) (K : ℝ → ℂ), Continuous K → tsupport K ⊆ Icc (-b) b → 0 ≤ b →
      2 * b ≤ L → 0 ≤ t0 →
      (∫ y : ℝ, K y * out.smoothOriginal.response (L - b + t0 - y)) =
        (∫ y : ℝ, K y * out.smoothOriginal.right (L - b + t0 - y)) +
          (∫ y : ℝ, K y * out.smoothOriginal.interior (L - b + t0 - y))) ∧
    (∀ (b t0 : ℝ) (K : ℝ → ℂ), tsupport K ⊆ Icc (-b) b → 0 ≤ b → 2 * b ≤ L → 0 ≤ t0 →
      ∀ y : ℝ,
        K y * out.smoothOriginal.right (L - b + t0 - y) =
          (Iio (t0 - b)).indicator
            (fun u : ℝ => K u * out.smoothOriginal.response (L - b + t0 - u)) y ∧
        K y * out.smoothOriginal.interior (L - b + t0 - y) =
          (Ici (t0 - b)).indicator
            (fun u : ℝ => K u * out.smoothOriginal.response (L - b + t0 - u)) y) ∧
    (∀ g : ℝ → ℂ, Continuous g → HasCompactSupport g →
      (∫ x : ℝ, out.smoothOriginal.response x * g x) =
        (∫ x : ℝ, out.smoothOriginal.left x * g x) +
          (∫ x : ℝ, out.smoothOriginal.interior x * g x) +
          (∫ x : ℝ, out.smoothOriginal.right x * g x)) ∧
    out.smoothOriginal.primeHistories = originalSmoothFourPrimeHistories sg a ∧
    (∀ x : ℝ, nativeWeilPrimeResponse out.originalTrial x =
      out.smoothOriginal.primeHistories x) ∧
    (∀ x ∈ Icc (0 : ℝ) L,
      let T := max (L - c) c
      let N := nativeHistoryCutoff UniversalSinc.fixedScale T + 1
      nativeOriginalKernelPrimeField (x - c) =
          ∑ n ∈ Finset.range N, (nativePrimeCoefficient n : ℂ) *
            universalSincKernel UniversalSinc.fixedScale (x - c - Real.log n) ∧
      nativeOriginalKernelPrimeField (c - x) =
          ∑ n ∈ Finset.range N, (nativePrimeCoefficient n : ℂ) *
            universalSincKernel UniversalSinc.fixedScale (c - x - Real.log n) ∧
      nativeOriginalKernelPrimeField (L - x - c) =
          ∑ n ∈ Finset.range N, (nativePrimeCoefficient n : ℂ) *
            universalSincKernel UniversalSinc.fixedScale (L - x - c - Real.log n) ∧
      nativeOriginalKernelPrimeField (x + c - L) =
          ∑ n ∈ Finset.range N, (nativePrimeCoefficient n : ℂ) *
            universalSincKernel UniversalSinc.fixedScale (x + c - L - Real.log n))

/-- Every field is filled from existing theorems on the SAME stored packet,
with small glue proofs and no hypothesis beyond `out`. -/
theorem Step123NativeFieldRecord.fromNative
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123NativeFieldRecord out where
  n01_source_scale := ⟨rfl, UniversalSinc.fixedScale_pos, rfl, rfl, rfl⟩
  n02_source_q_k_j :=
    ⟨rfl, fun _ _ => rfl, rfl, rfl,
      universalSincKernel_eq_real UniversalSinc.fixedScale UniversalSinc.fixedScale_pos,
      fun x => universalSincSecondKernel_eq_real UniversalSinc.fixedScale_pos x, rfl⟩
  n03_source_properties := by
    have hs := UniversalSinc.fixedScale_pos
    refine ⟨step123_fixed_source_evidence, universalSincSource_contDiff hs,
      universalSincKernel_contDiff hs, universalSincSecondKernel_contDiff hs,
      universalSincKernel_support hs, universalSincSecondKernel_support hs, ?_,
      originalSincTest_even hs, originalSincSecondTest_even hs,
      paperFT_universalSincKernel hs, paperFT_universalSincSecondKernel hs,
      universalSincSecondKernel_integral hs, nativeOriginalSource_integral⟩
    intro x
    rw [universalSincKernel_eq_real _ hs, universalSincSecondKernel_eq_real hs]
    exact ⟨Complex.ofReal_im _, Complex.ofReal_im _⟩
  n04_source_bounds :=
    ⟨universalSincSource_gevrey_bound UniversalSinc.fixedScale_pos,
      universalSincProduct_decay UniversalSinc.fixedScale_pos,
      universalSincSource_scale UniversalSinc.fixedScale_pos,
      poleKilled_universalSincSource_norm_sq UniversalSinc.fixedScale_pos⟩
  n05_trial_index := ⟨rfl, rfl, phaseSign_cases σ, out.aperture_pos, out.aperture_gt_four⟩
  n06_trial_original :=
    ⟨rfl, rfl, rfl, out.original_trial_reflected,
      fixedOriginalSincPhaseTrial_contDiff _ a,
      fixedOriginalSincPhaseTrial_hasCompactSupport _ a⟩
  n07_trial_original_properties := by
    have ha := step123_separation_gt_scale out
    have hs := UniversalSinc.fixedScale_pos
    refine ⟨ha, ?_, fixedOriginalSincPhaseTrial_integral_norm_sq (phaseSign_pm σ) ha,
      fixedOriginalSincPhaseTrial_support ha _, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : x - fixedOriginalSincLobeCenter ∈
          Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
      · right
        apply universalSincKernel_zero_outside hs
        intro hy
        have h1 := hx.2
        have h2 := hy.2
        unfold fixedOriginalSincTrialAperture at h2
        linarith
      · left
        exact universalSincKernel_zero_outside hs hx
    · rw [nativePoleMoment_eq_paperFT]
      apply fixedOriginalSincPhaseTrial_paperFT_eq_zero
      have hz : (-((1 / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I / 2 := by push_cast; ring
      rw [hz]
      exact (paperFT_originalSincTest_elementary_pair hs).2
    · rw [nativePoleMoment_eq_paperFT]
      apply fixedOriginalSincPhaseTrial_paperFT_eq_zero
      have hz : (-((-1 / 2 : ℝ) : ℂ) * Complex.I) = Complex.I / 2 := by push_cast; ring
      rw [hz]
      exact (paperFT_originalSincTest_elementary_pair hs).1
    · intro x
      rw [out.original_trial_reflected, out.original_trial_reflected]
      have hx : fixedOriginalSincTrialAperture a - (fixedOriginalSincTrialAperture a - x) -
          fixedOriginalSincLobeCenter = x - fixedOriginalSincLobeCenter := by ring
      rw [hx]
      linear_combination (-((fixedOriginalSincTrialNormalization : ℂ) *
        fixedOriginalSincKernel (fixedOriginalSincTrialAperture a - x -
          fixedOriginalSincLobeCenter))) * phaseSign_mul_self σ
  n08_image_raw := by
    have h2 := step123_aperture_two_le out
    exact ⟨rfl, rfl,
      originalDetectorPositivePadding_pos UniversalSinc.fixedScale_pos out.aperture_pos,
      fun _ => rfl, fun _ => rfl, fun _ => rfl,
      originalDetectorPaddedFiniteWindowImageFinsupp_support _ _ h2,
      localizedFiniteFunction_originalDetectorPaddedFiniteWindowImageCoefficients _ _ h2,
      localizedFiniteFunction_originalDetectorPaddedFinitePoleImageCoefficients _ _ h2, rfl⟩
  n09_image_positive_primitive := by
    have h2 := step123_aperture_two_le out
    have hs := UniversalSinc.fixedScale_pos
    have ha := step123_separation_gt_scale out
    have hleft : 1 + UniversalSinc.fixedScale ≤ fixedOriginalSincLobeCenter := le_of_eq rfl
    have hright : fixedOriginalSincLobeCenter + UniversalSinc.fixedScale ≤
        fixedOriginalSincTrialAperture a - 1 := by
      unfold fixedOriginalSincTrialAperture fixedOriginalSincLobeCenter
      linarith
    exact ⟨fun x hx => originalDetectorPaddedFiniteWindowImage_re_nonneg hs h2 hleft hright hx,
      fun x hx => originalDetectorPaddedFiniteEvenPrimitive_re_nonneg hs h2 hleft hright hx,
      originalDetectorPaddedFiniteWindowImage_real _ _ _ _,
      originalDetectorPaddedFiniteWindowImage_eq_unpadded_add _ _ _ _,
      originalDetectorPaddedFiniteOddPrimitive_padding_cancels _ _ _ _,
      originalDetectorOddPadding_coefficients_eq _ h2,
      originalDetectorOddPadding_unitVector_eq _ h2⟩
  n10_image_endpoint_jets := by
    have h2 := step123_aperture_two_le out
    refine ⟨fun r hr =>
        originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight _ _ out.aperture_pos hr,
      fun r hr => originalDetectorPaddedFinitePoleImage_endpoint_jets_lt_six _ _ h2 hr,
      originalDetectorPaddedFinitePoleImage_hard_contDiff_four _ _ h2, ?_, ?_⟩
    · intro r hr
      rw [step123_detector_coefficients out]
      exact originalDetectorPaddedFinitePhaseUnitVector_moment_zero_lt_six _ _ h2 hr
    · rw [step123_detector_coefficients out]
      exact paddedUnit_physical_contDiff_four _ _ h2
  n11_image_native_p := ⟨out.detector_source_eq, step123_detector_coefficients out, rfl, rfl⟩
  n12_image_unit_and_poles :=
    ⟨out.retained.state.detector_unit, out.originalDetector_poles.1,
      out.originalDetector_poles.2, nativePoleNeutralParityAmbient_legal σ _ _ _,
      canonicalNativeCoefficientInclusion_eq_ambient σ _ _ _,
      canonicalNativeCoefficientInclusion_mem_parity σ _ _ _⟩
  n13_image_physical_equality := by
    refine ⟨out.finitePhysicalSource_eq_originalPadded, rfl, ?_, out.physicalFiniteImage_unit⟩
    rw [← out.finitePhysicalSource_eq_originalPadded]
    exact canonicalNativePhysicalIsometry_ae σ out.aperture_pos _ _
  n15_phase_full_matrices :=
    ⟨rfl, rfl, rfl, originalDetectorPaddedFinitePhasePlane_rayleigh_identity _ _ _,
      originalDetectorPaddedFinitePhaseVector_eq_planeVector _ _ _ _⟩
  n16_phase_scalar_contract := by
    have hsel := out.source_selector
    have hpm := phaseSign_pm σ
    have hνω := originalDetectorPaddedPhase_denominator_pos (Or.inl rfl) _ _ out.aperture_pos
      hsel.even_nonzero
    have hνω' := originalDetectorPaddedPhase_denominator_pos (Or.inr rfl) _ _ out.aperture_pos
      hsel.odd_nonzero
    refine ⟨originalDetectorPaddedPhaseGram_real _ _ _,
      originalDetectorPaddedPhaseEnergy_real _ _ _, by linarith, by linarith,
      originalDetectorPaddedPhase_norm_sq hpm _ _ _,
      originalDetectorPaddedPhase_energy hpm _ _ _,
      originalDetectorPaddedPhase_scalar_quotient hpm _ _ _, ?_⟩
    rw [← nativePoleNeutralParityAmbient_energy, ← canonicalNativeCoefficientInclusion_eq_ambient,
      step123_detector_coefficients out, ← originalDetectorPaddedPhase_scalar_quotient hpm]
    unfold originalDetectorPaddedFinitePhaseUnitVector
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  n17_retained_state :=
    ⟨rfl, step123NativeCorePacket_eq_ofState out.retained, out.detector_source_eq,
      out.retained.state.detector_depth, Real.exp_pos _, out.retained.forcing_eq,
      out.retained.history_eq, rfl⟩
  n18_retained_eta_lambda := by
    have hg := nativeDeepThresholdGap_pos _ _ out.retained.state.depth_pos
      (out.retained.state.selection.cutoff_nonempty.trans
        out.retained.state.selection.cutoff_le_detector)
    have hd := out.retained.state.selection.lam_depth
    refine ⟨out.retained.state.selection.lam_is_actual_global,
      out.retained.state.selection.cutoff_nonempty,
      out.retained.state.selection.cutoff_le_detector,
      out.retained.state.selection.eta_lower, out.retained.state.selection.eta_upper, rfl, hg,
      hd, ?_, out.retained.state.selection.earlier_bottoms,
      out.retained.state.selection.predecessor_bottoms,
      out.retained.state.selection.first_predecessor_empty⟩
    intro h
    linarith
  n19_retained_inverses :=
    ⟨out.retained.state.inverses.evenGround_actual,
      out.retained.state.inverses.oddGround_actual,
      out.retained.state.inverses.evenDetector_actual,
      out.retained.state.inverses.oddDetector_actual,
      out.retained.state.inverses.evenGround_inverse_bound,
      out.retained.state.inverses.oddGround_inverse_bound,
      out.retained.state.inverses.evenDetector_inverse_bound,
      out.retained.state.inverses.oddDetector_inverse_bound,
      nativeDetectorPredecessorEquiv_actual σ out.retained.state.inverses,
      nativeSelectedGroundPredecessorEquiv_actual _ out.retained.state.inverses,
      nativeDetectorPredecessorEquiv_inverse_bound σ out.retained.state.inverses,
      nativeSelectedGroundPredecessorEquiv_inverse_bound _ out.retained.state.inverses,
      nativeDeepThreshold_inverse_norms_zero_at_first _ out.retained.state.inverses⟩
  n20_retained_ground :=
    ⟨rfl, out.selected_ground_eigen.1, out.selected_ground_eigen.2,
      out.retained.state.selection.lam_is_actual_global⟩
  n22_retained_source_correction := by
    have hK := out.retained.state.selection.cutoff_nonempty
    exact ⟨fun _ => rfl, rfl, poleNeutralEvenOutputResidual_eq_normal _ _, fun _ => rfl,
      fun _ => rfl,
      poleNeutralOddProjection_index_evenNormal_eq_cubic out.aperture_pos _ (by omega),
      canonicalPoleNeutralRankOneIntertwining out.aperture_pos _ (by omega)⟩
  n24_retained_admissible :=
    ⟨out.source_selector, out.source_selector.even_nonzero, out.source_selector.odd_nonzero,
      out.source_selector.even_unit, out.source_selector.odd_unit,
      out.retained.state.detector_depth⟩
  n25_schur_detector := by
    obtain ⟨h1, h2, h3⟩ := originalDetector_schur_loss_lower out.retained.state
    exact ⟨out.original_detector_complement_dimension, rfl,
      originalDetector_schur_completion out.retained.state, h1, h2, h3⟩
  n26_schur_ground := out.selected_ground_shiftedSchur
  n27_residual_neutral :=
    ⟨rfl, rfl,
      canonicalPoleNeutralTrialResidual_orthogonal σ _ _ _ out.retained.state.detector_unit,
      out.ownNeutralResidual_variance⟩
  n28_residual_gram :=
    ⟨canonicalPoleNeutralTrialChannel_sum σ _ _, out.ownNeutralResidual_channels,
      fun _ _ => rfl, out.ownNeutralResidual_gram⟩
  n29_native_X_U :=
    ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      native_divisor_convolution_identity, native_divisor_coefficient_identity,
      native_primeCoefficients_unique, originalDetector_correlationField_eq_sourceConvolution⟩
  n30_native_input_decay :=
    ⟨rfl, rfl, fun _ ht => nativeOriginalIntegerDrive_decay ht,
      nativeOriginalIntegerDrive_finiteOrder_bound, nativeOriginalIntegerDrive_rapid_bound,
      fun _ ht => nativeOriginalIntegerDrive_zero_of_neg ht,
      nativeOriginalIntegerDrive_integrable, nativeCompletedInput_integrable,
      fun _ ht => nativeCompletedInput_zero_of_neg ht, nativeCompletedInput_abs_le_uniform,
      fun _ hε => nativeCompletedInput_memLp hε⟩
  n31_native_a_Y :=
    ⟨rfl, fun _ => rfl, nativePositiveCompletion_nonneg,
      nativePositiveCompletion_integral_norm_lt_605_div_621, fun _ => rfl, fun _ => rfl,
      nativeCompletedInput_equation_integrable, nativeCompletedInput_equation⟩
  n32_native_transforms :=
    ⟨fun _ hw hne => nativePositiveCompletion_complexLaplace hw hne,
      nativePositiveCompletion_complexLaplace_half,
      fun _ hw hne => nativeOriginalIntegerDrive_complexLaplace hw hne,
      fun _ hw hne => nativeCompletedInput_complexLaplace hw hne,
      nativeCompletedInput_complexLaplace_half,
      nativeOriginalSourceLaplace_formula, fun _ => rfl⟩
  n33_range_operator :=
    ⟨fun ε hε f => (nativeDampedCompletionCausalL2Operator_coe_apply ε hε f).trans
        (nativeDampedCompletionL2Operator_apply ε hε f),
      fun _ _ => rfl, fun ε _ ht => nativeDampedCompletionKernel_zero_of_neg ε ht,
      fun _ hε => nativeDampedCompletionKernel_integral_norm_lt_605_div_621 hε,
      nativeDampedCompletionL2Operator_norm_lt_605_div_621,
      nativeDampedCompletionCausalL2Operator_norm_lt_605_div_621,
      nativeCompletionCausalL2_isClosed, nativeCompletedInputCausalL2_coeFn, fun _ _ => rfl⟩
  n34_range_residual_iteration :=
    ⟨nativeAdjointResidualIterate_succ, nativeAdjointResidual_norm_loss,
      nativeAdjointResidual_norm_antitone, nativeAdjointResidual_kernelProjection_preserved,
      fun _ _ _ => rfl, nativeCompletedInput_zeroJet_residual_lower⟩
  n35_forcing_direct := by
    obtain ⟨h1, h2⟩ := originalDetector_projectedForcing_eq σ out.retained.state.inverses
      out.retained.state.detector
    refine ⟨out.retained.forcing_eq, rfl, h1, ?_⟩
    intro v
    rw [out.retained.forcing_eq, h2 v, out.finitePhysicalSource_eq_originalPadded]
  n39_exterior_original :=
    ⟨out.originalInterior_not_ae_zero,
      out.originalLeftCausalTail_eq_indicator, out.originalRightCausalTail_eq_indicator,
      fun _ ht => out.originalCausalTails_zero_of_nonpos ht,
      out.originalResponse_causalTail_reconstruction, rfl, out.smoothOriginal_eq,
      out.smoothOriginal.response_eq, out.smoothOriginal.left_eq,
      out.smoothOriginal.interior_eq, out.smoothOriginal.right_eq,
      out.smoothOriginal.reconstruction, out.smoothOriginal.interior_memLp,
      fun x => (originalNativeExterior_history_eq _ a out.aperture_pos x).1,
      out.retained.nativeHistory.response_eq, out.retained.nativeHistory.interior_eq,
      originalDetectorNativeResponse_reconstruction σ _ _ _ out.aperture_pos.le,
      originalDetectorNativeInteriorHistory_memLp_two σ out.aperture_pos _ _,
      originalNativeExterior_residual_eq σ _ _ _ a⟩
  n40_exterior_history := by
    refine ⟨(Step123OriginalBoundaryEvidence.fromNative out).original_right_convolution_retains_interior,
      ?_, ?_, out.smoothOriginal.primeHistories_eq, out.smoothOriginal.prime_eq,
      fun x hx => originalNativeFourHistories_common_finite_cutoff a x hx⟩
    · intro b t0 K hKs hb hL ht0 y
      rw [out.smoothOriginal.response_eq, out.smoothOriginal.right_eq,
        out.smoothOriginal.interior_eq]
      exact originalSmoothRightBoundary_pointwise_cut _ a b t0 K hKs hb hL ht0 y
    · intro g hg hgc
      rw [out.smoothOriginal.response_eq, out.smoothOriginal.left_eq,
        out.smoothOriginal.interior_eq, out.smoothOriginal.right_eq]
      exact originalSmoothWeilResponse_compactPairing_split _ a out.aperture_pos.le hg hgc

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeFieldRecord.fromNative
