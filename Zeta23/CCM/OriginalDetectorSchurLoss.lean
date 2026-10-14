import Zeta23.CCM.Step123NativeCorePacket

/-!
# State-independent, original-detector native Schur loss

The scalar is defined from the ORIGINAL padded phase source and the
actual source-free selector (beta,L,eta,K); it does not receive a
separately chosen eigenvector, retained state or inverse.  The
predecessor inverse is forced by an actual coercive matrix.

The independent all-selectors subexponential bound remains OPEN.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

private theorem nativeAdmissiblePredecessor_coercive
    (σ : ReversalParity) {β L eta : ℝ} {K : ℕ}
    (h : AdmissibleDetectorSelector β L eta K)
    (v : nativePoleNeutralParitySpace σ L (K - 1)) :
    nativeDeepThresholdGap (Real.exp (β * L))
      (originalDetectorQuarticCutoff L) * ‖v‖ ^ 2 ≤
      (inner ℂ (nativePoleNeutralParityShifted σ L (K - 1) (-eta) v) v).re := by
  have hL : 0 < L := by linarith [h.aperture_large]
  by_cases hprev : 3 ≤ K - 1
  · have hless : K - 1 < K := by have hk := h.cutoff_nonempty; omega
    have hglobal := h.earlier_bottoms (K - 1) hprev hless
    cases σ
    · have hp : -eta + nativeDeepThresholdGap (Real.exp (β * L))
          (originalDetectorQuarticCutoff L) ≤
          poleNeutralEvenRayleighBottom L (K - 1) hL hprev :=
        hglobal.trans (min_le_left _ _)
      have hgap : nativeDeepThresholdGap (Real.exp (β * L))
          (originalDetectorQuarticCutoff L) ≤
          poleNeutralEvenRayleighBottom L (K - 1) hL hprev - (-eta) := by
        linarith
      exact (mul_le_mul_of_nonneg_right hgap (sq_nonneg ‖v‖)).trans
        (poleNeutralEvenShiftedCanonical_coercive hL (K - 1) hprev (-eta) v)
    · have hp : -eta + nativeDeepThresholdGap (Real.exp (β * L))
          (originalDetectorQuarticCutoff L) ≤
          poleNeutralOddRayleighBottom L (K - 1) hL hprev :=
        hglobal.trans (min_le_right _ _)
      have hgap : nativeDeepThresholdGap (Real.exp (β * L))
          (originalDetectorQuarticCutoff L) ≤
          poleNeutralOddRayleighBottom L (K - 1) hL hprev - (-eta) := by
        linarith
      exact (mul_le_mul_of_nonneg_right hgap (sq_nonneg ‖v‖)).trans
        (poleNeutralOddShiftedCanonical_coercive hL (K - 1) hprev (-eta) v)
  · have hfirst : K = 3 := by have hk := h.cutoff_nonempty; omega
    have hpred : K - 1 = 2 := by omega
    have hzero :
        Module.finrank ℂ (nativePoleNeutralParitySpace σ L (K - 1)) = 0 := by
      cases σ
      · simpa [hpred] using (h.first_predecessor_empty hfirst).1
      · simpa [hpred] using (h.first_predecessor_empty hfirst).2
    have hv : v = 0 :=
      (finrank_zero_iff_forall_zero
        (K := ℂ) (V := nativePoleNeutralParitySpace σ L (K - 1))).mp hzero v
    subst v
    simp

/-- An actual native inverse, defined from beta,L,eta,K alone on the
admissible selector domain. No inverse is supplied as a proof premise. -/
def nativeAdmissibleDetectorPredecessorEquiv
    (σ : ReversalParity) {β L eta : ℝ} {K : ℕ}
    (h : AdmissibleDetectorSelector β L eta K) :
    nativePoleNeutralParitySpace σ L (K - 1) ≃ₗ[ℂ]
      nativePoleNeutralParitySpace σ L (K - 1) := by
  let T := nativePoleNeutralParityShifted σ L (K - 1) (-eta)
  have hg : 0 < nativeDeepThresholdGap (Real.exp (β * L))
      (originalDetectorQuarticCutoff L) :=
    nativeDeepThresholdGap_pos _ _ (Real.exp_pos _)
      (h.cutoff_nonempty.trans h.cutoff_le_detector)
  have hi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hb := nativeAdmissiblePredecessor_coercive σ h u
    change T u = 0 at hu
    rw [hu, inner_zero_left, Complex.zero_re] at hb
    have hsq : ‖u‖ ^ 2 ≤ 0 := by
      by_contra hn
      push Not at hn
      exact (not_lt_of_ge hb) (mul_pos hg hn)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])
  exact LinearEquiv.ofInjectiveEndo T hi

theorem nativeAdmissibleDetectorPredecessorEquiv_actual
    (σ : ReversalParity) {β L eta : ℝ} {K : ℕ}
    (h : AdmissibleDetectorSelector β L eta K)
    (v : nativePoleNeutralParitySpace σ L (K - 1)) :
    nativeAdmissibleDetectorPredecessorEquiv σ h v =
      nativePoleNeutralParityShifted σ L (K - 1) (-eta) v := rfl

/-- The original normalized phase is selected solely by its source
index sigma; the detector eigenvector remains a different object. -/
def nativeOriginalAdmissibleSchurLoss
    (σ : ReversalParity) {β L eta : ℝ} {K : ℕ}
    (h : AdmissibleDetectorSelector β L eta K) : ℝ := by
  have h2 : 2 ≤ L := by linarith [h.aperture_large]
  let p := nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter h2
  let J := nativePoleNeutralParityCenteredZeroExtend σ L
    ((Nat.sub_le K 1).trans h.cutoff_le_detector)
  let T := nativePoleNeutralParityShifted σ L (originalDetectorQuarticCutoff L) (-eta)
  let P := nativeAdmissibleDetectorPredecessorEquiv σ h
  let y := isometricDetectorComplementCoordinate J p
  exact -(inner ℂ (isometricDetectorSchurOperator J T P y) y).re

/-- C-Schur: independent OPEN upper estimate on the exact, fully signed
detector complement. Constants are independent of the phase,
source-generated eta and cutoff, and the selected-ground branch. -/
def NativeOriginalDetectorSchurSubexponential : Prop :=
  ∀ (β ε : ℝ), 0 < β → 0 < ε →
    ∃ C L0 : ℝ, 0 < C ∧ 4 ≤ L0 ∧
      ∀ (σ : ReversalParity) (L eta : ℝ) (K : ℕ)
        (h : AdmissibleDetectorSelector β L eta K),
        L0 < L →
          nativeOriginalAdmissibleSchurLoss σ h ≤ C * Real.exp (ε * L)

/-- Independence from the separately stored inverse *witness*: the
source-parametric scalar uses the same actual coercive predecessor
operator, so inverse uniqueness forces equality on generated states. -/
theorem nativeOriginalAdmissibleSchurLoss_eq_retained
    (σ : ReversalParity) {β L : ℝ} {hL : 0 < L}
    (state : DetectorRetainedSchurState σ L
      (originalDetectorQuarticCutoff L) (Real.exp (β * L)) hL)
    (h : AdmissibleDetectorSelector β L
      state.selection.eta state.selection.cutoff)
    (hdet : state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [h.aperture_large])) :
    nativeOriginalAdmissibleSchurLoss σ h =
      -(inner ℂ
        (nativeDetectorSchurOperator σ state.inverses
          (isometricDetectorComplementCoordinate
            (nativeDetectorPredecessorEmbedding σ state.selection)
            state.detector))
        (isometricDetectorComplementCoordinate
          (nativeDetectorPredecessorEmbedding σ state.selection)
          state.detector)).re := by
  have hP :
      nativeAdmissibleDetectorPredecessorEquiv σ h =
      nativeDetectorPredecessorEquiv σ state.inverses := by
    apply LinearEquiv.ext
    intro v
    exact (nativeAdmissibleDetectorPredecessorEquiv_actual σ h v).trans
      (nativeDetectorPredecessorEquiv_actual σ state.inverses v).symm
  unfold nativeOriginalAdmissibleSchurLoss
  rw [hP, ← hdet]
  rfl

/-- The state-independent source loss inherits the exact
exponentially deep lower obstruction, not an independent upper sign. -/
theorem nativeOriginalAdmissibleSchurLoss_gt_half_depth
    (σ : ReversalParity) {β L : ℝ} {hL : 0 < L}
    (state : DetectorRetainedSchurState σ L
      (originalDetectorQuarticCutoff L) (Real.exp (β * L)) hL)
    (h : AdmissibleDetectorSelector β L
      state.selection.eta state.selection.cutoff)
    (hdet : state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [h.aperture_large])) :
    Real.exp (β * L) / 2 <
      nativeOriginalAdmissibleSchurLoss σ h := by
  rw [nativeOriginalAdmissibleSchurLoss_eq_retained σ state h hdet]
  have hd := (originalDetector_schur_loss_lower state).2.2
  dsimp at hd
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeAdmissibleDetectorPredecessorEquiv_actual

#print axioms Zeta23.CCM.nativeOriginalAdmissibleSchurLoss_gt_half_depth
