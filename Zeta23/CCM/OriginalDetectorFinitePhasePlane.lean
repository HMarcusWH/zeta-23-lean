import Zeta23.CCM.OriginalDetectorFinitePoleImageNonzero
import Zeta23.CCM.OriginalDetectorFinitePhysicalNorm
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseSymmetry

/-!
# The full native two-dimensional plane of the actual finite detector

Both basis vectors are constructed: the literal fixed-source quartic `Pq`
image and its coefficient reversal. The full Gram matrix and full native
energy matrix retain their cross terms before any parity specialization,
normalization or minimization.
-/

noncomputable section

open Set Complex Matrix
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

def originalDetectorFinitePhaseLeft (L c : ℝ) (hL : 0 < L) :
    EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1)) :=
  WithLp.toLp 2 (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL)

def originalDetectorFinitePhaseRight (L c : ℝ) (hL : 0 < L) :
    EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1)) :=
  WithLp.toLp 2 (reverseCoefficients (originalDetectorQuarticCutoff L)
    (originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL))

/-- The actual two-coordinate linear combination before any minimization. -/
def originalDetectorFinitePhasePlaneVector (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :=
  z 0 • originalDetectorFinitePhaseLeft L c hL + z 1 • originalDetectorFinitePhaseRight L c hL

/-- All four actual Gram entries, including the unreduced cross terms. -/
def originalDetectorFinitePhaseGram (L c : ℝ) (hL : 0 < L) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ (originalDetectorFinitePhaseLeft L c hL) (originalDetectorFinitePhaseLeft L c hL),
     inner ℂ (originalDetectorFinitePhaseLeft L c hL) (originalDetectorFinitePhaseRight L c hL);
     inner ℂ (originalDetectorFinitePhaseRight L c hL) (originalDetectorFinitePhaseLeft L c hL),
     inner ℂ (originalDetectorFinitePhaseRight L c hL) (originalDetectorFinitePhaseRight L c hL)]

/-- All four entries of the unchanged actual canonical native energy. -/
def originalDetectorFinitePhaseNativeEnergy (L c : ℝ) (hL : 0 < L) : Matrix (Fin 2) (Fin 2) ℂ :=
  let A := (canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
  !![inner ℂ (A (originalDetectorFinitePhaseLeft L c hL)) (originalDetectorFinitePhaseLeft L c hL),
     inner ℂ (A (originalDetectorFinitePhaseLeft L c hL)) (originalDetectorFinitePhaseRight L c hL);
     inner ℂ (A (originalDetectorFinitePhaseRight L c hL)) (originalDetectorFinitePhaseLeft L c hL),
     inner ℂ (A (originalDetectorFinitePhaseRight L c hL)) (originalDetectorFinitePhaseRight L c hL)]

/-- Four-term Hermitian evaluation, retaining every cross term. -/
def originalDetectorFinitePhaseMatrixValue (M : Matrix (Fin 2) (Fin 2) ℂ) (z : Fin 2 → ℂ) : ℂ :=
  conj (z 0) * z 0 * M 0 0 + conj (z 0) * z 1 * M 0 1 +
    conj (z 1) * z 0 * M 1 0 + conj (z 1) * z 1 * M 1 1

theorem originalDetectorFinitePhasePlane_inner_eq_Gram
    (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :
    inner ℂ (originalDetectorFinitePhasePlaneVector L c hL z)
      (originalDetectorFinitePhasePlaneVector L c hL z) =
        originalDetectorFinitePhaseMatrixValue (originalDetectorFinitePhaseGram L c hL) z := by
  simp only [originalDetectorFinitePhasePlaneVector, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, originalDetectorFinitePhaseMatrixValue,
    originalDetectorFinitePhaseGram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem originalDetectorFinitePhasePlane_inner_eq_nativeEnergy
    (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :
    inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorFinitePhasePlaneVector L c hL z))
      (originalDetectorFinitePhasePlaneVector L c hL z) =
        originalDetectorFinitePhaseMatrixValue (originalDetectorFinitePhaseNativeEnergy L c hL) z := by
  simp only [originalDetectorFinitePhasePlaneVector, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, originalDetectorFinitePhaseMatrixValue,
    originalDetectorFinitePhaseNativeEnergy, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The exact generalized Rayleigh identity uses the full actual Gram
denominator and full actual native energy numerator. No Gram cross term,
normalization factor or native energy cross term is discarded. -/
theorem originalDetectorFinitePhasePlane_rayleigh_identity
    (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :
    (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorFinitePhasePlaneVector L c hL z))
        (originalDetectorFinitePhasePlaneVector L c hL z)).re /
      ‖originalDetectorFinitePhasePlaneVector L c hL z‖ ^ 2 =
    (originalDetectorFinitePhaseMatrixValue (originalDetectorFinitePhaseNativeEnergy L c hL) z).re /
      (originalDetectorFinitePhaseMatrixValue (originalDetectorFinitePhaseGram L c hL) z).re := by
  rw [originalDetectorFinitePhasePlane_inner_eq_nativeEnergy]
  have hn : ‖originalDetectorFinitePhasePlaneVector L c hL z‖ ^ 2 =
      (originalDetectorFinitePhaseMatrixValue (originalDetectorFinitePhaseGram L c hL) z).re :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (originalDetectorFinitePhasePlaneVector L c hL z)).trans
      (congrArg Complex.re (originalDetectorFinitePhasePlane_inner_eq_Gram L c hL z))
  rw [hn]

/-- The actual two-lobe phase vector in the full plane. -/
def originalDetectorFinitePhaseVector (σ L c : ℝ) (hL : 0 < L) :=
  originalDetectorFinitePhaseLeft L c hL + (σ : ℂ) • originalDetectorFinitePhaseRight L c hL

theorem originalDetectorFinitePhaseVector_eq_planeVector (σ L c : ℝ) (hL : 0 < L) :
    originalDetectorFinitePhaseVector σ L c hL =
      originalDetectorFinitePhasePlaneVector L c hL ![1, (σ : ℂ)] := by
  simp [originalDetectorFinitePhaseVector, originalDetectorFinitePhasePlaneVector]

/-- The phase endpoints retain all four native energy terms. -/
theorem originalDetectorFinitePhaseVector_nativeEnergy (σ L c : ℝ) (hL : 0 < L) :
    inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorFinitePhaseVector σ L c hL)) (originalDetectorFinitePhaseVector σ L c hL) =
      originalDetectorFinitePhaseNativeEnergy L c hL 0 0 +
        (σ : ℂ) * originalDetectorFinitePhaseNativeEnergy L c hL 0 1 +
        (σ : ℂ) * originalDetectorFinitePhaseNativeEnergy L c hL 1 0 +
        (σ : ℂ) ^ 2 * originalDetectorFinitePhaseNativeEnergy L c hL 1 1 := by
  rw [originalDetectorFinitePhaseVector_eq_planeVector,
    originalDetectorFinitePhasePlane_inner_eq_nativeEnergy]
  simp [originalDetectorFinitePhaseMatrixValue, pow_two]

/-- Canonical exact circulant Gram identity for the required padded image. -/
alias originalDetectorPhaseGram_eq := originalDetectorPaddedFinitePhaseGram_circulant

/-- Canonical exact circulant native-energy identity before minimization. -/
alias originalDetectorPhaseEnergy_eq := originalDetectorPaddedFinitePhaseEnergy_circulant

/-- The complete generalized Rayleigh quotient retains the full Gram and energy. -/
alias originalDetectorPhaseRayleigh_eq := originalDetectorPaddedFinitePhasePlane_rayleigh_identity

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFinitePhasePlane_inner_eq_Gram
#print axioms Zeta23.CCM.originalDetectorFinitePhasePlane_inner_eq_nativeEnergy
#print axioms Zeta23.CCM.originalDetectorFinitePhasePlane_rayleigh_identity
#print axioms Zeta23.CCM.originalDetectorFinitePhaseVector_nativeEnergy
#print axioms Zeta23.CCM.originalDetectorPhaseGram_eq
#print axioms Zeta23.CCM.originalDetectorPhaseEnergy_eq
#print axioms Zeta23.CCM.originalDetectorPhaseRayleigh_eq
