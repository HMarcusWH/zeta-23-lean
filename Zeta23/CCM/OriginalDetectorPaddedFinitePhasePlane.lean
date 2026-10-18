import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageNonzero
import Zeta23.CCM.OriginalDetectorFinitePhysicalNorm

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

def originalDetectorPaddedFinitePhaseLeft (L c : ℝ) (hL : 0 < L) :
    EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1)) :=
  WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL)

def originalDetectorPaddedFinitePhaseRight (L c : ℝ) (hL : 0 < L) :
    EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1)) :=
  WithLp.toLp 2 (reverseCoefficients (originalDetectorQuarticCutoff L)
    (originalDetectorPaddedFinitePoleImageCoefficients UniversalSinc.fixedScale L c hL))

/-- The actual two-coordinate linear combination before any minimization. -/
def originalDetectorPaddedFinitePhasePlaneVector (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :=
  z 0 • originalDetectorPaddedFinitePhaseLeft L c hL + z 1 • originalDetectorPaddedFinitePhaseRight L c hL

/-- All four actual Gram entries, including the unreduced cross terms. -/
def originalDetectorPaddedFinitePhaseGram (L c : ℝ) (hL : 0 < L) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ (originalDetectorPaddedFinitePhaseLeft L c hL) (originalDetectorPaddedFinitePhaseLeft L c hL),
     inner ℂ (originalDetectorPaddedFinitePhaseLeft L c hL) (originalDetectorPaddedFinitePhaseRight L c hL);
     inner ℂ (originalDetectorPaddedFinitePhaseRight L c hL) (originalDetectorPaddedFinitePhaseLeft L c hL),
     inner ℂ (originalDetectorPaddedFinitePhaseRight L c hL) (originalDetectorPaddedFinitePhaseRight L c hL)]

/-- All four entries of the unchanged actual canonical native energy. -/
def originalDetectorPaddedFinitePhaseNativeEnergy (L c : ℝ) (hL : 0 < L) : Matrix (Fin 2) (Fin 2) ℂ :=
  let A := (canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
  !![inner ℂ (A (originalDetectorPaddedFinitePhaseLeft L c hL)) (originalDetectorPaddedFinitePhaseLeft L c hL),
     inner ℂ (A (originalDetectorPaddedFinitePhaseLeft L c hL)) (originalDetectorPaddedFinitePhaseRight L c hL);
     inner ℂ (A (originalDetectorPaddedFinitePhaseRight L c hL)) (originalDetectorPaddedFinitePhaseLeft L c hL),
     inner ℂ (A (originalDetectorPaddedFinitePhaseRight L c hL)) (originalDetectorPaddedFinitePhaseRight L c hL)]

/-- Four-term Hermitian evaluation, retaining every cross term. -/
def originalDetectorPaddedFinitePhaseMatrixValue (M : Matrix (Fin 2) (Fin 2) ℂ) (z : Fin 2 → ℂ) : ℂ :=
  conj (z 0) * z 0 * M 0 0 + conj (z 0) * z 1 * M 0 1 +
    conj (z 1) * z 0 * M 1 0 + conj (z 1) * z 1 * M 1 1

theorem originalDetectorPaddedFinitePhasePlane_inner_eq_Gram
    (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :
    inner ℂ (originalDetectorPaddedFinitePhasePlaneVector L c hL z)
      (originalDetectorPaddedFinitePhasePlaneVector L c hL z) =
        originalDetectorPaddedFinitePhaseMatrixValue (originalDetectorPaddedFinitePhaseGram L c hL) z := by
  simp only [originalDetectorPaddedFinitePhasePlaneVector, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, originalDetectorPaddedFinitePhaseMatrixValue,
    originalDetectorPaddedFinitePhaseGram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem originalDetectorPaddedFinitePhasePlane_inner_eq_nativeEnergy
    (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :
    inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorPaddedFinitePhasePlaneVector L c hL z))
      (originalDetectorPaddedFinitePhasePlaneVector L c hL z) =
        originalDetectorPaddedFinitePhaseMatrixValue (originalDetectorPaddedFinitePhaseNativeEnergy L c hL) z := by
  simp only [originalDetectorPaddedFinitePhasePlaneVector, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, originalDetectorPaddedFinitePhaseMatrixValue,
    originalDetectorPaddedFinitePhaseNativeEnergy, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The exact generalized Rayleigh identity uses the full actual Gram
denominator and full actual native energy numerator. No Gram cross term,
normalization factor or native energy cross term is discarded. -/
theorem originalDetectorPaddedFinitePhasePlane_rayleigh_identity
    (L c : ℝ) (hL : 0 < L) (z : Fin 2 → ℂ) :
    (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorPaddedFinitePhasePlaneVector L c hL z))
        (originalDetectorPaddedFinitePhasePlaneVector L c hL z)).re /
      ‖originalDetectorPaddedFinitePhasePlaneVector L c hL z‖ ^ 2 =
    (originalDetectorPaddedFinitePhaseMatrixValue (originalDetectorPaddedFinitePhaseNativeEnergy L c hL) z).re /
      (originalDetectorPaddedFinitePhaseMatrixValue (originalDetectorPaddedFinitePhaseGram L c hL) z).re := by
  rw [originalDetectorPaddedFinitePhasePlane_inner_eq_nativeEnergy]
  have hn : ‖originalDetectorPaddedFinitePhasePlaneVector L c hL z‖ ^ 2 =
      (originalDetectorPaddedFinitePhaseMatrixValue (originalDetectorPaddedFinitePhaseGram L c hL) z).re :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (originalDetectorPaddedFinitePhasePlaneVector L c hL z)).trans
      (congrArg Complex.re (originalDetectorPaddedFinitePhasePlane_inner_eq_Gram L c hL z))
  rw [hn]

/-- The actual two-lobe phase vector in the full plane. -/
def originalDetectorPaddedFinitePhaseVector (σ L c : ℝ) (hL : 0 < L) :=
  originalDetectorPaddedFinitePhaseLeft L c hL + (σ : ℂ) • originalDetectorPaddedFinitePhaseRight L c hL

theorem originalDetectorPaddedFinitePhaseVector_eq_planeVector (σ L c : ℝ) (hL : 0 < L) :
    originalDetectorPaddedFinitePhaseVector σ L c hL =
      originalDetectorPaddedFinitePhasePlaneVector L c hL ![1, (σ : ℂ)] := by
  simp [originalDetectorPaddedFinitePhaseVector, originalDetectorPaddedFinitePhasePlaneVector]

/-- The phase endpoints retain all four native energy terms. -/
theorem originalDetectorPaddedFinitePhaseVector_nativeEnergy (σ L c : ℝ) (hL : 0 < L) :
    inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorPaddedFinitePhaseVector σ L c hL)) (originalDetectorPaddedFinitePhaseVector σ L c hL) =
      originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 0 +
        (σ : ℂ) * originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 1 +
        (σ : ℂ) * originalDetectorPaddedFinitePhaseNativeEnergy L c hL 1 0 +
        (σ : ℂ) ^ 2 * originalDetectorPaddedFinitePhaseNativeEnergy L c hL 1 1 := by
  rw [originalDetectorPaddedFinitePhaseVector_eq_planeVector,
    originalDetectorPaddedFinitePhasePlane_inner_eq_nativeEnergy]
  simp [originalDetectorPaddedFinitePhaseMatrixValue, pow_two]

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhasePlane_inner_eq_Gram
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhasePlane_inner_eq_nativeEnergy
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhasePlane_rayleigh_identity
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseVector_nativeEnergy
