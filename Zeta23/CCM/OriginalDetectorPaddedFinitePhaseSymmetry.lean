import Zeta23.CCM.OriginalDetectorPaddedFinitePhasePlane

/-! Exact circulant Gram and native energy matrices of the actual padded lobes. -/

noncomputable section

open Complex Matrix
open scoped ComplexConjugate

namespace Zeta23.CCM

private theorem actualReverse_inner (K : ℕ) (u v : Fin (2 * K + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (reverseCoefficients K u))
      (WithLp.toLp 2 (reverseCoefficients K v)) =
        inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [reverseCoefficients, Fin.revPerm_apply]

private theorem actualReverse_cross (K : ℕ) (u v : Fin (2 * K + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (reverseCoefficients K u)) (WithLp.toLp 2 v) =
      inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 (reverseCoefficients K v)) := by
  have he := actualReverse_inner K u (reverseCoefficients K v)
  simpa only [reverseCoefficients_reverseCoefficients] using he

private theorem actualReverse_canonical (L : ℝ) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    (canonicalSourceMatrix L K).toEuclideanLin (WithLp.toLp 2 (reverseCoefficients K u)) =
      WithLp.toLp 2 (reverseCoefficients K (canonicalSourceMatrix L K *ᵥ u)) := by
  rw [Matrix.toEuclideanLin_apply_piLp_toLp, canonicalSourceMatrix_mulVec_reverseCoefficients]

theorem originalDetectorPaddedFinitePhaseGram_circulant
    (L c : ℝ) (hL : 0 < L) :
    originalDetectorPaddedFinitePhaseGram L c hL =
      !![originalDetectorPaddedFinitePhaseGram L c hL 0 0,
         originalDetectorPaddedFinitePhaseGram L c hL 0 1;
         originalDetectorPaddedFinitePhaseGram L c hL 0 1,
         originalDetectorPaddedFinitePhaseGram L c hL 0 0] := by
  have hcross : inner ℂ (originalDetectorPaddedFinitePhaseRight L c hL)
      (originalDetectorPaddedFinitePhaseLeft L c hL) =
      inner ℂ (originalDetectorPaddedFinitePhaseLeft L c hL)
        (originalDetectorPaddedFinitePhaseRight L c hL) := by
    exact actualReverse_cross _ _ _
  have hdiag : inner ℂ (originalDetectorPaddedFinitePhaseRight L c hL)
      (originalDetectorPaddedFinitePhaseRight L c hL) =
      inner ℂ (originalDetectorPaddedFinitePhaseLeft L c hL)
        (originalDetectorPaddedFinitePhaseLeft L c hL) := by
    exact actualReverse_inner _ _ _
  simp only [originalDetectorPaddedFinitePhaseGram, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hcross, hdiag]

theorem originalDetectorPaddedFinitePhaseEnergy_circulant
    (L c : ℝ) (hL : 0 < L) :
    originalDetectorPaddedFinitePhaseNativeEnergy L c hL =
      !![originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 0,
         originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 1;
         originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 1,
         originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 0] := by
  have hcross : inner ℂ
      ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseRight L c hL))
      (originalDetectorPaddedFinitePhaseLeft L c hL) =
      inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseLeft L c hL))
      (originalDetectorPaddedFinitePhaseRight L c hL) := by
    unfold originalDetectorPaddedFinitePhaseLeft originalDetectorPaddedFinitePhaseRight
    rw [actualReverse_canonical, Matrix.toEuclideanLin_apply_piLp_toLp]
    exact actualReverse_cross _ _ _
  have hdiag : inner ℂ
      ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseRight L c hL))
      (originalDetectorPaddedFinitePhaseRight L c hL) =
      inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseLeft L c hL))
      (originalDetectorPaddedFinitePhaseLeft L c hL) := by
    unfold originalDetectorPaddedFinitePhaseLeft originalDetectorPaddedFinitePhaseRight
    rw [actualReverse_canonical, Matrix.toEuclideanLin_apply_piLp_toLp]
    exact actualReverse_inner _ _ _
  simp only [originalDetectorPaddedFinitePhaseNativeEnergy, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hcross, hdiag]

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseGram_circulant
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseEnergy_circulant
