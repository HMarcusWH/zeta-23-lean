import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseSymmetry
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormalization

/-! The real scalar quotient of the actual full padded two-lobe trial plane. -/

noncomputable section

open Complex Matrix
open scoped ComplexConjugate

namespace Zeta23.CCM

def originalDetectorPaddedPhaseNu (L c : ℝ) (hL : 0 < L) : ℝ :=
  (originalDetectorPaddedFinitePhaseGram L c hL 0 0).re
def originalDetectorPaddedPhaseOmega (L c : ℝ) (hL : 0 < L) : ℝ :=
  (originalDetectorPaddedFinitePhaseGram L c hL 0 1).re
def originalDetectorPaddedPhaseD (L c : ℝ) (hL : 0 < L) : ℝ :=
  (originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 0).re
def originalDetectorPaddedPhaseC (L c : ℝ) (hL : 0 < L) : ℝ :=
  (originalDetectorPaddedFinitePhaseNativeEnergy L c hL 0 1).re

private theorem circulant_real (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hc : M = !![M 0 0, M 0 1; M 0 1, M 0 0])
    (hh : ∀ i j, conj (M i j) = M j i) :
    M = !![((M 0 0).re : ℂ), ((M 0 1).re : ℂ); ((M 0 1).re : ℂ), ((M 0 0).re : ℂ)] := by
  have h10 : M 1 0 = M 0 1 := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hc
    simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using he
  have h00 : ((M 0 0).re : ℂ) = M 0 0 := Complex.conj_eq_iff_re.mp (hh 0 0)
  have h01 : ((M 0 1).re : ℂ) = M 0 1 := Complex.conj_eq_iff_re.mp ((hh 0 1).trans h10)
  exact hc.trans (congrArg₂ (fun a b : ℂ => !![a, b; b, a]) h00.symm h01.symm)

theorem originalDetectorPaddedPhaseGram_real (L c : ℝ) (hL : 0 < L) :
    originalDetectorPaddedFinitePhaseGram L c hL =
      !![(originalDetectorPaddedPhaseNu L c hL : ℂ), (originalDetectorPaddedPhaseOmega L c hL : ℂ);
        (originalDetectorPaddedPhaseOmega L c hL : ℂ), (originalDetectorPaddedPhaseNu L c hL : ℂ)] := by
  apply circulant_real _ (originalDetectorPaddedFinitePhaseGram_circulant L c hL)
  have hh (u v : EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1))) :
      conj (inner ℂ u v) = inner ℂ v u := inner_conj_symm v u
  intro i j
  fin_cases i <;> fin_cases j <;> exact hh _ _

theorem originalDetectorPaddedPhaseEnergy_real (L c : ℝ) (hL : 0 < L) :
    originalDetectorPaddedFinitePhaseNativeEnergy L c hL =
      !![(originalDetectorPaddedPhaseD L c hL : ℂ), (originalDetectorPaddedPhaseC L c hL : ℂ);
        (originalDetectorPaddedPhaseC L c hL : ℂ), (originalDetectorPaddedPhaseD L c hL : ℂ)] := by
  apply circulant_real _ (originalDetectorPaddedFinitePhaseEnergy_circulant L c hL)
  have hh (u v : EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1))) :
      conj (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin u) v) =
        inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin v) u := by
    rw [inner_conj_symm]
    exact (canonicalSourceMatrix_toEuclideanLin_isSymmetric L _ v u).symm
  intro i j
  fin_cases i <;> fin_cases j <;> exact hh _ _

theorem originalDetectorPaddedPhase_norm_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (L c : ℝ) (hL : 0 < L) :
    ‖originalDetectorPaddedFinitePhaseVector σ L c hL‖ ^ 2 =
      2 * (originalDetectorPaddedPhaseNu L c hL + σ * originalDetectorPaddedPhaseOmega L c hL) := by
  have hh := norm_sq_eq_re_inner (𝕜 := ℂ) (originalDetectorPaddedFinitePhaseVector σ L c hL)
  rw [originalDetectorPaddedFinitePhaseVector_eq_planeVector,
    originalDetectorPaddedFinitePhasePlane_inner_eq_Gram, originalDetectorPaddedPhaseGram_real] at hh
  rw [originalDetectorPaddedFinitePhaseVector_eq_planeVector]
  rcases hσ with rfl | rfl <;>
    simp [originalDetectorPaddedFinitePhaseMatrixValue] at hh ⊢ <;> linarith

theorem originalDetectorPaddedPhase_energy {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (L c : ℝ) (hL : 0 < L) :
    (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorPaddedFinitePhaseVector σ L c hL)) (originalDetectorPaddedFinitePhaseVector σ L c hL)).re =
      2 * (originalDetectorPaddedPhaseD L c hL + σ * originalDetectorPaddedPhaseC L c hL) := by
  rw [originalDetectorPaddedFinitePhaseVector_eq_planeVector,
    originalDetectorPaddedFinitePhasePlane_inner_eq_nativeEnergy, originalDetectorPaddedPhaseEnergy_real]
  rcases hσ with rfl | rfl <;> simp [originalDetectorPaddedFinitePhaseMatrixValue] <;> ring

theorem originalDetectorPaddedPhase_denominator_pos {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (L c : ℝ) (hL : 0 < L) (hv : originalDetectorPaddedFinitePhaseVector σ L c hL ≠ 0) :
    0 < originalDetectorPaddedPhaseNu L c hL + σ * originalDetectorPaddedPhaseOmega L c hL := by
  have hn := originalDetectorPaddedPhase_norm_sq hσ L c hL
  have hp := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith

theorem originalDetectorPaddedPhase_scalar_quotient {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (L c : ℝ) (hL : 0 < L) :
    (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
      (originalDetectorPaddedFinitePhaseVector σ L c hL)) (originalDetectorPaddedFinitePhaseVector σ L c hL)).re /
        ‖originalDetectorPaddedFinitePhaseVector σ L c hL‖ ^ 2 =
      (originalDetectorPaddedPhaseD L c hL + σ * originalDetectorPaddedPhaseC L c hL) /
        (originalDetectorPaddedPhaseNu L c hL + σ * originalDetectorPaddedPhaseOmega L c hL) := by
  rw [originalDetectorPaddedPhase_energy hσ, originalDetectorPaddedPhase_norm_sq hσ]
  exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)

theorem exists_originalDetectorPaddedPhase_positive_denominators :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ (a : ℝ) (ha : UniversalSinc.fixedScale < a)
      (hL : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a),
      L0 ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a →
      0 < originalDetectorPaddedPhaseNu (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hL +
        originalDetectorPaddedPhaseOmega (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hL ∧
      0 < originalDetectorPaddedPhaseNu (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hL -
        originalDetectorPaddedPhaseOmega (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hL := by
  obtain ⟨L0, hL0, hunit⟩ := exists_originalDetectorPaddedFinitePhase_unit_threshold
  refine ⟨L0, hL0, ?_⟩
  intro a ha hL hlarge
  have he := (hunit 1 a (Or.inl rfl) ha hL hlarge).1
  have ho := (hunit (-1) a (Or.inr rfl) ha hL hlarge).1
  constructor
  · simpa using originalDetectorPaddedPhase_denominator_pos (Or.inl rfl) _ _ hL he
  · simpa using originalDetectorPaddedPhase_denominator_pos (Or.inr rfl) _ _ hL ho

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedPhaseGram_real
#print axioms Zeta23.CCM.originalDetectorPaddedPhaseEnergy_real
#print axioms Zeta23.CCM.originalDetectorPaddedPhase_norm_sq
#print axioms Zeta23.CCM.originalDetectorPaddedPhase_energy
#print axioms Zeta23.CCM.originalDetectorPaddedPhase_denominator_pos
#print axioms Zeta23.CCM.originalDetectorPaddedPhase_scalar_quotient
#print axioms Zeta23.CCM.exists_originalDetectorPaddedPhase_positive_denominators
