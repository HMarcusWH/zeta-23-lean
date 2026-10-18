import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormalization
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseWeilPadding
import Zeta23.ExceptionalZero.BoundaryFlatFiniteWeil

/-! # Exact native-energy transport of the actual normalized finite phase -/

noncomputable section

open Set Complex Matrix
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

private theorem localizedFiniteVector_smul_eq (L : ℝ) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ) :
    localizedFiniteVector L K (z • u) = fun x => z * localizedFiniteVector L K u x := by
  funext x
  unfold localizedFiniteVector
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem re_inner_apply_smul_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) (v : E) (t : ℝ) :
    (inner ℂ (A ((t : ℂ) • v)) ((t : ℂ) • v)).re = t ^ 2 * (inner ℂ (A v) v).re := by
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero]
  ring

/-- The original physical normalization scales the actual native energy
by exactly `η²`, using the unchanged genuine finite Weil/matrix identity. -/
theorem originalDetectorPaddedFiniteOriginalPhaseHard_Weil_re_eq_nativeEnergy
    {a : ℝ} (ha : 0 ≤ a) (σ : ℝ) (hLp : 0 < fixedOriginalSincTrialAperture a) :
    (zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)
      (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)).re =
      fixedOriginalSincTrialNormalization ^ 2 *
        (inner ℂ ((canonicalSourceMatrix (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))).toEuclideanLin
          (originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hLp))
          (originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hLp)).re := by
  let L := fixedOriginalSincTrialAperture a
  let K := originalDetectorQuarticCutoff L
  let v := originalDetectorPaddedFinitePhaseVector σ L fixedOriginalSincLobeCenter hLp
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) v
  let η := fixedOriginalSincTrialNormalization
  have hL2 : 2 ≤ L := by
    dsimp [L, fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter]
    linarith [UniversalSinc.fixedScale_pos]
  have hflat : BoundaryFlatCoefficients K u := by
    dsimp [u, v]
    rw [originalDetectorPaddedFinitePhaseVector_raw]
    exact originalDetectorPaddedFinitePhaseRaw_boundaryFlat σ _ hL2
  have hflatScaled : BoundaryFlatCoefficients K ((η : ℂ) • u) := by
    apply (mem_boundaryFlatSubspace_iff _ _).mp
    apply (boundaryFlatSubspace K).smul_mem
    exact (mem_boundaryFlatSubspace_iff _ _).mpr hflat
  have hp : localizedFiniteVector L K ((η : ℂ) • u) =
      originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp := localizedFiniteVector_smul_eq L K u η
  have hW := congrArg Complex.re
    (zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm K ((η : ℂ) • u) hLp hflatScaled)
  rw [hp] at hW
  have hquad : (quadraticForm (canonicalSourceMatrix L K) ((η : ℂ) • u)).re =
      (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin ((η : ℂ) • v)) ((η : ℂ) • v)).re := by
    simpa only [map_smul] using
      quadraticForm_re_eq_re_inner_apply_self (canonicalSourceMatrix L K) ((η : ℂ) • v)
  exact hW.trans (hquad.trans (re_inner_apply_smul_self _ v η))

/-- Unit native energy is the genuine finite physical Weil energy divided
by its proved actual physical mass. The nonzero vector is supplied later
by the constructed cofinal normalization threshold. -/
theorem originalDetectorPaddedFinitePhaseUnitVector_nativeEnergy_eq_Weil_div_mass
    {a : ℝ} (ha : 0 ≤ a) (σ : ℝ) (hLp : 0 < fixedOriginalSincTrialAperture a)
    (hv : originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a)
      fixedOriginalSincLobeCenter hLp ≠ 0) :
    (inner ℂ ((canonicalSourceMatrix (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))).toEuclideanLin
      (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hLp))
      (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hLp)).re =
    (zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)
      (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)).re /
      (fixedOriginalSincTrialNormalization ^ 2 *
        ‖originalDetectorPaddedFinitePhaseVector σ (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hLp‖ ^ 2) := by
  rw [originalDetectorPaddedFiniteOriginalPhaseHard_Weil_re_eq_nativeEnergy ha]
  unfold originalDetectorPaddedFinitePhaseUnitVector
  rw [re_inner_apply_smul_self]
  have hη := fixedOriginalSincTrialNormalization_pos.ne'
  have hn := norm_ne_zero_iff.mpr hv
  field_simp

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteOriginalPhaseHard_Weil_re_eq_nativeEnergy
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseUnitVector_nativeEnergy_eq_Weil_div_mass
