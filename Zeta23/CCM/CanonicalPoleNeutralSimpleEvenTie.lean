import Zeta23.CCM.CanonicalPoleNeutralIndexRigidity
import Zeta23.CCM.CanonicalPoleNeutralSourceMoment
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The actual finite centered-index obstruction at a simple even spectral tie.

All operators, kernels, metrics, and source pairings below are the existing
native ones. At a relative odd ground eigenvalue, zero fourth moment forces
the odd shifted energy to vanish. Simplicity of the actual even eigenspace
would then turn the actual squared index into a scalar eigenvector, which
the finite moment recurrence excludes on the legal carrier.

Neither a tie nor simplicity is asserted to hold. The conclusion concerns
the fourth moment; no corrected-source nonvanishing at a tie is asserted.
-/

section PositiveNullEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A positive operator kills a vector of zero quadratic energy. -/
theorem nativePositive_apply_eq_zero_of_energy_eq_zero
    (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (w : E)
    (hw : (inner ℂ (T w) w).re = 0) : T w = 0 := by
  classical
  by_contra hne
  let a : ℝ := ‖T w‖ ^ 2
  let b : ℝ := (inner ℂ (T (T w)) (T w)).re
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := hT.2 (T w)
  have hn : (inner ℂ (T w) (T w)).re = a := by
    simpa only [a, RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (T w)).symm
  have hquad (t : ℝ) : 0 ≤ b * t ^ 2 + 2 * a * t := by
    have hp := hT.2 ((t : ℂ) • T w + w)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_real_left, inner_smul_real_right] at hp
    rw [hT.1 (T w) w] at hp
    simp only [RCLike.re_eq_complex_re, Complex.add_re, Complex.smul_re,
      smul_eq_mul, hw, hn] at hp
    dsimp only [b]
    nlinarith
  let t : ℝ := -a / (b + 1)
  have hd : 0 < b + 1 := by linarith
  have ht : t < 0 := div_neg_of_neg_of_pos (by linarith) hd
  have hmul : t * (b + 1) = -a := div_mul_cancel₀ _ hd.ne'
  have hlin : 0 < b * t + 2 * a := by nlinarith
  have hneg : t * (b * t + 2 * a) < 0 := mul_neg_of_neg_of_pos ht hlin
  have hp := hquad t
  nlinarith

end PositiveNullEnergy

/-- The actual ambient centered-index matrix is symmetric. -/
theorem euclideanCenteredIndex_isSymmetric (K : ℕ) :
    LinearMap.IsSymmetric (euclideanIndexLinearMap K) := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  rw [indexMatrix, Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

/-- Erase the native and legal output subtypes of the unchanged index map. -/
theorem coe_poleNeutralIndexLinearMap {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    ((poleNeutralIndexLinearMap hL K u).val : EuclideanSpace ℂ (Fin (2 * K + 1))) =
      euclideanIndexLinearMap K (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := rfl

/-- When its fourth moment vanishes, the actual ambient second index iterate
is again in the native even pole kernel. -/
def poleNeutralEvenIndexSquareOfMomentFourZero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K)
    (h4 : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    poleNeutralEvenSubspace L K := by
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
    euclideanIndexLinearMap K (euclideanIndexLinearMap K u.val)
  have hxraw : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x =
      indexMatrix K *ᵥ (indexMatrix K *ᵥ evenBoundaryFlatRawCoefficients K u.val) := by
    dsimp only [x]
    rw [euclideanIndexLinearMap_coordinates, euclideanIndexLinearMap_coordinates]
  have hxlegal : x ∈ euclideanEvenBoundaryFlatSubspace K := by
    rw [mem_euclideanEvenBoundaryFlatSubspace_iff, hxraw]
    exact indexMatrix_sq_mem_evenBoundaryFlat_of_momentFour_eq_zero K _
      ((mem_euclideanEvenBoundaryFlatSubspace_iff K u.val).mp u.val.property) h4
  let xe : euclideanEvenBoundaryFlatSubspace K := ⟨x, hxlegal⟩
  refine ⟨xe, ?_⟩
  rw [mem_poleNeutralEvenSubspace]
  change poleEvenProfile L K ⬝ᵥ ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0
  rw [hxraw]
  exact poleEvenProfile_dot_indexMatrix_sq_eq_zero hL K _
    (evenBoundaryFlatRawCoefficients_boundaryFlat K u.val).1
    ((mem_poleNeutralEvenSubspace L K u.val).mp u.property)

theorem coe_poleNeutralEvenIndexSquareOfMomentFourZero {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K)
    (h4 : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    ((poleNeutralEvenIndexSquareOfMomentFourZero hL K u h4).val :
        EuclideanSpace ℂ (Fin (2 * K + 1))) =
      euclideanIndexLinearMap K (euclideanIndexLinearMap K
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) := rfl

/-- The actual adjoint product equals the actual ambient index square
pointwise under the fourth-moment condition. -/
theorem poleNeutralIndex_adjoint_index_eq_square_of_momentFour_eq_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : poleNeutralEvenSubspace L K)
    (h4 : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralIndexLinearMap hL K u) =
      poleNeutralEvenIndexSquareOfMomentFourZero hL K u h4 := by
  apply ext_inner_right ℂ
  intro v
  rw [LinearMap.adjoint_inner_left]
  simp only [Submodule.coe_inner, coe_poleNeutralIndexLinearMap,
    coe_poleNeutralEvenIndexSquareOfMomentFourZero]
  exact (euclideanCenteredIndex_isSymmetric K
    (euclideanIndexLinearMap K (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))
    (v.val : EuclideanSpace ℂ (Fin (2 * K + 1)))).symm

/-- Ambient value of the preceding actual adjoint identity. -/
theorem coe_poleNeutralIndex_adjoint_index_eq_ambient_square_of_momentFour_eq_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : poleNeutralEvenSubspace L K)
    (h4 : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    (((poleNeutralIndexLinearMap hL K).adjoint (poleNeutralIndexLinearMap hL K u)).val :
        EuclideanSpace ℂ (Fin (2 * K + 1))) =
      euclideanIndexLinearMap K (euclideanIndexLinearMap K
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
  rw [poleNeutralIndex_adjoint_index_eq_square_of_momentFour_eq_zero hL K u h4,
    coe_poleNeutralEvenIndexSquareOfMomentFourZero]

/-- A real shift at or below the actual odd bottom gives an actual positive
native odd operator. -/
theorem poleNeutralOddShifted_isPositive_of_le_bottom {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (λ : ℝ)
    (hλ : λ ≤ poleNeutralOddRayleighBottom L K hL hK) :
    LinearMap.IsPositive (poleNeutralOddCompressedCanonical L K -
      (λ : ℂ) • LinearMap.id) := by
  refine ⟨(poleNeutralOddCompressedCanonical_isSymmetric L K).sub
    (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id), ?_⟩
  intro w
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK w
  have hn : (inner ℂ w w).re = ‖w‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, inner_smul_real_left, Complex.sub_re, Complex.smul_re,
    smul_eq_mul, RCLike.re_eq_complex_re, hn]
  have hs : λ * ‖w‖ ^ 2 ≤ poleNeutralOddRayleighBottom L K hL hK * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hλ (sq_nonneg _)
  linarith

/-- The rank-one identity and zero fourth moment put the actual index image
in the odd eigenspace whenever the even eigenvalue lies below the odd bottom. -/
theorem poleNeutralIndex_odd_eigen_of_momentFour_eq_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (λ : ℝ) (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (λ : ℂ) • u)
    (hλ : λ ≤ poleNeutralOddRayleighBottom L K hL hK)
    (h4 : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u) =
      (λ : ℂ) • poleNeutralIndexLinearMap hL K u := by
  have he := poleNeutral_source_moment_energy_eq hL K (by omega) λ u hu
  rw [h4, mul_zero, Complex.zero_re] at he
  have hz := nativePositive_apply_eq_zero_of_energy_eq_zero
    (poleNeutralOddCompressedCanonical L K - (λ : ℂ) • LinearMap.id)
    (poleNeutralOddShifted_isPositive_of_le_bottom hL K hK λ hλ)
    (poleNeutralIndexLinearMap hL K u) he.symm
  exact sub_eq_zero.mp hz

/-- With zero fourth moment, the actual adjoint product remains in the even
eigenspace. The source term vanishes by its actual cubic pairing. -/
theorem poleNeutralIndex_adjoint_index_even_eigen_of_momentFour_eq_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (λ : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (λ : ℂ) • u)
    (hλ : λ ≤ poleNeutralOddRayleighBottom L K hL hK)
    (h4 : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = 0) :
    poleNeutralEvenCompressedCanonical L K
      ((poleNeutralIndexLinearMap hL K).adjoint (poleNeutralIndexLinearMap hL K u)) =
        (λ : ℂ) • (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralIndexLinearMap hL K u) := by
  let D : poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K :=
    poleNeutralIndexLinearMap hL K
  let A : poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K :=
    poleNeutralEvenCompressedCanonical L K
  let B : poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K :=
    poleNeutralOddCompressedCanonical L K
  have hBDu : B (D u) = (λ : ℂ) • D u :=
    poleNeutralIndex_odd_eigen_of_momentFour_eq_zero hL K hK λ u hu hλ h4
  have hpair : inner ℂ (D u) (poleNeutralCubicCompressionVector L K) = 0 := by
    apply inner_eq_zero_symm.mp
    rw [poleNeutral_cubic_pairing_eq_momentFour hL K u, h4]
  apply ext_inner_right ℂ
  intro v
  have hDA : D (A v) = B (D v) -
      poleNeutralCorrectedCubicSource L K v • poleNeutralCubicCompressionVector L K := by
    have hr := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) v
    simp only [poleNeutralCompressedIndexDefect, LinearMap.sub_apply, LinearMap.comp_apply] at hr
    rw [← hr]
    abel
  calc
    _ = inner ℂ (D.adjoint (D u)) (A v) :=
      poleNeutralEvenCompressedCanonical_isSymmetric L K _ v
    _ = inner ℂ (D u) (D (A v)) := LinearMap.adjoint_inner_left D (A v) (D u)
    _ = inner ℂ (D u) (B (D v)) := by
      rw [hDA, inner_sub_right, inner_smul_right, hpair, mul_zero, sub_zero]
    _ = inner ℂ (B (D u)) (D v) :=
      (poleNeutralOddCompressedCanonical_isSymmetric L K (D u) (D v)).symm
    _ = _ := by
      simp only [hBDu, inner_smul_left, Complex.conj_ofReal, LinearMap.adjoint_inner_left]

/-- At or below the odd bottom, a nonzero eigenmode in a simple actual even
eigenspace must have nonzero fourth moment. -/
theorem poleNeutral_momentFour_ne_zero_of_simple_even_of_le_odd_bottom
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (λ : ℝ)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (λ : ℂ) • u)
    (hλ : λ ≤ poleNeutralOddRayleighBottom L K hL hK)
    (hsimple : Module.finrank ℂ
      (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (λ : ℂ)) = 1) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0 := by
  intro h4
  let v := (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralIndexLinearMap hL K u)
  have hv : poleNeutralEvenCompressedCanonical L K v = (λ : ℂ) • v :=
    poleNeutralIndex_adjoint_index_even_eigen_of_momentFour_eq_zero hL K hK λ u hu hλ h4
  let ue : Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (λ : ℂ) :=
    ⟨u, Module.End.mem_eigenspace_iff.mpr hu⟩
  have hue : ue ≠ 0 := fun hz => hu0 (congrArg Subtype.val hz)
  let ve : Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (λ : ℂ) :=
    ⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ue hue).mp hsimple ve
  have hcv : c • u = v := congrArg Subtype.val hc
  have hambient : euclideanIndexLinearMap K (euclideanIndexLinearMap K
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        c • (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
    have hsq := coe_poleNeutralIndex_adjoint_index_eq_ambient_square_of_momentFour_eq_zero
      hL K u h4
    rw [← hcv] at hsq
    exact hsq.symm
  have huval : u.val = 0 := evenBoundaryFlat_eq_zero_of_euclideanIndex_sq_eigen K c u.val hambient
  exact hu0 (Subtype.ext huval)

/-- The simple actual even ground eigenspace cannot have silent fourth
moment at a common native parity bottom. -/
theorem poleNeutral_simpleEven_tie_momentFour_ne_zero {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (htie : poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK)
    (hsimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0 :=
  poleNeutral_momentFour_ne_zero_of_simple_even_of_le_odd_bottom hL K hK _ u hu0 hu
    htie.le hsimple

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositive_apply_eq_zero_of_energy_eq_zero
#print axioms Zeta23.CCM.euclideanCenteredIndex_isSymmetric
#print axioms Zeta23.CCM.poleNeutralEvenIndexSquareOfMomentFourZero
#print axioms Zeta23.CCM.poleNeutralIndex_adjoint_index_eq_square_of_momentFour_eq_zero
#print axioms Zeta23.CCM.coe_poleNeutralIndex_adjoint_index_eq_ambient_square_of_momentFour_eq_zero
#print axioms Zeta23.CCM.poleNeutralOddShifted_isPositive_of_le_bottom
#print axioms Zeta23.CCM.poleNeutralIndex_odd_eigen_of_momentFour_eq_zero
#print axioms Zeta23.CCM.poleNeutralIndex_adjoint_index_even_eigen_of_momentFour_eq_zero
#print axioms Zeta23.CCM.poleNeutral_momentFour_ne_zero_of_simple_even_of_le_odd_bottom
#print axioms Zeta23.CCM.poleNeutral_simpleEven_tie_momentFour_ne_zero
