import Zeta23.CCM.IsometricDetectorSchur
import Mathlib.Analysis.InnerProductSpace.Symmetric

noncomputable section

namespace Zeta23.OPICARound3

open CCM
open scoped ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem exists_unit_shell (J : E →ₗᵢ[ℂ] F)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1) :
    ∃ e : isometricDetectorComplement J, ‖e‖ = 1 := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show
    0 < Module.finrank ℂ (isometricDetectorComplement J) by omega)
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_⟩
  rw [norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
  change ‖(v : F)‖⁻¹ * ‖(v : F)‖ = 1
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (show (v : F) ≠ 0 from
    fun hz => hv (Subtype.ext hz)))

theorem inner_adjoint_isometry_left (J : E →ₗᵢ[ℂ] F) (x : E) (y : F) :
    inner ℂ (J.toLinearMap.adjoint y) x = inner ℂ y (J x) := by
  simpa only [LinearIsometry.coe_toLinearMap] using!
    (LinearMap.adjoint_inner_left J.toLinearMap x y)

theorem inner_adjoint_isometry_right (J : E →ₗᵢ[ℂ] F) (x : E) (y : F) :
    inner ℂ x (J.toLinearMap.adjoint y) = inner ℂ (J x) y := by
  simpa only [LinearIsometry.coe_toLinearMap] using!
    (LinearMap.adjoint_inner_right J.toLinearMap x y)

def predecessorBlock (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) : E →ₗ[ℂ] E :=
  J.toLinearMap.adjoint.comp (T.comp J.toLinearMap)

theorem predecessorBlock_symmetric (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) : (predecessorBlock J T).IsSymmetric := by
  intro x y
  change inner ℂ (J.toLinearMap.adjoint (T (J x))) y =
    inner ℂ x (J.toLinearMap.adjoint (T (J y)))
  rw [inner_adjoint_isometry_left J y, inner_adjoint_isometry_right J x]
  exact hT (J x) (J y)

theorem exists_kernelOrthogonal_preimage (A : E →ₗ[ℂ] E) (b : E)
    (hb : b ∈ A.range) : ∃ x : E, x ∈ A.kerᗮ ∧ A x = b := by
  obtain ⟨y, hy⟩ := hb
  refine ⟨y - A.ker.starProjection y, A.ker.sub_starProjection_mem_orthogonal y, ?_⟩
  have hz : A (A.ker.starProjection y) = 0 :=
    (LinearMap.mem_ker).mp (A.ker.starProjection_apply_mem y)
  rw [map_sub, hz, sub_zero, hy]

/-- The Moore--Penrose response on the range: the preimage orthogonal to
the predecessor kernel. No inverse of a singular predecessor is assumed. -/
def kernelSafeResponse (A : E →ₗ[ℂ] E) (b : E) (hb : b ∈ A.range) : E :=
  Classical.choose (exists_kernelOrthogonal_preimage A b hb)

theorem kernelSafeResponse_spec (A : E →ₗ[ℂ] E) (b : E) (hb : b ∈ A.range) :
    kernelSafeResponse A b hb ∈ A.kerᗮ ∧ A (kernelSafeResponse A b hb) = b :=
  Classical.choose_spec (exists_kernelOrthogonal_preimage A b hb)

theorem kernelOrthogonal_preimage_unique (A : E →ₗ[ℂ] E) (b : E)
    {x y : E} (hx : x ∈ A.kerᗮ) (hy : y ∈ A.kerᗮ)
    (hAx : A x = b) (hAy : A y = b) : x = y := by
  have hker : x - y ∈ A.ker := by simp [LinearMap.mem_ker, hAx, hAy]
  have horth : x - y ∈ A.kerᗮ := (A.kerᗮ).sub_mem hx hy
  have hz : inner ℂ (x - y) (x - y) = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hker
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hz)

theorem kernel_projection_zero_iff_range (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (b : E) :
    A.ker.starProjection b = 0 ↔ b ∈ A.range := by
  rw [Submodule.starProjection_apply_eq_zero_iff, LinearMap.orthogonal_ker, hA.adjoint_eq]

def oneShellSchurScalar (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T (e : F)) ∈ (predecessorBlock J T).range) : ℝ :=
  (inner ℂ (T (e : F)) (e : F)).re -
    (inner ℂ (J.toLinearMap.adjoint (T (e : F)))
      (kernelSafeResponse (predecessorBlock J T) _ hb)).re

theorem oneShellSchurScalar_of_subsingleton [Subsingleton E]
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T (e : F)) ∈ (predecessorBlock J T).range) :
    oneShellSchurScalar J T e hb = (inner ℂ (T (e : F)) (e : F)).re := by
  have hz : J.toLinearMap.adjoint (T (e : F)) = 0 := Subsingleton.elim _ _
  simp [oneShellSchurScalar, hz]

theorem oneShellSchurScalar_energy (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T (e : F)) ∈ (predecessorBlock J T).range) :
    let r := kernelSafeResponse (predecessorBlock J T) _ hb
    (inner ℂ (T ((e : F) - J r)) ((e : F) - J r)).re =
      oneShellSchurScalar J T e hb := by
  let r := kernelSafeResponse (predecessorBlock J T) _ hb
  have hr := (kernelSafeResponse_spec (predecessorBlock J T) _ hb).2
  change J.toLinearMap.adjoint (T (J r)) = J.toLinearMap.adjoint (T (e : F)) at hr
  have hres : J.toLinearMap.adjoint (T ((e : F) - J r)) = 0 := by
    rw [map_sub, map_sub, hr, sub_self]
  have hcross : inner ℂ (T ((e : F) - J r)) (J r) = 0 := by
    rw [← inner_adjoint_isometry_left J r, hres, inner_zero_left]
  have hreal : inner ℂ r (J.toLinearMap.adjoint (T (e : F))) =
      inner ℂ (J.toLinearMap.adjoint (T (e : F))) r := by
    rw [← hr]
    exact (predecessorBlock_symmetric J T hT r r).symm
  have hid : inner ℂ (T ((e : F) - J r)) ((e : F) - J r) =
      inner ℂ (T (e : F)) (e : F) -
        inner ℂ (J.toLinearMap.adjoint (T (e : F))) r := by
    rw [inner_sub_right, hcross, sub_zero, map_sub, inner_sub_left,
      hT (J r) (e : F), ← inner_adjoint_isometry_right J r, hreal]
  exact congrArg Complex.re hid

/-- Exact regular completion, retaining the actual complex shell coordinate. -/
theorem oneShell_regular_completedSquare (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T (e : F)) ∈ (predecessorBlock J T).range)
    (x : E) (t : ℂ) :
    let r := kernelSafeResponse (predecessorBlock J T) _ hb
    (inner ℂ (T (J x + t • (e : F))) (J x + t • (e : F))).re =
      (inner ℂ (predecessorBlock J T (x + t • r)) (x + t • r)).re +
        ‖t‖ ^ 2 * oneShellSchurScalar J T e hb := by
  let r := kernelSafeResponse (predecessorBlock J T) _ hb
  let q : F := (e : F) - J r
  let z := x + t • r
  have hr := (kernelSafeResponse_spec (predecessorBlock J T) _ hb).2
  change J.toLinearMap.adjoint (T (J r)) = J.toLinearMap.adjoint (T (e : F)) at hr
  have hres : J.toLinearMap.adjoint (T q) = 0 := by
    dsimp only [q]
    rw [map_sub, map_sub, hr, sub_self]
  have hcross : inner ℂ (T q) (J z) = 0 := by
    rw [← inner_adjoint_isometry_left J z, hres, inner_zero_left]
  have hcross' : inner ℂ (T (J z)) q = 0 := by
    rw [hT (J z) q]
    exact (inner_eq_zero_symm (𝕜 := ℂ)).mp hcross
  have hrec : J x + t • (e : F) = J z + t • q := by
    dsimp only [z, q]
    simp only [map_add, map_smul, smul_sub]
    abel
  have hpred : inner ℂ (T (J z)) (J z) = inner ℂ (predecessorBlock J T z) z := by
    exact (inner_adjoint_isometry_left J z (T (J z))).symm
  have heq : inner ℂ (T (J x + t • (e : F))) (J x + t • (e : F)) =
      inner ℂ (predecessorBlock J T z) z +
        ((‖t‖ ^ 2 : ℝ) : ℂ) * inner ℂ (T q) q := by
    rw [hrec]
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hcross, hcross', mul_zero, zero_mul,
      add_zero, zero_add, hpred]
    congr 1
    rw [← mul_assoc, mul_comm t (starRingEnd ℂ t), Complex.conj_mul']
    all_goals norm_cast
  have hscalar := oneShellSchurScalar_energy J T hT e hb
  change (inner ℂ (T q) q).re = oneShellSchurScalar J T e hb at hscalar
  have hre := congrArg Complex.re heq
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hscalar] using hre

/-- Exhaustive one-shell alternative for a negative successor with PSD
predecessor. The resonant coordinate is the actual kernel projection. -/
theorem oneShell_negative_classification (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric)
    (hPSD : ∀ x, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (e : isometricDetectorComplement J) (he : e ≠ 0)
    (hnegative : ∃ v, (inner ℂ (T v) v).re < 0) :
    (predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T (e : F))) ≠ 0 ∨
    ∃ hb : J.toLinearMap.adjoint (T (e : F)) ∈ (predecessorBlock J T).range,
      oneShellSchurScalar J T e hb < 0 := by
  by_cases hk : (predecessorBlock J T).ker.starProjection
      (J.toLinearMap.adjoint (T (e : F))) = 0
  · have hb := (kernel_projection_zero_iff_range _ (predecessorBlock_symmetric J T hT) _).mp hk
    refine Or.inr ⟨hb, ?_⟩
    obtain ⟨v, hv⟩ := hnegative
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' e he).mp hshell
      (isometricDetectorComplementCoordinate J v)
    have hrec := isometricDetector_coordinate_decomposition J v
    rw [← ht] at hrec
    simp only [Submodule.coe_smul] at hrec
    have heq := oneShell_regular_completedSquare J T hT e hb (J.toLinearMap.adjoint v) t
    rw [hrec] at heq
    have hp := hPSD (J.toLinearMap.adjoint v + t • kernelSafeResponse _ _ hb)
    have hmul : ‖t‖ ^ 2 * oneShellSchurScalar J T e hb < 0 := by linarith
    by_contra hs
    have hnonneg := mul_nonneg (sq_nonneg ‖t‖) (le_of_not_gt hs)
    linarith
  · exact Or.inl hk

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.kernelSafeResponse_spec
#print axioms Zeta23.OPICARound3.kernelOrthogonal_preimage_unique
#print axioms Zeta23.OPICARound3.oneShell_regular_completedSquare
#print axioms Zeta23.OPICARound3.oneShell_negative_classification
