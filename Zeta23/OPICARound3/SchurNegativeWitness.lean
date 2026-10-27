import Zeta23.OPICARound3.KernelSafeSchur

noncomputable section

namespace Zeta23.OPICARound3

open CCM
open scoped ComplexConjugate

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

def regularSchurWitness (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) : F :=
  e.val - J (kernelSafeResponse (predecessorBlock J T) _ hb)

theorem regularSchurWitness_energy (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :
    (inner ℂ (T (regularSchurWitness J T e hb)) (regularSchurWitness J T e hb)).re =
      oneShellSchurScalar J T e hb :=
  oneShellSchurScalar_energy J T hT e hb

theorem inner_kernelProjection_re (A : E →ₗ[ℂ] E) (b : E) :
    (inner ℂ b (A.ker.starProjection b)).re = ‖A.ker.starProjection b‖ ^ 2 := by
  let z := A.ker.starProjection b
  have hz : z ∈ A.ker := A.ker.starProjection_apply_mem b
  have horth := A.ker.sub_starProjection_mem_orthogonal b
  have hp := (Submodule.mem_orthogonal _ _).mp horth z hz
  have hp' : inner ℂ z b = inner ℂ z z := by
    apply sub_eq_zero.mp
    simpa only [inner_sub_right] using hp
  calc
    (inner ℂ b z).re = (inner ℂ z b).re := inner_re_symm (𝕜 := ℂ) b z
    _ = (inner ℂ z z).re := congrArg Complex.re hp'
    _ = ‖z‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      exact RCLike.re_ofReal_pow (K := ℂ) ‖z‖ 2

theorem oneShell_kernel_line_energy (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (e : isometricDetectorComplement J) (z : E)
    (hz : predecessorBlock J T z = 0) (t : ℝ) :
    (inner ℂ (T (e.val + (t : ℂ) • J z)) (e.val + (t : ℂ) • J z)).re =
      (inner ℂ (T e.val) e.val).re +
        2 * t * (inner ℂ (J.toLinearMap.adjoint (T e.val)) z).re := by
  have hleft : inner ℂ (T e.val) (J z) =
      inner ℂ (J.toLinearMap.adjoint (T e.val)) z :=
    (inner_adjoint_isometry_left J z (T e.val)).symm
  have hright : (inner ℂ (T (J z)) e.val).re =
      (inner ℂ (J.toLinearMap.adjoint (T e.val)) z).re := by
    calc
      _ = (inner ℂ (J z) (T e.val)).re := congrArg Complex.re (hT (J z) e.val)
      _ = (inner ℂ (T e.val) (J z)).re := inner_re_symm (𝕜 := ℂ) (J z) (T e.val)
      _ = _ := congrArg Complex.re hleft
  have hzero : inner ℂ (T (J z)) (J z) = 0 := by
    rw [← inner_adjoint_isometry_left J z (T (J z))]
    change inner ℂ (predecessorBlock J T z) z = 0
    rw [hz, inner_zero_left]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hzero, mul_zero, add_zero,
    Complex.add_re, Complex.mul_re]
  simp only [map_ofNat, Complex.conj_ofReal, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, hleft, hright]
  ring

def resonantSchurCoefficient (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J) : ℝ :=
  ((inner ℂ (T e.val) e.val).re + 1) /
    (2 * ‖(predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val))‖ ^ 2)

def resonantSchurWitness (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J) : F :=
  e.val - (resonantSchurCoefficient J T e : ℂ) •
    J ((predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val)))

theorem resonantSchurWitness_energy (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (e : isometricDetectorComplement J)
    (hz : (predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val)) ≠ 0) :
    (inner ℂ (T (resonantSchurWitness J T e)) (resonantSchurWitness J T e)).re = -1 := by
  let z := (predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val))
  have hker : predecessorBlock J T z = 0 :=
    (LinearMap.mem_ker).mp ((predecessorBlock J T).ker.starProjection_apply_mem _)
  have hq := oneShell_kernel_line_energy J T hT e z hker
    (-resonantSchurCoefficient J T e)
  have hp := inner_kernelProjection_re (predecessorBlock J T) (J.toLinearMap.adjoint (T e.val))
  change (inner ℂ (J.toLinearMap.adjoint (T e.val)) z).re = ‖z‖ ^ 2 at hp
  rw [hp] at hq
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hw : resonantSchurWitness J T e =
      e.val + ((-resonantSchurCoefficient J T e : ℝ) : ℂ) • J z := by
    simp only [resonantSchurWitness, Complex.ofReal_neg, neg_smul, sub_eq_add_neg]
    rfl
  rw [← hw] at hq
  rw [hq]
  unfold resonantSchurCoefficient
  change _ + 2 * (-((_ + 1) / (2 * ‖z‖ ^ 2))) * ‖z‖ ^ 2 = -1
  field_simp [hnorm]
  <;> ring

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.regularSchurWitness_energy
#print axioms Zeta23.OPICARound3.resonantSchurWitness_energy
