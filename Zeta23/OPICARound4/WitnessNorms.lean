import Zeta23.OPICARound3.SchurNegativeWitness
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4

open CCM OPICARound3
open scoped ComplexConjugate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Genuine orthogonal-shell Pythagoras: the inherited physical metric is used. -/
theorem shell_sub_norm_sq
    (J : E →ₗᵢ[ℂ] F) (e : isometricDetectorComplement J) (x : E) :
    ‖(e : F) - J x‖ ^ 2 = ‖(e : F)‖ ^ 2 + ‖x‖ ^ 2 := by
  have horth : inner ℂ (e : F) (J x) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp e.property _ ⟨x, rfl⟩
  have hneg : inner ℂ (e : F) (-(J x)) = 0 := by
    rw [inner_neg_right, horth, neg_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := ℂ) (e : F) (-(J x)) hneg
  simpa only [pow_two, sub_eq_add_neg, norm_neg, J.norm_map] using hp

/-- The regular Schur witness is not assumed to have unit norm. -/
theorem regular_witness_norm_sq
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J)
    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :
    ‖regularSchurWitness J T e hb‖ ^ 2 =
      ‖(e : F)‖ ^ 2 +
        ‖kernelSafeResponse (predecessorBlock J T) _ hb‖ ^ 2 := by
  change ‖(e : F) - J (kernelSafeResponse (predecessorBlock J T) _ hb)‖ ^ 2 = _
  exact shell_sub_norm_sq J e _

/-- The resonant witness pays its exact (possibly large) kernel-projection cost. -/
theorem resonant_witness_norm_sq
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (e : isometricDetectorComplement J) :
    ‖resonantSchurWitness J T e‖ ^ 2 =
      ‖(e : F)‖ ^ 2 +
      ‖(resonantSchurCoefficient J T e : ℂ)‖ ^ 2 *
        ‖(predecessorBlock J T).ker.starProjection
          (J.toLinearMap.adjoint (T e.val))‖ ^ 2 := by
  let z := (predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T e.val))
  let c : ℂ := resonantSchurCoefficient J T e
  have hp := shell_sub_norm_sq J e (c • z)
  change ‖(e : F) - J (c • z)‖ ^ 2 = ‖(e : F)‖ ^ 2 + ‖c • z‖ ^ 2 at hp
  have hz : ‖(e : F) - c • J z‖ ^ 2 = ‖(e : F)‖ ^ 2 + ‖c • z‖ ^ 2 := by
    simpa only [map_smul] using hp
  change ‖(e : F) - c • J z‖ ^ 2 =
    ‖(e : F)‖ ^ 2 + ‖c‖ ^ 2 * ‖z‖ ^ 2
  rw [hz, norm_smul]
  ring

/-- Rayleigh-energy bookkeeping, with no eigenvector assertion. -/
def rayleighEnergy (T : F →ₗ[ℂ] F) (x : F) : ℝ :=
  (inner ℂ (T x) x).re / ‖x‖ ^ 2

/-- Exact regular-Schur Rayleigh quotient for a unit shell (not a unit witness). -/
theorem regular_witness_rayleigh
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (e : isometricDetectorComplement J) (he : ‖(e : F)‖ = 1)
    (hb : J.toLinearMap.adjoint (T e.val) ∈ (predecessorBlock J T).range) :
    rayleighEnergy T (regularSchurWitness J T e hb) =
      oneShellSchurScalar J T e hb /
        (1 + ‖kernelSafeResponse (predecessorBlock J T) _ hb‖ ^ 2) := by
  unfold rayleighEnergy
  rw [regularSchurWitness_energy J T hT e hb,
      regular_witness_norm_sq J T e hb, he]
  simp only [one_pow]

/-- The resonant energy is -1, but its normalized depth is generally not -1. -/
theorem resonant_witness_rayleigh
    (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (hT : T.IsSymmetric)
    (e : isometricDetectorComplement J) (he : ‖(e : F)‖ = 1)
    (hz : (predecessorBlock J T).ker.starProjection
      (J.toLinearMap.adjoint (T e.val)) ≠ 0) :
    rayleighEnergy T (resonantSchurWitness J T e) =
      -1 / (1 + ‖(resonantSchurCoefficient J T e : ℂ)‖ ^ 2 *
        ‖(predecessorBlock J T).ker.starProjection
          (J.toLinearMap.adjoint (T e.val))‖ ^ 2) := by
  unfold rayleighEnergy
  rw [resonantSchurWitness_energy J T hT e hz,
      resonant_witness_norm_sq J T e, he]
  simp only [one_pow]

end Zeta23.OPICARound4
