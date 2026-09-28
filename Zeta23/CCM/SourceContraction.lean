import Zeta23.CCM.CanonicalSourceEnergy

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: elementary source contraction contract

The paper-level all-K small-aperture argument reduces first to a uniform bound
on the elementary source matrix. The endpoints are already theorem-backed.
The interior statement is kept as an explicit proposition until its Fourier
integral proof is formalized.

No axiom, placeholder proof, RH hypothesis, or positivity claim is introduced.
-/

/-- Uniform source-contraction statement required by the paper proof. -/
def SourceContractionBound : Prop :=
  ∀ K : ℕ, ∀ ω : ℝ, 0 ≤ ω → ω ≤ 1 →
    ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      |matrixRealEnergy (sourceMatrix ω K) x| ≤ 2 * ‖x‖ ^ 2

/-- The source-contraction inequality is exact at the left endpoint. -/
theorem sourceMatrix_energy_abs_le_two_norm_sq_at_zero
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    |matrixRealEnergy (sourceMatrix 0 K) x| ≤ 2 * ‖x‖ ^ 2 := by
  rw [sourceMatrix_zero, matrixRealEnergy_zero, abs_zero]
  positivity

/-- The source-contraction inequality is exact at the right endpoint. -/
theorem sourceMatrix_energy_abs_le_two_norm_sq_at_one
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    |matrixRealEnergy (sourceMatrix 1 K) x| ≤ 2 * ‖x‖ ^ 2 := by
  rw [matrixRealEnergy_sourceMatrix_one]
  have hnonneg : 0 ≤ 2 * ‖x‖ ^ 2 := by positivity
  rw [abs_of_nonneg hnonneg]

/-- Exact remaining analytic obligation after the two endpoints are removed. -/
def SourceContractionInteriorObligation : Prop :=
  ∀ K : ℕ, ∀ ω : ℝ, 0 < ω → ω < 1 →
    ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      |matrixRealEnergy (sourceMatrix ω K) x| ≤ 2 * ‖x‖ ^ 2

/-- Endpoint theorems plus the open interior obligation give the complete
source-contraction statement. -/
theorem sourceContractionBound_of_interior
    (h : SourceContractionInteriorObligation) :
    SourceContractionBound := by
  intro K ω hω0 hω1 x
  by_cases h0 : ω = 0
  · subst ω
    exact sourceMatrix_energy_abs_le_two_norm_sq_at_zero K x
  by_cases h1 : ω = 1
  · subst ω
    exact sourceMatrix_energy_abs_le_two_norm_sq_at_one K x
  have hω0' : 0 < ω := lt_of_le_of_ne hω0 (Ne.symm h0)
  have hω1' : ω < 1 := lt_of_le_of_ne hω1 h1
  exact h K ω hω0' hω1' x

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceMatrix_energy_abs_le_two_norm_sq_at_zero
#print axioms Zeta23.CCM.sourceMatrix_energy_abs_le_two_norm_sq_at_one
#print axioms Zeta23.CCM.sourceContractionBound_of_interior
