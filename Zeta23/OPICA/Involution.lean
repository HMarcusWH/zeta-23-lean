import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Field.Defs

/-!
# Commutators of a linear involution

This is the algebraic content of OPICA H3. All operators act on the same
module. Analytic Fourier applications must first establish that common domain.
-/

noncomputable section

namespace Zeta23.OPICA

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The commutator acts on the common module of its two operators. -/
def involutionCommutator (P F : V →ₗ[𝕜] V) (v : V) : V :=
  P (F v) - F (P v)

/-- Projection onto the invariant subspace when `F` is an involution and
the scalar field has characteristic different from two. -/
def involutionSelfdualProjection (F : V →ₗ[𝕜] V) (v : V) : V :=
  (2 : 𝕜)⁻¹ • (v + F v)

/-- H3: a commutator applied to an invariant input is anti-invariant. -/
theorem commutator_anti_invariant (P F : V →ₗ[𝕜] V)
    (hF : Function.Involutive F) {v : V} (hv : F v = v) :
    F (involutionCommutator P F v) = -involutionCommutator P F v := by
  simp only [involutionCommutator, map_sub, hv, neg_sub]
  rw [hF (P v)]

/-- The selfdual projection of the H3 commutator vanishes. -/
theorem commutator_selfdual_projection_zero (P F : V →ₗ[𝕜] V)
    (hF : Function.Involutive F) {v : V} (hv : F v = v) :
    involutionSelfdualProjection F (involutionCommutator P F v) = 0 := by
  rw [involutionSelfdualProjection, commutator_anti_invariant P F hF hv]
  simp

end Zeta23.OPICA

#print axioms Zeta23.OPICA.commutator_anti_invariant
#print axioms Zeta23.OPICA.commutator_selfdual_projection_zero
