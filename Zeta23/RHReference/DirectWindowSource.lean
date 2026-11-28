import Zeta23.RHReference.DirectWindowContract
import Zeta23WindowArithmetic.PrincipalWindowSupply

/-!
# Bind the original arithmetic windows to the native literal source

Both definitions sum von Mangoldt over the same inclusive integer interval,
retain all prime powers, and use the same Euler--Mascheroni correction.  Their
equality is definitional and holds for every real argument.
-/

noncomputable section

namespace Zeta23.RHReference

open Zeta23.OPICARound6.PrimeDeficit

/-- The original and native literal formulas have exactly the same terms. -/
theorem originalGz_eq_literalG (x : ℝ) :
    Formalism.Gz x = literalG x := rfl

/-- The proved original supplier, expressed in the native window contract. -/
theorem principal_literal_windows : DirectArithmeticWindowSupply := by
  intro t ht B
  obtain ⟨Y, hY, hupper⟩ :=
    Zeta23WindowArithmetic.principal_original_windows t ht B
  refine ⟨Y, hY, ?_⟩
  intro x hx
  calc
    literalG x = Formalism.Gz x := (originalGz_eq_literalG x).symm
    _ ≤ x ^ (1 / 2 + t) := hupper x hx
    _ = 1 * x ^ (1 / 2 + t) := (one_mul _).symm

end Zeta23.RHReference
