import Zeta23WindowArithmetic.ProvedInputs
import Zeta23WindowArithmetic.WindowExtraction
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi

/-!
# Unconditional principal arithmetic-window supplier

This is the original-source extraction boundary.  Its statement has no
arithmetic, literature, zero-free, energy, or moment-bound premise.
-/

noncomputable section

namespace Zeta23WindowArithmetic

open Formalism.HC

/-- Arbitrarily late complete real windows with coefficient exactly one. -/
theorem principal_original_windows :
    ∀ t : ℝ, 0 < t → ∀ B : ℝ, ∃ Y : ℝ,
      max B 2 ≤ Y ∧
      ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
        Formalism.Gz x ≤ x ^ (1 / 2 + t) :=
  principal_original_windows_of_inputs arithmeticInputs.1
    (UpperTheory.Top.supplyChi PChar.one (arithmeticInputs.2 PChar.one))

end Zeta23WindowArithmetic
