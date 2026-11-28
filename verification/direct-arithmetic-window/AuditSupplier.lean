import Zeta23WindowArithmetic.PrincipalWindowSupply
import DirectWindowAudit.Core

open Lean Elab Command DirectWindowAudit
open Zeta23WindowArithmetic

/- Independent expected surface: all real points on arbitrarily late windows,
   with no literature, arithmetic, zero-free, or native-energy premise. -/
example : ∀ t : ℝ, 0 < t → ∀ B : ℝ, ∃ Y : ℝ,
    max B 2 ≤ Y ∧
    ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
      Formalism.Gz x ≤ x ^ (1 / 2 + t) :=
  principal_original_windows

set_option maxHeartbeats 0 in
run_cmd
  audit ``principal_original_windows .supplier
    [``arithmeticInputs, ``principal_level_kept, ``principal_level_gm_eq_Gz,
     ``principal_original_windows_of_inputs,
     ``UpperTheory.Comparison₂.level_gm_le_on_family_scales,
     ``UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter,
     ``UpperTheory.Zero.LLC.recTExists]
    [``principal_original_windows_of_inputs, ``arithmeticInputs]
