import Zeta23.CCM.GlobalParityBottomSimplicity
import Zeta23.CCM.CanonicalPrimeSeamTaylor

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A2: moving-ground transfer interface

No canonical transfer theorem is asserted yet.  The data type records exactly
what a strict or multiplicity-safe perturbation result must return.
-/

inductive GroundBranchKind
  | evenStrict
  | oddStrict
  | parityTie
  deriving DecidableEq, Repr

structure GroundPerturbationResult where
  branch : GroundBranchKind
  leadingOrder : ℕ
  leadingCoefficient : ℝ
  remainderConstant : ℝ
  remainder_nonnegative : 0 ≤ remainderConstant

/-- The actual canonical strict/tie transfer remains an OPEN obligation in the
campaign manifest; open obligations receive metadata, not axioms. -/

end Zeta23.CCM
