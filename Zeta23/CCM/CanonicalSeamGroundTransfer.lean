import Zeta23.CCM.ParityGroundPerturbation

namespace Zeta23.CCM

/-!
# Closure campaign A2: seam-ground result envelope

This module fixes the output shape for a future canonical transfer theorem.
It does not assert that the output exists for every seam.
-/

structure CanonicalSeamGroundTransferData where
  q : ℕ
  K : ℕ
  branch : GroundBranchKind
  leadingOrder : ℕ
  coefficient : ℝ
  remainderConstant : ℝ
  remainder_nonnegative : 0 ≤ remainderConstant

end Zeta23.CCM
