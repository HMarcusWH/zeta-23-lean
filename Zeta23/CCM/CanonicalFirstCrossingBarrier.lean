import Zeta23.CCM.CanonicalInteriorFirstCrossingBarrier
import Zeta23.CCM.CanonicalSeamFirstCrossingBarrier

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 exhaustive first-crossing barrier interface

The production closure target is split into the interior and seam propositions
defined in the two dedicated modules.  Positive aperture geometry is exhaustive:
every contact is either an interior point of one fixed cutoff cell or exactly a
logarithmic integer seam.

This file proves only the composition of the two still-OPEN barriers.
-/

/-- The interior/seam split is exhaustive, so proofs of both production
barriers exclude every canonical parity first-crossing shell. -/
theorem no_canonicalParityFirstCrossingShell_of_barriers
    (hinterior : CanonicalInteriorFirstCrossingBarrier)
    (hseam : CanonicalSeamFirstCrossingBarrier)
    (c : CanonicalParityFirstCrossingShell) :
    False := by
  have hstarpos : 0 < c.Lstar :=
    lt_trans c.Lsmall_pos c.Lsmall_lt_Lstar
  rcases canonicalApertureLocation_of_pos hstarpos with
      ⟨q, hq, hEq⟩ | ⟨Q, hQ, hcell⟩
  · exact hseam c q hq hEq
  · exact hinterior c Q hQ hcell

end Zeta23.CCM

#print axioms Zeta23.CCM.no_canonicalParityFirstCrossingShell_of_barriers
