import Zeta23.CCM.CanonicalParityFirstCrossingShell
import Zeta23.CCM.CanonicalApertureLocation

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 first-crossing barrier interfaces

The remaining production theorem is deliberately split by aperture geometry.
These are propositions, not assumed facts and not theorem authority.

* interior barrier: no canonical parity first-crossing shell can have its
  contact strictly inside one fixed physical cutoff cell;
* seam barrier: no canonical parity first-crossing shell can have its contact
  exactly at a logarithmic integer cutoff seam.

The exhaustive aperture-location theorem proves that these two barriers would
exclude every first-crossing shell.  Neither barrier is proved here.
-/

/-- OPEN target: exclude a first-crossing shell whose contact lies inside one
fixed physical cutoff cell. -/
def CanonicalInteriorFirstCrossingBarrier : Prop :=
  ∀ c : CanonicalParityFirstCrossingShell,
    ∀ Q : ℕ, 1 ≤ Q →
      c.Lstar ∈ fixedCanonicalCutoffCell Q →
        False

/-- OPEN target: exclude a first-crossing shell whose contact is a logarithmic
integer seam. -/
def CanonicalSeamFirstCrossingBarrier : Prop :=
  ∀ c : CanonicalParityFirstCrossingShell,
    ∀ q : ℕ, 2 ≤ q →
      c.Lstar = Real.log (q : ℝ) →
        False

/-- The interior/seam split is exhaustive, so proofs of both production
barriers would exclude every canonical parity first-crossing shell. -/
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
