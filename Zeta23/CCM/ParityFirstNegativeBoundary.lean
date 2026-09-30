import Zeta23.CCM.CanonicalGroundContinuity

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 parity first-negative boundary interface

This module introduces the one-parity contact object used by the post-#278
first-crossing reduction.

The global legal successor bottom is the minimum of the even and odd parity
bottoms.  Once one terminal parity is selected, the closure route should stay
on that parity rather than repeatedly reason through the minimum.

No existence theorem is assumed by these definitions.  In particular this
module does not assert aperture monotonicity, a crossing barrier, or RH.
-/

/-- The successor parity bottom at predecessor-size index `N`. -/
def paritySuccessorGround
    (p : ReversalParity) (N : ℕ) (L : ℝ) : ℝ :=
  parityRayleighBottom p L (N + 1)

/-- Negative values occur arbitrarily close to the right of `Lstar`. -/
def ParityRightCrossesNegative
    (p : ReversalParity) (N : ℕ) (Lstar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ L : ℝ,
      Lstar < L ∧
      L < Lstar + ε ∧
      paritySuccessorGround p N L < 0

/-- One fixed parity reaches its first negative boundary after a positive
anchor.  The prefix condition records the actual first-boundary information;
the right-crossing condition records that this is not merely an arbitrary IVT
zero. -/
structure ParityFirstNegativeBoundary where
  p : ReversalParity
  N : ℕ
  one_le_N : 1 ≤ N
  Lsmall : ℝ
  Lstar : ℝ
  Lneg : ℝ
  Lsmall_pos : 0 < Lsmall
  Lsmall_lt_Lstar : Lsmall < Lstar
  Lstar_lt_Lneg : Lstar < Lneg
  base_positive :
    0 < paritySuccessorGround p N Lsmall
  contact_zero :
    paritySuccessorGround p N Lstar = 0
  prefix_nonnegative :
    ∀ L : ℝ, Lsmall ≤ L → L ≤ Lstar →
      0 ≤ paritySuccessorGround p N L
  right_crossing :
    ParityRightCrossesNegative p N Lstar

end Zeta23.CCM
