import Zeta23.CCM.CanonicalParityFirstCrossingShell
import Zeta23.CCM.FirstCrossingSourceDynamics
import Zeta23.CCM.CanonicalApertureLocation
import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.GlobalParityBottomPrimeWeightJets

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 seam first-crossing barrier target

This module isolates the exact OPEN one-sided production theorem at
`Lstar = log q`.

The entering q-atom vanishes at the seam, and the existing source-jet stack
proves the boundary-flat seventh-order and even ninth-order formulas.  Because
the production prime channel is subtracted, those jet signs alone do not give a
barrier; the smooth pole/arch/background germ and the contact constraints must
be controlled together.

No seam barrier is assumed or proved here.
-/

/-- OPEN target: no canonical parity first-crossing shell can have its contact
at a logarithmic integer cutoff seam. -/
def CanonicalSeamFirstCrossingBarrier : Prop :=
  ∀ c : CanonicalParityFirstCrossingShell,
    ∀ q : ℕ, 2 ≤ q →
      c.Lstar = Real.log (q : ℝ) →
        False

/-- Scalar production target for the one-sided seam route.

For regular nearby states to the right of a seam first contact, the complete
canonical zero-shift Schur endpoint must stay nonnegative.  Proving this
requires the full production germ, not the sign of the entering source atom in
isolation. -/
def CanonicalSeamRegularEndpointBarrier : Prop :=
  ∀ c : CanonicalParityFirstCrossingShell,
    ∀ q : ℕ, 2 ≤ q →
      c.Lstar = Real.log (q : ℝ) →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ L : ℝ,
            c.Lstar < L →
            L < c.Lstar + δ →
            ∀ hreg : IntrinsicPredecessorRegular c.p L c.k,
              PredecessorSectorNonnegative c.p L c.k →
              0 ≤ Complex.re
                (regularZeroShiftSchurEndpoint c.p L c.k hreg)

end Zeta23.CCM
