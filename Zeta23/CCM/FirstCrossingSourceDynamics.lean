import Zeta23.CCM.FirstCrossingSchurReduction
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport
import Zeta23.CCM.CanonicalSourceEnergyJets
import Zeta23.CCM.CanonicalSourceMomentJets

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#278 first-crossing source-dynamics interface

At a regular predecessor block the canonical cubic shell coupling has a unique
zero-shift preimage.  This module packages that preimage and its scalar Schur
endpoint as a canonical function of the regular state.

The source-derivative and endpoint-jet modules are imported here because this
scalar is the object whose production aperture germ must be controlled next.
No sign theorem for that germ is asserted.
-/

/-- Canonical zero-shift preimage on a regular predecessor block. -/
noncomputable def regularCubicZeroShiftPreimage
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    intrinsicParityPredecessorSubspace p N :=
  Classical.choose
    (existsUnique_cubicZeroShiftPreimage_of_regular p L N hreg).exists

/-- The chosen regular preimage solves the actual shell-coupling equation. -/
theorem regularCubicZeroShiftPreimage_spec
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    intrinsicPredecessorBlock p L N
        (regularCubicZeroShiftPreimage p L N hreg) =
      intrinsicShellToPredecessor p L N
        (intrinsicCubicShellPart p N) := by
  exact
    Classical.choose_spec
      (existsUnique_cubicZeroShiftPreimage_of_regular p L N hreg).exists

/-- Canonical regular zero-shift Schur endpoint. -/
noncomputable def regularZeroShiftSchurEndpoint
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) : ℂ :=
  cubicZeroShiftSchurEndpoint p L N
    (regularCubicZeroShiftPreimage p L N hreg)

/-- Exact real-energy normal form of the canonical regular endpoint. -/
theorem regularZeroShiftSchurEndpoint_re_eq_shell_sub_predecessor
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    Complex.re (regularZeroShiftSchurEndpoint p L N hreg) =
      cubicShellRealEnergy p L N -
        intrinsicPredecessorRealEnergy p L N
          (regularCubicZeroShiftPreimage p L N hreg) := by
  unfold regularZeroShiftSchurEndpoint
  exact
    cubicZeroShiftSchurEndpoint_re_eq_shell_sub_predecessorRealEnergy
      p L N
      (regularCubicZeroShiftPreimage p L N hreg)
      (regularCubicZeroShiftPreimage_spec p L N hreg)

/-- At any regular bad successor over a nonnegative predecessor, the canonical
regular endpoint is strictly negative. -/
theorem regularZeroShiftSchurEndpoint_re_neg_of_parityBad
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev : PredecessorSectorNonnegative p L N)
    (hbad : ParityBad p L (N + 1))
    (hreg : IntrinsicPredecessorRegular p L N) :
    Complex.re (regularZeroShiftSchurEndpoint p L N hreg) < 0 := by
  unfold regularZeroShiftSchurEndpoint
  exact
    cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
      p hL N hN hprev hbad
      (regularCubicZeroShiftPreimage p L N hreg)
      (regularCubicZeroShiftPreimage_spec p L N hreg)

end Zeta23.CCM

#print axioms Zeta23.CCM.regularCubicZeroShiftPreimage_spec
#print axioms Zeta23.CCM.regularZeroShiftSchurEndpoint_re_eq_shell_sub_predecessor
#print axioms Zeta23.CCM.regularZeroShiftSchurEndpoint_re_neg_of_parityBad
