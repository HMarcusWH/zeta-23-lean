import Zeta23.CCM.CanonicalSmallApertureCoercivity
import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.CanonicalUniformDomination
import Zeta23.Spectral.RealZeroLimitTransfer
import Zeta23.ExceptionalZero.CanonicalArithmeticCriterion
import Zeta23.ExceptionalZero.QuantitativeCanonicalWitness

noncomputable section

namespace Zeta23.RHRC

open Zeta23.CCM
open Zeta23.ExceptionalZero

/-!
# Closure-campaign obligation bindings

Only actual Lean applications appear here. OPEN graph obligations have no Lean
axiom or placeholder declaration.
-/

theorem rh_of_canonicalFiniteWeilPositivity
    (h : CanonicalFiniteWeilPositivity) :
    RiemannHypothesis :=
  canonicalFiniteWeilPositivity_iff_riemannHypothesis.mp h

theorem smallApertureBase_of_channelBounds
    (h : CanonicalSmallApertureChannelBounds) :
    CanonicalSmallApertureCoercivity :=
  canonicalSmallApertureCoercivity_of_channel_bounds h

theorem pointwiseSchur_of_uniform
    (h : CanonicalUniformDomination)
    (p : ReversalParity) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    CanonicalSchurCertificateAt p L N :=
  canonicalSchurCertificateAt_of_uniformDomination h p L hL N

end Zeta23.RHRC

#print axioms Zeta23.RHRC.rh_of_canonicalFiniteWeilPositivity
#print axioms Zeta23.RHRC.smallApertureBase_of_channelBounds
#print axioms Zeta23.RHRC.pointwiseSchur_of_uniform
