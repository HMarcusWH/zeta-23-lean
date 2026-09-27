import Zeta23.CCM.CanonicalSmallApertureCoercivity
import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.CanonicalUniformDomination
import Zeta23.CCM.CanonicalAllAperturePositivity
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

/-- Unconditional CCM all-aperture positivity matches the terminal finite-Weil
premise without importing the terminal layer back into CCM. -/
theorem canonicalFiniteWeilPositivity_of_allAperture
    (h : CanonicalAllAperturePositivity) :
    CanonicalFiniteWeilPositivity := by
  intro L hL K x hx
  exact h L hL K x hx

/-- Final adapter: a future proof of the unconditional CCM target closes the
literal Mathlib RH proposition on the RHRC side of the firewall. -/
theorem rh_of_canonicalAllAperturePositivity
    (h : CanonicalAllAperturePositivity) :
    RiemannHypothesis :=
  rh_of_canonicalFiniteWeilPositivity
    (canonicalFiniteWeilPositivity_of_allAperture h)

end Zeta23.RHRC

#print axioms Zeta23.RHRC.rh_of_canonicalFiniteWeilPositivity
#print axioms Zeta23.RHRC.smallApertureBase_of_channelBounds
#print axioms Zeta23.RHRC.pointwiseSchur_of_uniform
#print axioms Zeta23.RHRC.canonicalFiniteWeilPositivity_of_allAperture
#print axioms Zeta23.RHRC.rh_of_canonicalAllAperturePositivity
