import Zeta23.CCM.CanonicalArithmeticCofinal
import Zeta23.ExceptionalZero.CofinalLowerBoundConditionalRH

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# Audit-only: cofinal canonical arithmetic certificates imply RH

This is a sufficient conditional seam only.  No arithmetic certificate family
is constructed here and no reverse implication is claimed.
-/

/-- Arbitrarily large positive apertures each carry a jointly cofinal
size/error family of exact all-vector canonical arithmetic certificates. -/
def CofinalCanonicalArithmeticCertificates : Prop :=
  ∀ B : ℝ, ∃ L : ℝ,
    0 < L ∧ B < L ∧ JointCofinalCanonicalArithmeticLowerBounds L

/-- The arithmetic premise supplies the abstract cofinal bottom premise used by
the already-checked conditional RH seam. -/
theorem cofinalCanonicalLowerCertificates_of_cofinalCanonicalArithmeticCertificates
    (hcert : CofinalCanonicalArithmeticCertificates) :
    CofinalCanonicalLowerCertificates := by
  intro B
  obtain ⟨L, hL, hBL, hA⟩ := hcert B
  exact ⟨L, hL, hBL,
    jointCofinalBottomLowerBounds_of_jointCofinalCanonicalArithmeticLowerBounds
      hL hA⟩

/-- Literal Mathlib RH from the exact cofinal arithmetic premise.  The premise
remains OPEN; this theorem does not construct it. -/
theorem riemannHypothesis_of_cofinalCanonicalArithmeticCertificates
    (hcert : CofinalCanonicalArithmeticCertificates) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinalCanonicalLowerCertificates
    (cofinalCanonicalLowerCertificates_of_cofinalCanonicalArithmeticCertificates
      hcert)

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.cofinalCanonicalLowerCertificates_of_cofinalCanonicalArithmeticCertificates
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_cofinalCanonicalArithmeticCertificates
