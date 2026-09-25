import Zeta23.CCM.CofinalLowerBound
import Zeta23.ExceptionalZero.ApertureFreedom
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# Audit-only: the exact remaining cofinal certificate would imply RH

No certificate is constructed here. In particular this file is NOT a
premise-free RH closure and is not imported into either active aggregator.
The arithmetic inequality required to construct this family remains OPEN.
-/

/-- Cofinal positive apertures, each with a jointly cofinal size/error family.
This is the exact infinite certificate obligation, not a finite experiment. -/
def CofinalCanonicalLowerCertificates : Prop :=
  ∀ B : ℝ, ∃ L : ℝ, 0 < L ∧ B < L ∧ JointCofinalBottomLowerBounds L

/-- Aperture freedom and N-antitonicity close the implication once, and only
once, the infinite lower-certificate family is supplied. -/
theorem criticalLine_of_cofinalCanonicalLowerCertificates
    (hcert : CofinalCanonicalLowerCertificates) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  obtain ⟨L₀, _hL₀, hbad⟩ :=
    eventually_all_apertures_have_globalFirstBad_of_offLine_zero ⟨ρ, hρ⟩ hoff
  obtain ⟨L, hL, hlarge, hbound⟩ := hcert L₀
  obtain ⟨K, hK, hKbad, _hminimal⟩ := hbad L hlarge
  have hKsucc : K - 1 + 1 = K := by omega
  have hneg : globalParitySuccessorBottom L (K - 1) < 0 := by
    apply globalParitySuccessorBottom_neg_of_anyParityBad
    simpa only [hKsucc] using hKbad
  have hnonneg := globalParitySuccessorBottom_nonneg_of_jointCofinal_lowerBounds
    hL hbound (K - 1) (by omega)
  exact (not_lt_of_ge hnonneg) hneg

/-- Literal Mathlib RH, with the undispatched arithmetic certificate visible
as a theorem argument. It is deliberately not called a closure theorem. -/
theorem riemannHypothesis_of_cofinalCanonicalLowerCertificates
    (hcert : CofinalCanonicalLowerCertificates) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by simpa using hs
  exact criticalLine_of_cofinalCanonicalLowerCertificates hcert s hmem

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.criticalLine_of_cofinalCanonicalLowerCertificates
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_cofinalCanonicalLowerCertificates
