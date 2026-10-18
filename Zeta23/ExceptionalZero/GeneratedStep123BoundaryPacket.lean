import Zeta23.CCM.Step123OriginalBoundaryEvidence

/-!
# Source-preserving strengthened zero-indexed output

This structure PROVES that the constructed exact original forcing,
signed four-prime P-duality, legal/normal/outer Galerkin decomposition
and nonvanishing-allowed physical interior all belong to ONE
zero-generated Step123 packet with ONE detector and selected state.

It uses the existing off-line zero carrier and actual Y nonrange
obstruction. No externally supplied Schur upper law, numerical fitting,
free inverse, extra detector, or hypothetical global X L2 is present.

This is the formal bridge for the currently established N35-N40 data;
all 44 independently reviewed release fields remain a distinct gate.
-/

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

structure GeneratedStep123BoundaryPacket
    (ρ : zetaZeroConfig.carrier) (β : ℝ)
    (σ : ReversalParity) (R : ℝ) where
  generated : GeneratedStep123Output ρ β σ R
  original : Step123OriginalBoundaryEvidence generated.native

/-- Extends the actual generated packet, never repackages an arbitrary
source, selected ground or interior response. -/
def GeneratedStep123BoundaryPacket.fromActualGenerated
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (generated : GeneratedStep123Output ρ β σ R) :
    GeneratedStep123BoundaryPacket ρ β σ R where
  generated := generated
  original := Step123OriginalBoundaryEvidence.fromNative generated.native

/-- Every hypothetical off-line zero, allowed exponent, phase and
lateness bound produces the same-source enhanced packet. This is
conditional geometry, not a proof of an off-line zero's existence. -/
theorem exists_generatedStep123BoundaryPacket
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    Nonempty (GeneratedStep123BoundaryPacket ρ β σ R) := by
  obtain ⟨out⟩ := exists_generatedStep123Output ρ hβ hβρ σ R
  exact ⟨GeneratedStep123BoundaryPacket.fromActualGenerated out⟩

/-- Both parities can separately produce arbitrarily late enhanced
packets, without pretending they share a common chosen aperture. -/
theorem exists_generatedStep123BoundaryPacket_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123BoundaryPacket ρ β σ R,
      max R 4 < fixedOriginalSincTrialAperture
        out.generated.sourceData.separation := by
  obtain ⟨out, hL⟩ :=
    exists_generatedStep123Output_cofinal ρ hβ hβρ σ R
  exact ⟨GeneratedStep123BoundaryPacket.fromActualGenerated out, hL⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.GeneratedStep123BoundaryPacket.fromActualGenerated
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123BoundaryPacket
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123BoundaryPacket_cofinal
