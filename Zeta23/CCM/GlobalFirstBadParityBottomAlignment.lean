import Zeta23.CCM.BiRegularFirstBadCanonicalEnergy
import Zeta23.CCM.GlobalFirstBadParityBottom
import Zeta23.CCM.CubicExplicitSecular

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — align the retained certificate with the true global ground shift

The historical negative-energy constructor selected an arbitrary negative
successor eigenvalue.  The global-bottom argument needs all retained downstream
geometry to live at the actual minimum of the two parity spectra.

This module proves that the retained certificate can be reselected, at the
same aperture and same cell-minimal size, to whichever parity attains the
global bottom.  Bi-regularity is exactly what makes the parity switch legal.

The zero-shift negative-energy conclusion is then rebuilt from that exact
ground secular root, so every downstream theorem phrased on
RegularCellMinimalNegativeEnergyCertificate can be reused with lam equal to
the true selected parity bottom.
-/

/-- Reselect the successor parity of a bi-regular retained first-bad state
without moving aperture, size, or cell-minimal ancestry. -/
def BiRegularCellMinimalFirstBadCertificate.reselectParity
    {Q : ℕ}
    (b : BiRegularCellMinimalFirstBadCertificate Q)
    (p : ReversalParity)
    (hbad : ParityBad p b.firstBad.L b.firstBad.Kstar) :
    RegularCellMinimalFirstBadCertificate Q := {
  Kstar := b.firstBad.Kstar
  Nstar := b.firstBad.Nstar
  L := b.firstBad.L
  p := p
  one_le_Q := b.firstBad.one_le_Q
  two_le_Kstar := b.firstBad.two_le_Kstar
  one_le_Nstar := b.firstBad.one_le_Nstar
  succ_eq := b.firstBad.succ_eq
  L_mem := b.firstBad.L_mem
  bad := hbad
  cell_minimal := b.firstBad.cell_minimal
  smaller_good := b.firstBad.smaller_good
  regular := by
    cases p with
    | even => exact b.regular_even
    | odd => exact b.regular_odd
}

/-- Build the complete retained negative-energy certificate from a specified
negative explicit secular root, rather than asking the spectral theorem to
choose an arbitrary negative eigenvalue. -/
theorem
    exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_explicitRoot
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q)
    (lam : ℝ) (hlam : lam < 0)
    (hroot :
      cubicExplicitSchurScalar c.p c.L_pos c.Nstar
        (c.predecessorNonnegative_anyParity c.p) lam hlam = 0) :
    ∃ e : RegularCellMinimalNegativeEnergyCertificate Q,
      e.firstBad = c ∧ e.lam = lam := by
  let hprev := c.predecessorNonnegative_anyParity c.p
  obtain ⟨x₀, hx₀, _hunique⟩ :=
    existsUnique_cubicZeroShiftPreimage_of_regular
      c.p c.L c.Nstar c.regular
  have henergyNeg :
      parityCanonicalSourceEnergy c.p c.L (c.Nstar + 1)
        (cubicZeroShiftTrialVector c.p c.L c.Nstar x₀) < 0 :=
    parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_neg_of_explicit_root
      c.p c.L_pos c.Nstar c.one_le_Nstar hprev
      x₀ hx₀ lam hlam hroot
  have henergyEq :=
    parityCanonicalSourceEnergy_eq_channels
      c.p c.L_pos (c.Nstar + 1)
        (cubicZeroShiftTrialVector c.p c.L c.Nstar x₀)
  have hchannelNeg :
      canonicalSourceChannelEnergy c.L (c.Nstar + 1)
        (cubicZeroShiftTrialVector c.p c.L c.Nstar x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.Nstar + 1) + 1))) < 0 := by
    rw [← henergyEq]
    exact henergyNeg
  let e : RegularCellMinimalNegativeEnergyCertificate Q := {
    firstBad := c
    predecessorNonnegative := hprev
    x₀ := x₀
    lam := lam
    lam_neg := hlam
    explicit_root := hroot
    preimage := hx₀
    parityEnergyNeg := henergyNeg
    channelEnergyNeg := hchannelNeg
  }
  exact ⟨e, rfl, rfl⟩

/-- Build the same certificate from an exact quotient secular root. -/
theorem
    exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_secularRoot
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q)
    (lam : ℝ) (hlam : lam < 0)
    (hroot :
      cubicSecularScalar c.p c.L_pos c.Nstar
        (c.predecessorNonnegative_anyParity c.p) lam hlam = 0) :
    ∃ e : RegularCellMinimalNegativeEnergyCertificate Q,
      e.firstBad = c ∧ e.lam = lam := by
  have hexp :
      cubicExplicitSchurScalar c.p c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity c.p) lam hlam = 0 :=
    (cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
      c.p c.L_pos c.Nstar c.one_le_Nstar
      (c.predecessorNonnegative_anyParity c.p) lam hlam).2 hroot
  exact
    exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_explicitRoot
      c lam hlam hexp

/-- Package a complete bi-regular retained first-bad state from an already
bi-regular negative-energy certificate. -/
def BiRegularCellMinimalNegativeEnergyCertificate.toBiRegularFirstBad
    {Q : ℕ}
    (b : BiRegularCellMinimalNegativeEnergyCertificate Q) :
    BiRegularCellMinimalFirstBadCertificate Q := {
  firstBad := b.energy.firstBad
  regular_even := b.regular_even
  regular_odd := b.regular_odd
}

/-- Even-attained global bottom: reselect the retained certificate to even and
make its stored negative shift exactly the even ground energy. -/
theorem
    exists_globalBottomAligned_negativeEnergyCertificate_even
    {Q : ℕ}
    (b : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (hbottom :
      parityRayleighBottom .even b.energy.firstBad.L
          (b.energy.firstBad.Nstar + 1) ≤
        parityRayleighBottom .odd b.energy.firstBad.L
          (b.energy.firstBad.Nstar + 1)) :
    ∃ e : RegularCellMinimalNegativeEnergyCertificate Q,
      e.firstBad.L = b.energy.firstBad.L ∧
      e.firstBad.Nstar = b.energy.firstBad.Nstar ∧
      e.firstBad.p = .even ∧
      e.lam =
        parityRayleighBottom .even b.energy.firstBad.L
          (b.energy.firstBad.Nstar + 1) := by
  let fb := b.energy.firstBad
  have hany : AnyParityBad fb.L (fb.Nstar + 1) := fb.anyParityBad_succ
  have hglobal := globalParitySuccessorBottom_neg_of_anyParityBad hany
  have hmin :
      globalParitySuccessorBottom fb.L fb.Nstar =
        parityRayleighBottom .even fb.L (fb.Nstar + 1) :=
    min_eq_left hbottom
  rw [hmin] at hglobal
  let hlam : parityRayleighBottom .even fb.L (fb.Nstar + 1) < 0 := hglobal
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ
      .even fb.L fb.Nstar fb.one_le_Nstar
  have hbadEven :
      ParityBad .even fb.L fb.Kstar := by
    have hbadSucc :
        ParityBad .even fb.L (fb.Nstar + 1) :=
      parityBad_of_negative_eigenmode hlam hvne hveig
    rw [← fb.succ_eq]
    exact hbadSucc
  let c :=
    b.toBiRegularFirstBad.reselectParity .even hbadEven
  have hroot :
      cubicSecularScalar .even c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .even)
          (parityRayleighBottom .even c.L (c.Nstar + 1)) hlam = 0 := by
    exact cubicSecularScalar_eq_zero_at_parityBottom
      .even c.L_pos c.Nstar c.one_le_Nstar
      (c.predecessorNonnegative_anyParity .even) hlam
  obtain ⟨e, heq, hlamEq⟩ :=
    exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_secularRoot
      c (parityRayleighBottom .even c.L (c.Nstar + 1)) hlam hroot
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rw [heq]
    rfl
  · rw [heq]
    rfl
  · rw [heq]
    rfl
  · rw [hlamEq]
    rfl

/-- Odd-attained global bottom: symmetric re-selection to the odd parity. -/
theorem
    exists_globalBottomAligned_negativeEnergyCertificate_odd
    {Q : ℕ}
    (b : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (hbottom :
      parityRayleighBottom .odd b.energy.firstBad.L
          (b.energy.firstBad.Nstar + 1) <
        parityRayleighBottom .even b.energy.firstBad.L
          (b.energy.firstBad.Nstar + 1)) :
    ∃ e : RegularCellMinimalNegativeEnergyCertificate Q,
      e.firstBad.L = b.energy.firstBad.L ∧
      e.firstBad.Nstar = b.energy.firstBad.Nstar ∧
      e.firstBad.p = .odd ∧
      e.lam =
        parityRayleighBottom .odd b.energy.firstBad.L
          (b.energy.firstBad.Nstar + 1) := by
  let fb := b.energy.firstBad
  have hany : AnyParityBad fb.L (fb.Nstar + 1) := fb.anyParityBad_succ
  have hglobal := globalParitySuccessorBottom_neg_of_anyParityBad hany
  have hmin :
      globalParitySuccessorBottom fb.L fb.Nstar =
        parityRayleighBottom .odd fb.L (fb.Nstar + 1) :=
    min_eq_right (le_of_lt hbottom)
  rw [hmin] at hglobal
  let hlam : parityRayleighBottom .odd fb.L (fb.Nstar + 1) < 0 := hglobal
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ
      .odd fb.L fb.Nstar fb.one_le_Nstar
  have hbadOdd :
      ParityBad .odd fb.L fb.Kstar := by
    have hbadSucc :
        ParityBad .odd fb.L (fb.Nstar + 1) :=
      parityBad_of_negative_eigenmode hlam hvne hveig
    rw [fb.succ_eq]
    exact hbadSucc
  let c :=
    b.toBiRegularFirstBad.reselectParity .odd hbadOdd
  have hroot :
      cubicSecularScalar .odd c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd)
          (parityRayleighBottom .odd c.L (c.Nstar + 1)) hlam = 0 := by
    exact cubicSecularScalar_eq_zero_at_parityBottom
      .odd c.L_pos c.Nstar c.one_le_Nstar
      (c.predecessorNonnegative_anyParity .odd) hlam
  obtain ⟨e, heq, hlamEq⟩ :=
    exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_secularRoot
      c (parityRayleighBottom .odd c.L (c.Nstar + 1)) hlam hroot
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rw [heq]
    rfl
  · rw [heq]
    rfl
  · rw [heq]
    rfl
  · rw [hlamEq, heq]
    rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.BiRegularCellMinimalFirstBadCertificate.reselectParity
#print axioms Zeta23.CCM.exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_explicitRoot
#print axioms Zeta23.CCM.exists_regularCellMinimalNegativeEnergyCertificate_of_firstBad_secularRoot
#print axioms Zeta23.CCM.exists_globalBottomAligned_negativeEnergyCertificate_even
#print axioms Zeta23.CCM.exists_globalBottomAligned_negativeEnergyCertificate_odd
