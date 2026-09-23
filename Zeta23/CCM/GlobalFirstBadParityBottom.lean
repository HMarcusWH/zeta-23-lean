import Zeta23.CCM.RegularFirstBadCanonicalEnergy
import Zeta23.CCM.FirstBadSpectralInterfaces
import Zeta23.CCM.GlobalParityBottomCrossParity
import Zeta23.CCM.GlobalParityBottomIntertwining

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — retained first-bad global-bottom interface

This module attaches the new parity-ground-state machinery to the exact
cell-minimal first-bad certificate already retained by the repository.

No new existential selection of aperture or first-bad size is made.  The same
retained L and Nstar are used; only the successor spectral parameter is
reselected from the historical arbitrary negative eigenvalue to the true
two-parity ground level.
-/

/-- The retained selected bad successor is, of course, an AnyParityBad state
at the stored successor size.  This tiny interface keeps the selected parity
out of the #247 spectral layer. -/
theorem RegularCellMinimalFirstBadCertificate.anyParityBad_succ
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q) :
    AnyParityBad c.L (c.Nstar + 1) := by
  have hbad :
      ParityBad c.p c.L (c.Nstar + 1) := by
    rw [c.succ_eq]
    exact c.bad
  cases hp : c.p with
  | even =>
      exact Or.inl (by simpa [hp] using hbad)
  | odd =>
      exact Or.inr (by simpa [hp] using hbad)

/-- The true common successor bottom of every retained first-bad certificate is
strictly negative. -/
theorem RegularCellMinimalFirstBadCertificate.globalParityBottom_neg
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q) :
    globalParitySuccessorBottom c.L c.Nstar < 0 :=
  globalParitySuccessorBottom_neg_of_anyParityBad c.anyParityBad_succ

/-- Exact retained parity-bottom trichotomy. -/
theorem RegularCellMinimalFirstBadCertificate.parityBottom_trichotomy
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q) :
    parityRayleighBottom .even c.L (c.Nstar + 1) <
        parityRayleighBottom .odd c.L (c.Nstar + 1) ∨
      parityRayleighBottom .even c.L (c.Nstar + 1) =
        parityRayleighBottom .odd c.L (c.Nstar + 1) ∨
      parityRayleighBottom .odd c.L (c.Nstar + 1) <
        parityRayleighBottom .even c.L (c.Nstar + 1) :=
  paritySuccessorBottom_trichotomy c.L c.Nstar

/-- Retained strict-even branch, with no odd-good-at-zero premise. -/
theorem RegularCellMinimalFirstBadCertificate.evenStrict_globalBottom_crossParity
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q)
    (hstrict :
      parityRayleighBottom .even c.L (c.Nstar + 1) <
        parityRayleighBottom .odd c.L (c.Nstar + 1)) :
    ∃ hneg : parityRayleighBottom .even c.L (c.Nstar + 1) < 0,
      let lam := parityRayleighBottom .even c.L (c.Nstar + 1)
      let Fplus :=
        cubicSecularScalar .even c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .even) lam hneg
      let Fminus :=
        cubicSecularScalar .odd c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let S :=
        evenQuadraticSourceMoment c.L (c.Nstar + 1)
          (cubicSecularTrialVector .even c.L_pos c.Nstar
            (c.predecessorNonnegative_anyParity .even) lam hneg)
      Fplus = 0 ∧
      Fminus = Gamma * S ∧
      Gamma ≠ 0 ∧ S ≠ 0 := by
  obtain ⟨hneg, hplus, htransfer, _hpos⟩ :=
    globalBottom_evenStrict_crossParity
      c.L_pos c.Nstar c.one_le_Nstar
      c.predecessorNonnegative_anyParity c.anyParityBad_succ hstrict
  obtain ⟨hneg', hGamma, hS⟩ :=
    globalBottom_evenStrict_gamma_source_ne_zero
      c.L_pos c.Nstar c.one_le_Nstar
      c.predecessorNonnegative_anyParity c.anyParityBad_succ hstrict
  have hproof : hneg' = hneg := Subsingleton.elim _ _
  subst hneg'
  exact ⟨hneg, hplus, htransfer, hGamma, hS⟩

/-- Retained strict-odd branch: exact odd root, nonzero even secular value, and
the full source balance. -/
theorem RegularCellMinimalFirstBadCertificate.oddStrict_globalBottom_crossParity
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q)
    (hstrict :
      parityRayleighBottom .odd c.L (c.Nstar + 1) <
        parityRayleighBottom .even c.L (c.Nstar + 1)) :
    ∃ hneg : parityRayleighBottom .odd c.L (c.Nstar + 1) < 0,
      let lam := parityRayleighBottom .odd c.L (c.Nstar + 1)
      let Fplus :=
        cubicSecularScalar .even c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .even) lam hneg
      let Fminus :=
        cubicSecularScalar .odd c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let alpha :=
        crossParitySecularAlpha c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let S :=
        evenQuadraticSourceMoment c.L (c.Nstar + 1)
          (cubicSecularTrialVector .even c.L_pos c.Nstar
            (c.predecessorNonnegative_anyParity .even) lam hneg)
      Fminus = 0 ∧ Fplus ≠ 0 ∧ alpha * Fplus + Gamma * S = 0 := by
  obtain ⟨hneg, hminus, hbalance, _hpos⟩ :=
    globalBottom_oddStrict_crossParity
      c.L_pos c.Nstar c.one_le_Nstar
      c.predecessorNonnegative_anyParity c.anyParityBad_succ hstrict
  obtain ⟨hneg', hplusNe⟩ :=
    globalBottom_oddStrict_evenSecular_ne_zero
      c.L_pos c.Nstar c.one_le_Nstar
      c.predecessorNonnegative_anyParity c.anyParityBad_succ hstrict
  have hproof : hneg' = hneg := Subsingleton.elim _ _
  subst hneg'
  exact ⟨hneg, hminus, hplusNe, hbalance⟩

/-- Retained tied-bottom branch: simultaneous roots reduce exactly to Gamma*S=0. -/
theorem RegularCellMinimalFirstBadCertificate.tie_globalBottom_crossParity
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q)
    (htie :
      parityRayleighBottom .even c.L (c.Nstar + 1) =
        parityRayleighBottom .odd c.L (c.Nstar + 1)) :
    ∃ hneg : parityRayleighBottom .even c.L (c.Nstar + 1) < 0,
      let lam := parityRayleighBottom .even c.L (c.Nstar + 1)
      let Fplus :=
        cubicSecularScalar .even c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .even) lam hneg
      let Fminus :=
        cubicSecularScalar .odd c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma c.L_pos c.Nstar
          (c.predecessorNonnegative_anyParity .odd) lam hneg
      let S :=
        evenQuadraticSourceMoment c.L (c.Nstar + 1)
          (cubicSecularTrialVector .even c.L_pos c.Nstar
            (c.predecessorNonnegative_anyParity .even) lam hneg)
      Fplus = 0 ∧ Fminus = 0 ∧ Gamma * S = 0 := by
  exact globalBottom_tie_crossParity
    c.L_pos c.Nstar c.one_le_Nstar
    c.predecessorNonnegative_anyParity c.anyParityBad_succ htie

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalFirstBadCertificate.anyParityBad_succ
#print axioms Zeta23.CCM.RegularCellMinimalFirstBadCertificate.globalParityBottom_neg
#print axioms Zeta23.CCM.RegularCellMinimalFirstBadCertificate.evenStrict_globalBottom_crossParity
#print axioms Zeta23.CCM.RegularCellMinimalFirstBadCertificate.oddStrict_globalBottom_crossParity
#print axioms Zeta23.CCM.RegularCellMinimalFirstBadCertificate.tie_globalBottom_crossParity
