import Zeta23.ExceptionalZero.GlobalParityBottomGeneratedState
import Zeta23.ExceptionalZero.GeneratedFamilyFinalGateEquivalence
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt
import Zeta23.CCM.GlobalParityBottomPrimeRemainder

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM

/-!
# PR #247 — arithmetic-equivalence audit

This file is intentionally quarantined from the active proof route.  It
theoremizes the anti-self-deception result: a universal dominance assertion
over every global-bottom residual state is only residual-state nonexistence in
disguise, and that nonexistence is equivalent to Mathlib's exact RH statement.

These equivalences are audit facts, not closure proofs.
-/

/-- Universal exclusion of globally aligned residual states. -/
def GlobalBottomResidualExclusion : Prop :=
  ∀ Q : ℕ, ∀ s : GlobalBottomResidualState Q, False

/-- Historical dominance-shaped gate, retained only for strength auditing. -/
def LegacyGlobalBottomResidualPrimeDominance
    {Q : ℕ} (s : GlobalBottomResidualState Q) : Prop :=
  canonicalPrimeFreeBudget
      s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)
      (s.groundTrial : EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) ≤
    -canonicalPrimeRemainderEnergy
      s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)
      (s.groundTrial : EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))

/-- Historical universal arithmetic closure gate. -/
def LegacyGlobalBottomArithmeticClosure : Prop :=
  ∀ Q : ℕ, ∀ s : GlobalBottomResidualState Q,
    LegacyGlobalBottomResidualPrimeDominance s

theorem legacyGlobalBottomArithmeticClosure_iff_residualExclusion :
    LegacyGlobalBottomArithmeticClosure ↔ GlobalBottomResidualExclusion := by
  constructor
  · intro hclose Q s
    have hfail := s.groundTrial_primeRemainder_failure
    exact (not_lt_of_ge (hclose Q s)) hfail
  · intro hexcl Q s
    exact False.elim (hexcl Q s)

/-- Residual exclusion implies the repository-carrier critical-line statement. -/
theorem criticalLine_of_globalBottomResidualExclusion
    (hkill : GlobalBottomResidualExclusion) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  obtain ⟨Q, s, _hlarge⟩ :=
    exists_arbitrarilyLarge_globalBottomResidualState_of_offLine_zero
      ⟨ρ, hρ⟩ hoff 0
  exact hkill Q s

/-- Residual exclusion is sufficient for literal Mathlib RH. -/
theorem riemannHypothesis_of_globalBottomResidualExclusion
    (hkill : GlobalBottomResidualExclusion) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  exact criticalLine_of_globalBottomResidualExclusion hkill s hmem

/-- Mathlib RH forbids every residual state because each one contains an
aligned retained negative-energy certificate. -/
theorem globalBottomResidualExclusion_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    GlobalBottomResidualExclusion := by
  intro Q s
  have hline : ∀ rho ∈ zetaZeroConfig.carrier, rho.re = 1 / 2 := by
    intro rho hrho
    exact RH_implies_on_line hRH (by simpa using hrho)
  exact no_regularCellMinimalNegativeEnergyCertificate_of_criticalLine
    hline Q s.aligned

theorem globalBottomResidualExclusion_iff_riemannHypothesis :
    GlobalBottomResidualExclusion ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_globalBottomResidualExclusion,
    globalBottomResidualExclusion_of_riemannHypothesis⟩

/-- Dumbassery firewall: the old universal arithmetic closure is exactly RH
in logical strength. -/
theorem legacyGlobalBottomArithmeticClosure_iff_riemannHypothesis :
    LegacyGlobalBottomArithmeticClosure ↔ RiemannHypothesis := by
  rw [legacyGlobalBottomArithmeticClosure_iff_residualExclusion,
    globalBottomResidualExclusion_iff_riemannHypothesis]

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.legacyGlobalBottomArithmeticClosure_iff_residualExclusion
#print axioms Zeta23.ExceptionalZero.globalBottomResidualExclusion_iff_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.legacyGlobalBottomArithmeticClosure_iff_riemannHypothesis
