import Zeta23.CCM.CanonicalGroundPropagation
import Zeta23.CCM.CanonicalUniformDomination
import Zeta23.RHRC.ClosureObligationBindings
import Zeta23.ExceptionalZero.GlobalParityBottomSignOpposition
import Zeta23.ExceptionalZero.GlobalFirstBadOneStepDomination
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

noncomputable section

namespace Zeta23.RHRC

open Complex
open Zeta23.CCM
open Zeta23.ExceptionalZero

/-!
# Post-#276 closure-strength audit

These are audit theorems, not active closure premises.  They classify two
universal campaign targets by composing them with already-proved
off-line-zero countercertificates.

* global successor-ground propagation from the #276 base is sufficient for RH;
* uniform one-step domination is sufficient for RH.

Therefore neither proposition should be treated as a modest independent
sub-RH lemma.  Fixed-cell continuity/propagation and local seam control remain
legitimate intermediate mathematics.

RH remains OPEN.
-/

/-- The campaign's global ground-propagation proposition at the small-aperture
anchor is already sufficient for literal Mathlib RH.  This theorem does not
establish that propagation proposition. -/
theorem riemannHypothesis_of_canonicalGlobalGroundPropagation_smallAperture
    (hprop :
      CanonicalGlobalGroundPropagation ((1 : ℝ) / 512)) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  by_contra hoff
  have hoff' : ((⟨s, hmem⟩ : zetaZeroConfig.carrier) : ℂ).re ≠ 1 / 2 := by
    simpa using hoff
  obtain ⟨N, hN, Lneg, hLneg, hbase, hneg⟩ :=
    exists_fixedN_ground_sign_opposition_of_offLine_zero
      (Lsmall := (1 : ℝ) / 512)
      (by norm_num) le_rfl
      (⟨s, hmem⟩ : zetaZeroConfig.carrier) hoff'
  have hbase_nonneg :
      0 ≤ globalParitySuccessorBottom ((1 : ℝ) / 512) N := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hbase
  have hlater_nonneg :
      0 ≤ globalParitySuccessorBottom Lneg N :=
    hprop N hN Lneg (le_of_lt hLneg) hbase_nonneg
  exact (not_lt_of_ge hlater_nonneg) hneg

/-- Uniform canonical one-step domination is already sufficient for literal
Mathlib RH because every hypothetical off-line zero produces a global first-bad
state where the same domination certificate fails.  The premise remains OPEN. -/
theorem riemannHypothesis_of_canonicalUniformDomination
    (hdomAll : CanonicalUniformDomination) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by
    simpa using hs
  by_contra hoff
  have hoff' : ((⟨s, hmem⟩ : zetaZeroConfig.carrier) : ℂ).re ≠ 1 / 2 := by
    simpa using hoff
  obtain ⟨L, hL, N, _hN, p, _hprev, _hbad, _hmin, hfail⟩ :=
    exists_globalFirstBad_not_canonicalOneStepDomination_of_offLine_zero
      (⟨s, hmem⟩ : zetaZeroConfig.carrier) hoff'
  have hdom : canonicalOneStepDomination p L N :=
    canonicalSchurCertificateAt_of_uniformDomination hdomAll p L hL N
  exact hfail hdom

/-- The historical B3 bridge follows immediately once the B2 premise is
assumed.  This proves only a conditional implication; it does not prove B2 or
all-aperture positivity. -/
theorem canonicalAllAperturePositivity_of_canonicalUniformDomination
    (hdomAll : CanonicalUniformDomination) :
    CanonicalAllAperturePositivity :=
  canonicalAllAperturePositivity_iff_riemannHypothesis.mpr
    (riemannHypothesis_of_canonicalUniformDomination hdomAll)

end Zeta23.RHRC

#print axioms Zeta23.RHRC.riemannHypothesis_of_canonicalGlobalGroundPropagation_smallAperture
#print axioms Zeta23.RHRC.riemannHypothesis_of_canonicalUniformDomination
#print axioms Zeta23.RHRC.canonicalAllAperturePositivity_of_canonicalUniformDomination
