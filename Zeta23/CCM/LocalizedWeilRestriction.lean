import Zeta23.CCM.LocalizedFiniteSpace
import Zeta23.CCM.DictionaryRHSIdentity
import Zeta23.CCM.CutoffFreeMatrix

noncomputable section

namespace Zeta23.CCM

/-!
# G1-A: additive localized Weil restriction firewall

This module performs the shortest theorem-authoritative composition available
after G0-B.

The external Connes--Consani--Moscovici source uses the even additive
correlation q(f,g) and a positive-half functional PsiSharp after the logarithmic
coordinate change.  G0-B proves that the repository's actual symmetrized
localized correlation of a finite vector is exactly twice the production
`dictionaryTest`.

Accordingly, this file defines the repository-side *additive half-correlation
RHS* and proves that its restriction to every actual full-complex localized
finite vector is exactly the quadratic form of `cutoffFreeMatrix`.

Claim firewall: this definition is NOT declared to be the external localized
Weil form QW_lambda.  The source-coordinate/kappa/PsiSharp identification is a
separate downstream obligation.  The final conditional theorem in this file
isolates that remaining obligation explicitly.
-/

/-- Half of the actual symmetrized localized correlation.

G0-B theorem-locks the factor two between the full source correlation and the
production dictionary convention. -/
def localizedWeilHalfTest (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun y => (1 / 2 : ℂ) * localizedWeilCorrelation f g y

/-- Repository additive explicit-formula RHS evaluated on the half-correlation.

This is the finite-restriction candidate suggested by the source evenization
identity.  It is deliberately not named or claimed as the external CCM
`QW_lambda` form. -/
def localizedWeilAdditiveRHS (f g : ℝ → ℂ) : ℂ :=
  Zeta23.EF.literatureRHS (localizedWeilHalfTest f g)

/-- G0-B normalization cashed out globally: the half-correlation of an actual
finite vector is exactly the theorem-authoritative production dictionary test. -/
theorem localizedWeilHalfTest_finiteVector_eq_dictionaryTest
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ}
    (hL : 0 < L) :
    localizedWeilHalfTest
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u) =
    dictionaryTest N u L := by
  unfold localizedWeilHalfTest
  rw [localizedWeilCorrelation_finiteVector_eq_two_mul_dictionaryTest N u hL]
  funext y
  ring

/-- The additive half-correlation RHS on the actual finite vector is exactly the
existing complex-coefficient deterministic dictionary quadratic form. -/
theorem localizedWeilAdditiveRHS_finiteVector_eq_dictionaryQuadraticForm
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ}
    (hL : 0 < L) :
    localizedWeilAdditiveRHS
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u) =
    quadraticForm (dictionaryMatrix L N) u := by
  unfold localizedWeilAdditiveRHS
  rw [localizedWeilHalfTest_finiteVector_eq_dictionaryTest N u hL]
  exact dictionaryRHS_dictionaryTest_eq_quadraticForm N u hL

/-- **G1-A unconditional finite endpoint.**

For the full complex centered coefficient sector, the repository additive
half-correlation Weil RHS has exactly the independently defined cutoff-free
CCM/CvS finite matrix.

This is a finite additive-functional restriction theorem.  It does not by
itself identify the external CCM localized form `QW_lambda` with
`localizedWeilAdditiveRHS`. -/
theorem localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ}
    (hL : 0 < L) :
    localizedWeilAdditiveRHS
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u) =
    quadraticForm (cutoffFreeMatrix L N) u := by
  rw [localizedWeilAdditiveRHS_finiteVector_eq_dictionaryQuadraticForm N u hL]
  rw [cutoffFreeMatrix_eq_dictionaryMatrix]

/-- Source-facing lambda wrapper with the exact convention `L = 2*log(lambda)`. -/
theorem localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm_ofLambda
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {lam : ℝ}
    (hlam : 1 < lam) :
    localizedWeilAdditiveRHS
      (localizedFiniteVector (2 * Real.log lam) N u)
      (localizedFiniteVector (2 * Real.log lam) N u) =
    quadraticForm (cutoffFreeMatrixOfLambda lam N) u := by
  have hlog : 0 < Real.log lam := Real.log_pos hlam
  have hL : 0 < 2 * Real.log lam := by positivity
  simpa [cutoffFreeMatrixOfLambda] using
    localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
      N u hL

/-- Explicit firewall for the remaining source-identification obligation.

An ambient sesquilinear/quadratic functional matches the repository additive
RHS on the actual localized finite spaces iff it satisfies this finite-sector
law.  G1-B must discharge such an identification for the genuine external
localized Weil form rather than defining it into existence. -/
def MatchesLocalizedWeilAdditiveRHSOnFiniteSpace
    (Q : (ℝ → ℂ) → (ℝ → ℂ) → ℂ) : Prop :=
  ∀ (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ),
    0 < L →
    Q
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u) =
    localizedWeilAdditiveRHS
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u)

/-- Once an ambient form satisfies the explicit G1-B source-identification
gate, its finite restriction is automatically the canonical cutoff-free matrix.
No further finite algebra remains. -/
theorem finiteRestriction_eq_cutoffFreeQuadraticForm_of_matches
    (Q : (ℝ → ℂ) → (ℝ → ℂ) → ℂ)
    (hQ : MatchesLocalizedWeilAdditiveRHSOnFiniteSpace Q)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ}
    (hL : 0 < L) :
    Q
      (localizedFiniteVector L N u)
      (localizedFiniteVector L N u) =
    quadraticForm (cutoffFreeMatrix L N) u := by
  rw [hQ L N u hL]
  exact localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
    N u hL

end Zeta23.CCM

#print axioms Zeta23.CCM.localizedWeilHalfTest_finiteVector_eq_dictionaryTest
#print axioms Zeta23.CCM.localizedWeilAdditiveRHS_finiteVector_eq_dictionaryQuadraticForm
#print axioms Zeta23.CCM.localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm
#print axioms Zeta23.CCM.localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm_ofLambda
#print axioms Zeta23.CCM.finiteRestriction_eq_cutoffFreeQuadraticForm_of_matches
