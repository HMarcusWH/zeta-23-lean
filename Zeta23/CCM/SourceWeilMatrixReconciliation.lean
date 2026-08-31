import Zeta23.CCM.CutoffFreeMatrix

noncomputable section

namespace Zeta23.CCM

open MeasureTheory
open scoped Interval ArithmeticFunction

/-!
# G1-B0: source Weil normalization firewall

Post-G1-A source inspection exposed two distinct normalization seams in the
Connes--Consani--Moscovici Section 4 formulas.

* Equation (4.4) gives the archimedean Weil contribution directly in terms of
  `q(U_n,U_m)`.
* Equation (4.11) rewrites the diagonal integral using a correction `c(L)`.
* Equation (4.14) then defines a lighter-notation gamma with another explicit
  `+ c(L)`.

The repository already has the printed-(4.14) convention as `gammaL` and the
independently audited convention `cutoffFreeGammaL = gammaL-cCorrection`.

This module does NOT silently identify the equation-(4.4) primitive with either
one.  Instead it formalizes all three ingredients independently and theorem-
locks the exact pointwise correction-factor discrepancy visible between the
algebraic subtraction implied by rho(x) and the printed `c(L)` integrand.

Claim firewall: no theorem below identifies the external ambient QW_lambda
restriction with `cutoffFreeMatrix`.  That remains open until the source
normalization seam is resolved.
-/

/-- Regularized integrand appearing in the equation-(4.4) diagonal after
substituting `q(U_n,U_n)(x)=2(1-x/L)cos(2*pi*n*x/L)`: the non-beta part uses
`(cos-1)*rho`. -/
def sourceEq44CosMinusOneIntegrand
    (n : ℤ) (L x : ℝ) : ℝ :=
  if x = 0 then 0
  else
    (Real.cos (2 * Real.pi * (n : ℝ) * x / L) - 1) * archDensity x

/-- Regularized left-hand integrand of the source equation (4.11), also the
integral appearing inside the printed equation-(4.14) gamma. -/
def sourceEq411LhsIntegrand
    (n : ℤ) (L x : ℝ) : ℝ :=
  if x = 0 then 1 / 4
  else
    (Real.cos (2 * Real.pi * (n : ℝ) * x / L) - Real.exp (-x / 2))
      * archDensity x

/-- Correction integrand forced pointwise by subtracting the equation-(4.4)
`(cos-1)rho` integrand from the equation-(4.11) left-hand integrand. -/
def sourceEq411DerivedCorrectionIntegrand (x : ℝ) : ℝ :=
  if x = 0 then 1 / 4
  else
    (1 - Real.exp (-x / 2)) * archDensity x

/-- Exact pointwise algebra behind the equation-(4.11) rewrite.

This theorem does not use the printed `cCorrectionIntegrand`; it computes the
correction forced by the two displayed rho-weighted integrands themselves. -/
theorem sourceEq411_integrand_decomposition
    (n : ℤ) (L x : ℝ) :
    sourceEq411LhsIntegrand n L x =
      sourceEq44CosMinusOneIntegrand n L x +
        sourceEq411DerivedCorrectionIntegrand x := by
  by_cases h : x = 0
  · subst x
    simp [sourceEq411LhsIntegrand, sourceEq44CosMinusOneIntegrand,
      sourceEq411DerivedCorrectionIntegrand]
  · simp [sourceEq411LhsIntegrand, sourceEq44CosMinusOneIntegrand,
      sourceEq411DerivedCorrectionIntegrand, h]
    ring

/-- The correction forced by the rho-weighted algebra is the printed
`cCorrectionIntegrand` multiplied by `exp(x/2)`.

This is the exact normalization firewall discovered in the post-green source
audit.  No inequality/nonzero claim is made here. -/
theorem sourceEq411DerivedCorrectionIntegrand_eq_exp_mul_cCorrectionIntegrand
    (x : ℝ) :
    sourceEq411DerivedCorrectionIntegrand x =
      Real.exp (x / 2) * cCorrectionIntegrand x := by
  by_cases h : x = 0
  · subst x
    simp [sourceEq411DerivedCorrectionIntegrand, cCorrectionIntegrand]
  · simp [sourceEq411DerivedCorrectionIntegrand, cCorrectionIntegrand,
      archDensity, h]
    ring

/-- Equation-(4.4) diagonal primitive before the beta term. -/
def sourceEq44GammaL (n : ℤ) (L : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..L, sourceEq44CosMinusOneIntegrand n L x)
    + wCorrection L

/-- Left-hand equation-(4.11) primitive, without adding the printed correction
again. -/
def sourceEq411LhsGammaL (n : ℤ) (L : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..L, sourceEq411LhsIntegrand n L x)
    + wCorrection L

/-- The equation-(4.11) left-hand primitive is exactly the independently audited
cutoff-free primitive.  This is an internal formula identity only. -/
theorem sourceEq411LhsGammaL_eq_cutoffFreeGammaL
    (n : ℤ) (L : ℝ) :
    sourceEq411LhsGammaL n L = cutoffFreeGammaL n L := by
  unfold sourceEq411LhsGammaL sourceEq411LhsIntegrand
  unfold cutoffFreeGammaL gammaL
  ring

/-- Exact relation to the repository's printed-(4.14) convention:
`gammaL` adds one explicit `cCorrection(L)` to the equation-(4.11)
left-hand primitive. -/
theorem gammaL_eq_sourceEq411LhsGammaL_add_correction
    (n : ℤ) (L : ℝ) :
    gammaL n L = sourceEq411LhsGammaL n L + cCorrection L := by
  unfold gammaL sourceEq411LhsGammaL sourceEq411LhsIntegrand
  ring

/-- The exact integrated correction assertion needed to pass from the raw
source equation-(4.4) primitive to the printed equation-(4.11) rewrite.

It is intentionally a named OPEN proposition, not a theorem: the pointwise
firewall above shows that the algebraically forced correction integrand and the
repository's printed `cCorrectionIntegrand` differ by an `exp(x/2)` factor. -/
def SourceEq411CorrectionIdentity : Prop :=
  ∀ (n : ℤ) (L : ℝ),
    sourceEq411LhsGammaL n L =
      sourceEq44GammaL n L + cCorrection L

/-- Archimedean matrix entry normalized directly from equation (4.4). -/
def sourceEq44ArchComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * sourceEq44GammaL n L - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- Archimedean matrix entry using the left-hand integral of equation (4.11),
without re-adding the printed correction. -/
def sourceEq411LhsArchComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * sourceEq411LhsGammaL n L - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- The equation-(4.11)-left-hand archimedean convention is exactly the
cutoff-free archimedean convention. -/
theorem sourceEq411LhsArchComponent_eq_cutoffFreeArchComponent
    (n m : ℤ) (L : ℝ) :
    sourceEq411LhsArchComponent n m L =
      cutoffFreeArchComponent n m L := by
  by_cases h : n = m
  · subst m
    simp [sourceEq411LhsArchComponent, cutoffFreeArchComponent,
      sourceEq411LhsGammaL_eq_cutoffFreeGammaL]
  · simp [sourceEq411LhsArchComponent, cutoffFreeArchComponent, h]

/-- Full finite formula using the equation-(4.4) archimedean normalization and
the already theorem-authoritative pole and prime channels.  No equality to an
existing production matrix is asserted. -/
def sourceEq44Entry (n m : ℤ) (L : ℝ) : ℝ :=
  poleComponent n m L - sourceEq44ArchComponent n m L - primeComponent n m L

/-- Full centered finite matrix using the raw equation-(4.4) normalization. -/
def sourceEq44Matrix (L : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    (sourceEq44Entry (centeredIndex N i) (centeredIndex N j) L : ℂ)

/-- Full finite formula using the equation-(4.11) left-hand normalization. -/
def sourceEq411LhsEntry (n m : ℤ) (L : ℝ) : ℝ :=
  poleComponent n m L -
    sourceEq411LhsArchComponent n m L -
    primeComponent n m L

/-- The equation-(4.11)-left-hand full entry is exactly the cutoff-free entry. -/
theorem sourceEq411LhsEntry_eq_cutoffFreeEntry
    (n m : ℤ) (L : ℝ) :
    sourceEq411LhsEntry n m L = cutoffFreeEntry n m L := by
  rw [sourceEq411LhsEntry, cutoffFreeEntry,
    sourceEq411LhsArchComponent_eq_cutoffFreeArchComponent]

/-- Full centered matrix using the equation-(4.11) left-hand normalization. -/
def sourceEq411LhsMatrix (L : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    (sourceEq411LhsEntry (centeredIndex N i) (centeredIndex N j) L : ℂ)

/-- **G1-B0 safe endpoint.**

The finite formula built from the left-hand integral of equation (4.11), before
adding the printed correction again, is exactly the independently audited
cutoff-free matrix.

This theorem deliberately does NOT identify `sourceEq44Matrix` with
`cutoffFreeMatrix`. -/
theorem sourceEq411LhsMatrix_eq_cutoffFreeMatrix
    (L : ℝ) (N : ℕ) :
    sourceEq411LhsMatrix L N = cutoffFreeMatrix L N := by
  ext i j
  simp [sourceEq411LhsMatrix, cutoffFreeMatrix,
    sourceEq411LhsEntry_eq_cutoffFreeEntry]

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceEq411_integrand_decomposition
#print axioms Zeta23.CCM.sourceEq411DerivedCorrectionIntegrand_eq_exp_mul_cCorrectionIntegrand
#print axioms Zeta23.CCM.sourceEq411LhsGammaL_eq_cutoffFreeGammaL
#print axioms Zeta23.CCM.gammaL_eq_sourceEq411LhsGammaL_add_correction
#print axioms Zeta23.CCM.sourceEq411LhsArchComponent_eq_cutoffFreeArchComponent
#print axioms Zeta23.CCM.sourceEq411LhsEntry_eq_cutoffFreeEntry
#print axioms Zeta23.CCM.sourceEq411LhsMatrix_eq_cutoffFreeMatrix
