import Zeta23.CCM.SourceNormalizationRepair

noncomputable section

namespace Zeta23.CCM

open Matrix MeasureTheory
open scoped Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4a: canonical source channels

This module exposes the production `canonicalSourceMatrix` as exact pole,
canonical equation-(4.4) archimedean, and prime matrices.  It also removes the
index-independent archimedean scalar from the source formula using the already
proved corrected equation-(4.11) representation.

The printed equation-(4.11) correction proposition is not used.  No sign,
nonzeroness, positivity, branch exclusion, or RH conclusion is asserted.
-/

/-- Pole channel of the production canonical source matrix. -/
def canonicalPoleMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (poleComponent (centeredIndex K i) (centeredIndex K j) L : ℂ)

/-- Direct equation-(4.4) archimedean channel of the production matrix. -/
def canonicalArchMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (sourceEq44ArchComponent (centeredIndex K i) (centeredIndex K j) L : ℂ)

/-- Finite prime-power channel of the production canonical source matrix. -/
def canonicalPrimeMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (primeComponent (centeredIndex K i) (centeredIndex K j) L : ℂ)

@[simp] theorem canonicalPoleMatrix_apply
    (L : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    canonicalPoleMatrix L K i j =
      (poleComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) := rfl

@[simp] theorem canonicalArchMatrix_apply
    (L : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    canonicalArchMatrix L K i j =
      (sourceEq44ArchComponent
        (centeredIndex K i) (centeredIndex K j) L : ℂ) := rfl

@[simp] theorem canonicalPrimeMatrix_apply
    (L : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    canonicalPrimeMatrix L K i j =
      (primeComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) := rfl

/-- Exact matrix-level production decomposition.  The prime and archimedean
channels enter with the same minus signs as direct source equation (4.4). -/
theorem canonicalSourceMatrix_eq_pole_sub_arch_sub_prime
    (L : ℝ) (K : ℕ) :
    canonicalSourceMatrix L K =
      canonicalPoleMatrix L K -
        canonicalArchMatrix L K -
          canonicalPrimeMatrix L K := by
  rw [canonicalSourceMatrix_eq_sourceEq44Matrix]
  ext i j
  simp [sourceEq44Matrix, sourceEq44Entry,
    canonicalPoleMatrix, canonicalArchMatrix, canonicalPrimeMatrix]

/-- Index-dependent regularized part of the canonical diagonal gamma term. -/
def reducedCanonicalGammaL (n : ℤ) (L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, sourceEq411RhsCosMinusOneIntegrand n L x

/-- The index-independent scalar added to every diagonal entry of the canonical
archimedean channel when the corrected equation-(4.11) representation is used. -/
def canonicalArchScalarCorrection (L : ℝ) : ℝ :=
  2 * (sourceEq411DerivedCorrection L + wCorrection L)

/-- Safe corrected representation of the direct equation-(4.4) diagonal
primitive. -/
theorem sourceEq44GammaL_eq_reducedCanonicalGammaL
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    sourceEq44GammaL n L =
      reducedCanonicalGammaL n L +
        sourceEq411DerivedCorrection L + wCorrection L := by
  have h :=
    canonicalSourceGammaL_eq_rhs_add_derivedCorrection (n := n) hL
  simpa [canonicalSourceGammaL, reducedCanonicalGammaL] using h

/-- Canonical archimedean entry with every index-independent diagonal scalar
removed. -/
def reducedCanonicalArchComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * reducedCanonicalGammaL n L - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- Entrywise canonical archimedean decomposition into the reduced source term
plus one scalar diagonal correction. -/
theorem sourceEq44ArchComponent_eq_reducedCanonicalArchComponent_add_scalar
    (n m : ℤ) {L : ℝ} (hL : 0 < L) :
    sourceEq44ArchComponent n m L =
      reducedCanonicalArchComponent n m L +
        if n = m then canonicalArchScalarCorrection L else 0 := by
  by_cases hnm : n = m
  · subst m
    rw [sourceEq44ArchComponent, reducedCanonicalArchComponent]
    simp only [if_pos rfl]
    rw [sourceEq44GammaL_eq_reducedCanonicalGammaL n hL]
    unfold canonicalArchScalarCorrection
    ring
  · simp [sourceEq44ArchComponent, reducedCanonicalArchComponent, hnm]

/-- Matrix of the index-dependent canonical archimedean channel. -/
def reducedCanonicalArchMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    (reducedCanonicalArchComponent
      (centeredIndex K i) (centeredIndex K j) L : ℂ)

@[simp] theorem reducedCanonicalArchMatrix_apply
    (L : ℝ) (K : ℕ) (i j : Fin (2 * K + 1)) :
    reducedCanonicalArchMatrix L K i j =
      (reducedCanonicalArchComponent
        (centeredIndex K i) (centeredIndex K j) L : ℂ) := rfl

/-- Matrix-level version of the corrected archimedean scalar separation. -/
theorem canonicalArchMatrix_eq_reducedCanonicalArchMatrix_add_scalar
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    canonicalArchMatrix L K =
      reducedCanonicalArchMatrix L K +
        ((canonicalArchScalarCorrection L : ℝ) : ℂ) •
          (1 : Matrix
            (Fin (2 * K + 1))
            (Fin (2 * K + 1)) ℂ) := by
  ext i j
  rw [canonicalArchMatrix_apply, reducedCanonicalArchMatrix_apply]
  rw [sourceEq44ArchComponent_eq_reducedCanonicalArchComponent_add_scalar
    (centeredIndex K i) (centeredIndex K j) hL]
  by_cases hij : i = j
  · subst j
    simp
  · have hidx : centeredIndex K i ≠ centeredIndex K j := by
      exact fun h => hij ((centeredIndex_injective K) h)
    simp [hij, hidx]

/-- Diagonal part of the reduced canonical archimedean matrix. -/
def reducedCanonicalArchDiagonalMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    if i = j then
      (reducedCanonicalArchComponent
        (centeredIndex K i) (centeredIndex K i) L : ℂ)
    else 0

/-- Off-diagonal part of the reduced canonical archimedean matrix. -/
def reducedCanonicalArchOffDiagonalMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    if i = j then 0
    else
      (reducedCanonicalArchComponent
        (centeredIndex K i) (centeredIndex K j) L : ℂ)

/-- Exact diagonal/off-diagonal split of the reduced archimedean matrix. -/
theorem reducedCanonicalArchMatrix_eq_diagonal_add_offDiagonal
    (L : ℝ) (K : ℕ) :
    reducedCanonicalArchMatrix L K =
      reducedCanonicalArchDiagonalMatrix L K +
        reducedCanonicalArchOffDiagonalMatrix L K := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [reducedCanonicalArchMatrix,
      reducedCanonicalArchDiagonalMatrix,
      reducedCanonicalArchOffDiagonalMatrix]
  · simp [reducedCanonicalArchMatrix,
      reducedCanonicalArchDiagonalMatrix,
      reducedCanonicalArchOffDiagonalMatrix, hij]

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSourceMatrix_eq_pole_sub_arch_sub_prime
#print axioms Zeta23.CCM.sourceEq44GammaL_eq_reducedCanonicalGammaL
#print axioms Zeta23.CCM.sourceEq44ArchComponent_eq_reducedCanonicalArchComponent_add_scalar
#print axioms Zeta23.CCM.canonicalArchMatrix_eq_reducedCanonicalArchMatrix_add_scalar
#print axioms Zeta23.CCM.reducedCanonicalArchMatrix_eq_diagonal_add_offDiagonal
