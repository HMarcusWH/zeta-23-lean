import Zeta23.CCM.DictionaryZeroSideBridge

noncomputable section

namespace Zeta23.CCM

open Matrix

/-!
# Cutoff-free CCM finite matrix

This module formalizes the cutoff-free finite CCM/CvS source convention
independently from `finiteMatrix`, `dictionaryMatrix`, and `zeroSideMatrix`.

The pinned external normalization audit identified the primitive convention map

```text
alpha_reference = alpha_ours
beta_reference  = beta_ours
gamma_reference = gamma_ours - cCorrection(L)
pole_reference  = pole_ours
```

The definitions below encode that convention directly and then prove, in Lean,
that the resulting full centered `(2N+1) x (2N+1)` matrix is exactly

```text
finiteMatrix(L,N) + 2*cCorrection(L)*I.
```

Composing with the already-proved finite zeta zero-side bridge then identifies
the actual `zeroSideMatrix` with this cutoff-free matrix.

This is a finite matrix-formula identification only.  It does not prove a
Hilbert-space Galerkin restriction theorem, positivity, finite-to-infinite
convergence, or RH.
-/

/-- Cutoff-free diagonal archimedean primitive.  This is the convention
isolated by the independent CCM/CvS normalization audit. -/
def cutoffFreeGammaL (n : ℤ) (L : ℝ) : ℝ :=
  gammaL n L - cCorrection L

/-- Archimedean channel in the cutoff-free finite CCM/CvS convention. -/
def cutoffFreeArchComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * cutoffFreeGammaL n L - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- Complete scalar entry in the cutoff-free finite CCM/CvS convention. -/
def cutoffFreeEntry (n m : ℤ) (L : ℝ) : ℝ :=
  poleComponent n m L - cutoffFreeArchComponent n m L - primeComponent n m L

/-- Full cutoff-free finite matrix on centered Fourier indices `-N,...,N`. -/
def cutoffFreeMatrix (L : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    (cutoffFreeEntry (centeredIndex N i) (centeredIndex N j) L : ℂ)

@[simp] theorem cutoffFreeMatrix_apply
    (L : ℝ) (N : ℕ) (i j : Fin (2 * N + 1)) :
    cutoffFreeMatrix L N i j =
      (cutoffFreeEntry (centeredIndex N i) (centeredIndex N j) L : ℂ) := rfl

/-- The cutoff-free archimedean convention differs from the fork-owned
finite-matrix convention only on the diagonal, by exactly
`-2*cCorrection(L)`. -/
theorem cutoffFreeArchComponent_eq_archComponent_sub_two_correction
    (n m : ℤ) (L : ℝ) :
    cutoffFreeArchComponent n m L =
      archComponent n m L -
        (if n = m then 2 * cCorrection L else 0) := by
  by_cases h : n = m
  · subst m
    simp [cutoffFreeArchComponent, cutoffFreeGammaL, archComponent]
    ring
  · simp [cutoffFreeArchComponent, archComponent, h]

/-- Entrywise normalization map from the fork-owned finite CCM convention to
the cutoff-free convention. -/
theorem cutoffFreeEntry_eq_entry_add_two_correction
    (n m : ℤ) (L : ℝ) :
    cutoffFreeEntry n m L =
      entry n m L +
        (if n = m then 2 * cCorrection L else 0) := by
  rw [cutoffFreeEntry, entry,
    cutoffFreeArchComponent_eq_archComponent_sub_two_correction]
  by_cases h : n = m
  · simp [h]
    ring
  · simp [h]

/-- Exact full-matrix normalization theorem:
`Q_inf = M + 2*cCorrection(L)*I`. -/
theorem cutoffFreeMatrix_eq_dictionaryMatrix
    (L : ℝ) (N : ℕ) :
    cutoffFreeMatrix L N = dictionaryMatrix L N := by
  ext i j
  rw [cutoffFreeMatrix_apply, dictionaryMatrix_apply, finiteMatrix_apply,
    cutoffFreeEntry_eq_entry_add_two_correction]
  by_cases hij : i = j
  · subst j
    simp
  · have hidx : centeredIndex N i ≠ centeredIndex N j := by
      intro h
      exact hij (centeredIndex_injective N h)
    simp [hij, hidx]

/-- Registry-facing source-convention normalization. -/
theorem cutoffFreeMatrix_eq_finiteMatrix_add_correction
    (L : ℝ) (N : ℕ) :
    cutoffFreeMatrix L N =
      finiteMatrix L N +
        ((2 * cCorrection L : ℝ) : ℂ) •
          (1 : Matrix
            (Fin (2 * N + 1))
            (Fin (2 * N + 1)) ℂ) := by
  simpa [dictionaryMatrix] using cutoffFreeMatrix_eq_dictionaryMatrix L N

/-- Actual zeta zero-side matrix equals the independently defined cutoff-free
finite CCM matrix for every finite size and positive aperture. -/
theorem zeroSideMatrix_eq_cutoffFreeMatrix
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideMatrix hs N L = cutoffFreeMatrix L N := by
  rw [zeroSideMatrix_eq_dictionaryMatrix hs N hL,
    cutoffFreeMatrix_eq_dictionaryMatrix]

end Zeta23.CCM

#print axioms Zeta23.CCM.cutoffFreeArchComponent_eq_archComponent_sub_two_correction
#print axioms Zeta23.CCM.cutoffFreeEntry_eq_entry_add_two_correction
#print axioms Zeta23.CCM.cutoffFreeMatrix_eq_dictionaryMatrix
#print axioms Zeta23.CCM.cutoffFreeMatrix_eq_finiteMatrix_add_correction
#print axioms Zeta23.CCM.zeroSideMatrix_eq_cutoffFreeMatrix
