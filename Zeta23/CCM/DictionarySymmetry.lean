import Zeta23.CCM.DictionaryDeterministicRHS

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ArithmeticFunction

/-!
# Symmetry of the production dictionary matrix

This module records the deterministic symmetry needed before real polarization
of the smooth-core quadratic identity.  No zero sum or explicit formula is used.
-/

/-- The elementary finite kernel is symmetric in its two Fourier indices. -/
theorem qBasis_comm (n m : ℤ) (y L : ℝ) :
    qBasis n m y L = qBasis m n y L := by
  by_cases h : n = m
  · subst m
    rfl
  · have h' : m ≠ n := Ne.symm h
    rw [qBasis, if_neg h, qBasis, if_neg h']
    push_cast
    ring

/-- The pole component is symmetric. -/
theorem poleComponent_comm (n m : ℤ) (L : ℝ) :
    poleComponent n m L = poleComponent m n L := by
  unfold poleComponent
  push_cast
  ring

/-- The archimedean component is symmetric. -/
theorem archComponent_comm (n m : ℤ) (L : ℝ) :
    archComponent n m L = archComponent m n L := by
  by_cases h : n = m
  · subst m
    rfl
  · have h' : m ≠ n := Ne.symm h
    rw [archComponent, if_neg h, archComponent, if_neg h']
    push_cast
    ring

/-- The finite prime-power component is symmetric. -/
theorem primeComponent_comm (n m : ℤ) (L : ℝ) :
    primeComponent n m L = primeComponent m n L := by
  unfold primeComponent
  apply Finset.sum_congr rfl
  intro k hk
  rw [qBasis_comm]

/-- Every scalar CCM entry is symmetric. -/
theorem entry_comm (n m : ℤ) (L : ℝ) :
    entry n m L = entry m n L := by
  rw [entry, entry, poleComponent_comm, archComponent_comm, primeComponent_comm]

/-- The canonical finite CCM matrix is symmetric entrywise. -/
theorem finiteMatrix_apply_comm
    (L : ℝ) (N : ℕ) (i j : Fin (2 * N + 1)) :
    finiteMatrix L N i j = finiteMatrix L N j i := by
  simp only [finiteMatrix_apply]
  push_cast
  exact_mod_cast entry_comm (centeredIndex N i) (centeredIndex N j) L

/-- The production dictionary matrix is symmetric entrywise. -/
theorem dictionaryMatrix_apply_comm
    (L : ℝ) (N : ℕ) (i j : Fin (2 * N + 1)) :
    dictionaryMatrix L N i j = dictionaryMatrix L N j i := by
  rw [dictionaryMatrix_apply, dictionaryMatrix_apply, finiteMatrix_apply_comm]
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp [h, h']

end Zeta23.CCM
