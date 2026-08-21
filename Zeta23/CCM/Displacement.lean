import Zeta23.CCM.DividedDifference
import Zeta23.ExceptionalZero.DisplacementTransfer

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped ArithmeticFunction

/-- Pole contribution to the displacement-generating scalar sequence. -/
def poleSeq (n : ℤ) (L : ℝ) : ℝ :=
  let κ : ℝ := 16 * Real.pi ^ 2
  let C : ℝ := 32 * L * Real.sinh (L / 4) ^ 2
  C * (n : ℝ) / (L ^ 2 + κ * (n : ℝ) ^ 2)

/-- Prime contribution to the displacement-generating scalar sequence. -/
def primeSeq (n : ℤ) (L : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    (Λ k / Real.sqrt k : ℝ) *
      (Real.sin (2 * Real.pi * (n : ℝ) * Real.log k / L) / Real.pi)

/-- Scalar sequence whose divided differences generate the off-diagonal CCM entries. -/
def displacementSeq (n : ℤ) (L : ℝ) : ℝ :=
  poleSeq n L + alphaL n L + primeSeq n L

/-- Complex source potential underlying the concrete finite CCM divided-difference matrix. -/
def ccmPotential (L : ℝ) (n : ℤ) : ℂ := (displacementSeq n L : ℂ)

/-- Concrete CCM diagonal data, deliberately separated from the off-diagonal source potential. -/
def ccmDiagonal (L : ℝ) (n : ℤ) : ℂ := (entry n n L : ℂ)

/-- The off-diagonal truncated-character kernel is an exact divided difference. -/
theorem qBasis_displacement {n m : ℤ} (h : n ≠ m) (y L : ℝ) :
    (((n - m : ℤ) : ℝ)) * (-qBasis n m y L) =
      (Real.sin (2 * Real.pi * (n : ℝ) * y / L)
        - Real.sin (2 * Real.pi * (m : ℝ) * y / L)) / Real.pi := by
  have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
  have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
  unfold qBasis
  rw [if_neg h]
  have hdiff : (((m - n : ℤ) : ℝ)) = -(((n - m : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [hdiff]
  field_simp [hnmR, Real.pi_ne_zero]

/-- Exact pole-channel divided-difference identity. -/
theorem poleComponent_displacement {n m : ℤ} {L : ℝ} (hL : 0 < L) :
    (((n - m : ℤ) : ℝ)) * poleComponent n m L = poleSeq n L - poleSeq m L := by
  let κ : ℝ := 16 * Real.pi ^ 2
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  have hdn : 0 < L ^ 2 + κ * (n : ℝ) ^ 2 := by
    have : 0 < L ^ 2 := sq_pos_of_pos hL
    positivity
  have hdm : 0 < L ^ 2 + κ * (m : ℝ) ^ 2 := by
    have : 0 < L ^ 2 := sq_pos_of_pos hL
    positivity
  simp [poleComponent, poleSeq, κ]
  field_simp [ne_of_gt hdn, ne_of_gt hdm]
  push_cast
  ring

/-- Exact off-diagonal archimedean divided-difference identity. -/
theorem archComponent_displacement {n m : ℤ} (h : n ≠ m) (L : ℝ) :
    (((n - m : ℤ) : ℝ)) * (-archComponent n m L) = alphaL n L - alphaL m L := by
  have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
  have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
  unfold archComponent
  rw [if_neg h]
  field_simp [hnmR]
  ring

/-- Exact off-diagonal prime divided-difference identity. -/
theorem primeComponent_displacement {n m : ℤ} (h : n ≠ m) (L : ℝ) :
    (((n - m : ℤ) : ℝ)) * (-primeComponent n m L) = primeSeq n L - primeSeq m L := by
  classical
  unfold primeComponent primeSeq
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hq := qBasis_displacement h (Real.log k) L
  calc
    -((((n - m : ℤ) : ℝ)) *
        ((Λ k / Real.sqrt k : ℝ) * qBasis n m (Real.log k) L))
        = (Λ k / Real.sqrt k : ℝ) *
            ((((n - m : ℤ) : ℝ)) * (-qBasis n m (Real.log k) L)) := by ring
    _ = (Λ k / Real.sqrt k : ℝ) *
          ((Real.sin (2 * Real.pi * (n : ℝ) * Real.log k / L)
            - Real.sin (2 * Real.pi * (m : ℝ) * Real.log k / L)) / Real.pi) := by
          rw [hq]
    _ = (Λ k / Real.sqrt k : ℝ) *
          (Real.sin (2 * Real.pi * (n : ℝ) * Real.log k / L) / Real.pi)
        - (Λ k / Real.sqrt k : ℝ) *
          (Real.sin (2 * Real.pi * (m : ℝ) * Real.log k / L) / Real.pi) := by ring

/-- Exact entrywise displacement law for the formal CCM scalar entry. -/
theorem entry_displacement {n m : ℤ} {L : ℝ} (hL : 0 < L) :
    (((n - m : ℤ) : ℝ)) * entry n m L = displacementSeq n L - displacementSeq m L := by
  by_cases h : n = m
  · subst m
    simp [displacementSeq]
  · have hp := poleComponent_displacement (n := n) (m := m) hL
    have ha := archComponent_displacement h L
    have hq := primeComponent_displacement h L
    unfold entry displacementSeq
    calc
      (((n - m : ℤ) : ℝ)) *
          (poleComponent n m L - archComponent n m L - primeComponent n m L)
          = (((n - m : ℤ) : ℝ)) * poleComponent n m L
            + (((n - m : ℤ) : ℝ)) * (-archComponent n m L)
            + (((n - m : ℤ) : ℝ)) * (-primeComponent n m L) := by ring
      _ = (poleSeq n L - poleSeq m L)
            + (alphaL n L - alphaL m L)
            + (primeSeq n L - primeSeq m L) := by rw [hp, ha, hq]
      _ = (poleSeq n L + alphaL n L + primeSeq n L)
            - (poleSeq m L + alphaL m L + primeSeq m L) := by ring

/-- The concrete CCM scalar entry is exactly an instance of the generic
divided-difference class.  The channel lemmas above provide the zeta-specific
content; all subsequent matrix displacement algebra is generic. -/
theorem entry_eq_dividedDifferenceEntry {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    (entry n m L : ℂ) = dividedDifferenceEntry (ccmPotential L) (ccmDiagonal L) n m := by
  by_cases h : n = m
  · subst m
    simp [ccmDiagonal]
  · rw [dividedDifferenceEntry_of_ne _ _ h]
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hnmC : (((n - m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hnmZ
    have hreal := entry_displacement (n := n) (m := m) hL
    have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) hreal
    push_cast at hcomplex
    apply (eq_div_iff hnmC).2
    simpa [ccmPotential, mul_comm] using hcomplex

/-- Complex-valued displacement vector on the centered finite Fourier grid. -/
def displacementVector (L : ℝ) (N : ℕ) : Fin (2 * N + 1) → ℂ :=
  dividedDifferenceVector (ccmPotential L) N

/-- The formal finite CCM matrix is a centered generic divided-difference matrix. -/
theorem finiteMatrix_eq_dividedDifferenceMatrix {L : ℝ} (hL : 0 < L) (N : ℕ) :
    finiteMatrix L N = dividedDifferenceMatrix (ccmPotential L) (ccmDiagonal L) N := by
  ext i j
  rw [finiteMatrix_apply, dividedDifferenceMatrix_apply]
  exact entry_eq_dividedDifferenceEntry hL _ _

/-- The canonical finite CCM matrix has exact displacement rank at most two.
This now follows from the generic divided-difference chassis after the concrete
zeta-specific entry has been identified with that class. -/
theorem finiteMatrix_displacement {L : ℝ} (hL : 0 < L) (N : ℕ) :
    indexMatrix N * finiteMatrix L N - finiteMatrix L N * indexMatrix N =
      vecMulVec (displacementVector L N) (fun _ => 1)
        - vecMulVec (fun _ => 1) (displacementVector L N) := by
  rw [finiteMatrix_eq_dividedDifferenceMatrix hL N]
  exact dividedDifferenceMatrix_displacement _ _ _

/-- Rank form of the exact finite displacement theorem. -/
theorem rank_finiteMatrix_displacement_le_two {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (indexMatrix N * finiteMatrix L N - finiteMatrix L N * indexMatrix N).rank ≤ 2 := by
  rw [finiteMatrix_eq_dividedDifferenceMatrix hL N]
  exact rank_dividedDifferenceMatrix_displacement_le_two _ _ _

end Zeta23.CCM
