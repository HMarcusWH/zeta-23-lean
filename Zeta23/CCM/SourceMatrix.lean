import Zeta23.CCM.DividedDifference
import Zeta23.CCM.Kernel

noncomputable section

namespace Zeta23.CCM

open Matrix

/-! # Elementary single-frequency source matrices

This is the finite source atom used by the Guinand--Weil dictionary.  The
parameter `ω` is the source coordinate; its potential on the Fourier lattice is
`sin(2πωn)/π`, with derivative data `2ω cos(2πωn)` on the diagonal.
-/

/-- Single-frequency source potential on the integer Fourier lattice. -/
def sourcePotential (ω : ℝ) (n : ℤ) : ℂ :=
  ((Real.sin (2 * Real.pi * (n : ℝ) * ω) / Real.pi : ℝ) : ℂ)

/-- Diagonal derivative data for the single-frequency source potential. -/
def sourceDiagonal (ω : ℝ) (n : ℤ) : ℂ :=
  ((2 * ω * Real.cos (2 * Real.pi * (n : ℝ) * ω) : ℝ) : ℂ)

/-- Elementary source entry as a specialization of the generic divided-difference chassis. -/
def sourceEntry (ω : ℝ) (n m : ℤ) : ℂ :=
  dividedDifferenceEntry (sourcePotential ω) (sourceDiagonal ω) n m

/-- Centered finite single-frequency source matrix. -/
def sourceMatrix (ω : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  dividedDifferenceMatrix (sourcePotential ω) (sourceDiagonal ω) N

@[simp] theorem sourceEntry_self (ω : ℝ) (n : ℤ) :
    sourceEntry ω n n = sourceDiagonal ω n := by
  simp [sourceEntry]

theorem sourceEntry_of_ne (ω : ℝ) {n m : ℤ} (h : n ≠ m) :
    sourceEntry ω n m =
      (sourcePotential ω n - sourcePotential ω m) / (((n - m : ℤ) : ℂ)) := by
  exact dividedDifferenceEntry_of_ne _ _ h

@[simp] theorem sourceMatrix_apply (ω : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    sourceMatrix ω N i j =
      sourceEntry ω (centeredIndex N i) (centeredIndex N j) := rfl

/-- The elementary source matrix is symmetric. -/
theorem sourceEntry_symmetric (ω : ℝ) (n m : ℤ) :
    sourceEntry ω n m = sourceEntry ω m n := by
  by_cases h : n = m
  · subst m
    rfl
  · have h' : m ≠ n := Ne.symm h
    rw [sourceEntry_of_ne ω h, sourceEntry_of_ne ω h']
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hmnZ : m - n ≠ 0 := sub_ne_zero.mpr h'
    have hnmC : (((n - m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hnmZ
    have hmnC : (((m - n : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hmnZ
    field_simp [hnmC, hmnC]
    push_cast
    ring

/-- Periodicity conversion for the source potential at `ω = 1-y/L`. -/
theorem sourcePotential_one_sub (n : ℤ) (y L : ℝ) :
    sourcePotential (1 - y / L) n =
      ((-Real.sin (2 * Real.pi * (n : ℝ) * y / L) / Real.pi : ℝ) : ℂ) := by
  unfold sourcePotential
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * (1 - y / L) =
      (n : ℝ) * (2 * Real.pi) - 2 * Real.pi * (n : ℝ) * y / L by ring]
  rw [Real.sin_int_mul_two_pi_sub]
  ring

/-- Periodicity conversion for the diagonal source data at `ω = 1-y/L`. -/
theorem sourceDiagonal_one_sub (n : ℤ) (y L : ℝ) :
    sourceDiagonal (1 - y / L) n =
      ((2 * (1 - y / L) *
        Real.cos (2 * Real.pi * (n : ℝ) * y / L) : ℝ) : ℂ) := by
  unfold sourceDiagonal
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * (1 - y / L) =
      (n : ℝ) * (2 * Real.pi) - 2 * Real.pi * (n : ℝ) * y / L by ring]
  rw [Real.cos_int_mul_two_pi_sub]

/-- Exact convention bridge between the elementary source matrix and the fork-owned
one-sided CCM basis.  This theorem is the sign/parameter acceptance test for the
finite dictionary: `ω = 1-y/L` reproduces `qBasis` exactly. -/
theorem sourceEntry_one_sub_eq_qBasis (n m : ℤ) (y L : ℝ) :
    sourceEntry (1 - y / L) n m = (qBasis n m y L : ℂ) := by
  by_cases h : n = m
  · subst m
    rw [sourceEntry_self, sourceDiagonal_one_sub]
    simp [qBasis]
  · rw [sourceEntry_of_ne _ h, sourcePotential_one_sub, sourcePotential_one_sub]
    unfold qBasis
    rw [if_neg h]
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hmnZ : m - n ≠ 0 := by omega
    have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
    have hmnR : (((m - n : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hmnZ
    norm_cast
    field_simp [hnmR, hmnR, Real.pi_ne_zero]
    push_cast
    ring

/-- Universal displacement identity specialized to one elementary source frequency. -/
theorem sourceMatrix_displacement (ω : ℝ) (N : ℕ) :
    indexMatrix N * sourceMatrix ω N - sourceMatrix ω N * indexMatrix N =
      vecMulVec (dividedDifferenceVector (sourcePotential ω) N) (fun _ => 1)
        - vecMulVec (fun _ => 1) (dividedDifferenceVector (sourcePotential ω) N) := by
  exact dividedDifferenceMatrix_displacement _ _ _

/-- Every elementary source matrix has displacement rank at most two. -/
theorem rank_sourceMatrix_displacement_le_two (ω : ℝ) (N : ℕ) :
    (indexMatrix N * sourceMatrix ω N - sourceMatrix ω N * indexMatrix N).rank ≤ 2 := by
  exact rank_dividedDifferenceMatrix_displacement_le_two _ _ _

end Zeta23.CCM
