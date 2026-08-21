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

/-- At the left dictionary endpoint `ω = 0`, the source potential vanishes. -/
@[simp] theorem sourcePotential_zero (n : ℤ) : sourcePotential 0 n = 0 := by
  simp [sourcePotential]

/-- At the left dictionary endpoint `ω = 0`, the diagonal data vanish. -/
@[simp] theorem sourceDiagonal_zero (n : ℤ) : sourceDiagonal 0 n = 0 := by
  simp [sourceDiagonal]

/-- At `ω = 1`, integer Fourier periodicity kills the source potential. -/
@[simp] theorem sourcePotential_one (n : ℤ) : sourcePotential 1 n = 0 := by
  unfold sourcePotential
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) by ring]
  have hsin : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_int_mul_two_pi 0 n
  rw [hsin]
  simp

/-- At `ω = 1`, every diagonal source value is exactly `2`. -/
@[simp] theorem sourceDiagonal_one (n : ℤ) : sourceDiagonal 1 n = 2 := by
  unfold sourceDiagonal
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) by ring]
  rw [Real.cos_int_mul_two_pi]
  ring

/-- The elementary source entry at `ω = 0` is zero. -/
@[simp] theorem sourceEntry_zero (n m : ℤ) : sourceEntry 0 n m = 0 := by
  simp [sourceEntry, dividedDifferenceEntry]

/-- The elementary source entry at `ω = 1` is `2` on the diagonal and zero off it. -/
@[simp] theorem sourceEntry_one (n m : ℤ) :
    sourceEntry 1 n m = if n = m then 2 else 0 := by
  by_cases h : n = m
  · subst m
    simp
  · rw [sourceEntry_of_ne 1 h]
    simp [h]

/-- Centered Fourier indexing is injective. -/
theorem centeredIndex_injective (N : ℕ) : Function.Injective (centeredIndex N) := by
  intro i j hij
  apply Fin.ext
  dsimp [centeredIndex] at hij
  omega

/-- At `ω = 0` the whole source matrix vanishes. -/
@[simp] theorem sourceMatrix_zero (N : ℕ) :
    sourceMatrix 0 N = 0 := by
  ext i j
  simp [sourceMatrix_apply]

/-- At `ω = 1` the source matrix is exactly twice the identity. -/
@[simp] theorem sourceMatrix_one (N : ℕ) :
    sourceMatrix 1 N = (2 : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [sourceMatrix_apply]
  · have hc : centeredIndex N i ≠ centeredIndex N j := by
      exact fun hidx => h ((centeredIndex_injective N) hidx)
    simp [sourceMatrix_apply, hc, h]

/-- Periodicity conversion for the source potential at `ω = 1-y/L`. -/
theorem sourcePotential_one_sub (n : ℤ) (y L : ℝ) :
    sourcePotential (1 - y / L) n =
      ((-Real.sin (2 * Real.pi * (n : ℝ) * y / L) / Real.pi : ℝ) : ℂ) := by
  unfold sourcePotential
  norm_cast
  rw [show 2 * Real.pi * (n : ℝ) * (1 - y / L) =
      (n : ℝ) * (2 * Real.pi) - 2 * Real.pi * (n : ℝ) * y / L by ring]
  rw [Real.sin_int_mul_two_pi_sub]

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
