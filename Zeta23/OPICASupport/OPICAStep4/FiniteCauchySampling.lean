import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Finite rational sampling with moment cancellation

This module contains algebra over an arbitrary field.  No zeta-zero hypothesis,
positivity assertion, or Fourier-transform identity is assumed or concluded.
-/

noncomputable section

namespace Zeta23.OPICARound20

open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Cauchy sum with coefficients `u` and poles `a`. -/
def finiteCauchySum (a u : ι → F) (z : F) : F :=
  ∑ i, u i / (z - a i)

/-- Its polynomial numerator over the common nodal denominator. -/
def finiteCauchyNumerator (a u : ι → F) : F[X] :=
  ∑ i, C (u i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))

/-- The common nodal denominator. -/
def finiteCauchyDenominator (a : ι → F) : F[X] :=
  ∏ i, (X - C (a i))

theorem finiteCauchyNumerator_eval (a u : ι → F) (z : F)
    (hz : ∀ i, z ≠ a i) :
    (finiteCauchyNumerator a u).eval z =
      (finiteCauchyDenominator a).eval z * finiteCauchySum a u z := by
  simp only [finiteCauchyNumerator, finiteCauchyDenominator, finiteCauchySum,
    eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ (fun j => z - a j) (Finset.mem_univ i)]
  field_simp [sub_ne_zero.mpr (hz i)]

theorem finiteCauchyNumerator_eval_pole (a u : ι → F) (i : ι) :
    (finiteCauchyNumerator a u).eval (a i) =
      u i * ∏ j ∈ Finset.univ.erase i, (a i - a j) := by
  simp only [finiteCauchyNumerator, eval_finsetSum, eval_mul, eval_C,
    eval_prod, eval_sub, eval_X]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩
    rw [Finset.prod_eq_zero hmem (sub_self (a i)), mul_zero]
  · simp

theorem finiteCauchyNumerator_eq_zero_iff (a u : ι → F)
    (ha : Function.Injective a) :
    finiteCauchyNumerator a u = 0 ↔ u = 0 := by
  constructor
  · intro hp
    funext i
    have h := finiteCauchyNumerator_eval_pole a u i
    rw [hp, eval_zero] at h
    have hprod : (∏ j ∈ Finset.univ.erase i, (a i - a j)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      apply sub_ne_zero.mpr
      intro hji
      exact (Finset.mem_erase.mp hj).1 (ha hji).symm
    exact (mul_eq_zero.mp h.symm).resolve_right hprod
  · intro hu
    simp [finiteCauchyNumerator, hu]

theorem finiteCauchyNumerator_natDegree_le (a u : ι → F) :
    (finiteCauchyNumerator a u).natDegree ≤ Fintype.card ι - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_C_mul_le _ _).trans
  simp

/-- Multiplication of the numerator by `X` shifts the coefficient moment. -/
theorem finiteCauchyNumerator_shift (a u : ι → F) :
    X * finiteCauchyNumerator a u =
      C (∑ i, u i) * finiteCauchyDenominator a +
        finiteCauchyNumerator a (fun i => a i * u i) := by
  have hterm (i : ι) :
      X * (C (u i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))) =
      C (u i) * finiteCauchyDenominator a +
        C (a i * u i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) := by
    have hd : finiteCauchyDenominator a =
        (X - C (a i)) * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) := by
      exact (Finset.mul_prod_erase Finset.univ (fun j => X - C (a j))
        (Finset.mem_univ i)).symm
    rw [hd, C_mul]
    ring
  simp only [finiteCauchyNumerator, Finset.mul_sum, hterm,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum]

/-- If the first `r` moments vanish, multiplying the numerator by `X^r`
only replaces each coefficient by `a_i^r u_i`. -/
theorem finiteCauchyNumerator_moment_shift (a u : ι → F) (r : ℕ)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0) :
    X ^ r * finiteCauchyNumerator a u =
      finiteCauchyNumerator a (fun i => a i ^ r * u i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev : ∀ k < r, ∑ i, a i ^ k * u i = 0 :=
      fun k hk => hm k (Nat.lt_trans hk (Nat.lt_succ_self r))
    rw [pow_succ', mul_assoc, ih hprev, finiteCauchyNumerator_shift,
      hm r (Nat.lt_succ_self r), C_0, zero_mul, zero_add]
    congr 1
    funext i
    rw [pow_succ']
    ring

/-- Each vanished prefix moment lowers the maximum possible numerator degree
by one.  The nonzero-polynomial premise makes this valid for all finite cardinalities. -/
theorem finiteCauchyNumerator_degree_defect (a u : ι → F) (r : ℕ)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hp : finiteCauchyNumerator a u ≠ 0) :
    (finiteCauchyNumerator a u).natDegree + r < Fintype.card ι := by
  have hu : u ≠ 0 := by
    intro hu
    apply hp
    simp [finiteCauchyNumerator, hu]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  have : Nonempty ι := ⟨i⟩
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hdeg := finiteCauchyNumerator_natDegree_le a (fun i => a i ^ r * u i)
  rw [← finiteCauchyNumerator_moment_shift a u r hm,
    natDegree_mul (pow_ne_zero r X_ne_zero) hp, natDegree_pow, natDegree_X,
    mul_one] at hdeg
  omega

/-- `N-r` distinct samples away from the poles determine the coefficients once
the first `r` moments vanish.  The cardinal inequality handles `N ≤ r`, including
an empty sample type, without a separate nondegeneracy hypothesis. -/
theorem finiteCauchySum_zero_forces_coefficients
    {κ : Type*} [Fintype κ] (a u : ι → F) (z : κ → F) (r : ℕ)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (hza : ∀ j i, z j ≠ a i)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hcard : Fintype.card ι ≤ Fintype.card κ + r)
    (hzero : ∀ j, finiteCauchySum a u (z j) = 0) : u = 0 := by
  by_contra hu
  have hp : finiteCauchyNumerator a u ≠ 0 := by
    intro hp
    exact hu ((finiteCauchyNumerator_eq_zero_iff a u ha).mp hp)
  have hdeg := finiteCauchyNumerator_degree_defect a u r hm hp
  have hsmall : (finiteCauchyNumerator a u).natDegree < Fintype.card κ := by omega
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (finiteCauchyNumerator a u) hz
  · intro j
    rw [finiteCauchyNumerator_eval a u (z j) (hza j), hzero j, mul_zero]
  · exact hsmall

/-- When the number of vanishing moments reaches the number of distinct poles,
the coefficient vector is zero without taking any samples. -/
theorem finite_moments_force_coefficients
    (a u : ι → F) (r : ℕ) (ha : Function.Injective a)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hcard : Fintype.card ι ≤ r) : u = 0 := by
  exact finiteCauchySum_zero_forces_coefficients a u (fun j : Fin 0 => j.elim0) r ha
    (fun j => j.elim0) (fun j => j.elim0) hm (by simpa using hcard)
    (fun j => j.elim0)

/-- A nonzero moment-flat vector has a nonzero Cauchy sample in every sufficiently
large family of distinct points away from the poles. -/
theorem finiteCauchySum_nonzero_sample
    {κ : Type*} [Fintype κ] (a u : ι → F) (z : κ → F) (r : ℕ)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (hza : ∀ j i, z j ≠ a i)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hcard : Fintype.card ι ≤ Fintype.card κ + r)
    (hu : u ≠ 0) : ∃ j, finiteCauchySum a u (z j) ≠ 0 := by
  by_contra h
  push Not at h
  exact hu (finiteCauchySum_zero_forces_coefficients a u z r ha hz hza hm hcard h)

/-- Any finite set of nonpole zeros of a nonzero moment-flat Cauchy sum obeys
the strict degree bound.  This counts distinct points, not multiplicities. -/
theorem finiteCauchySum_zero_set_card_bound
    (a u : ι → F) (r : ℕ) (s : Finset F)
    (ha : Function.Injective a)
    (hsa : ∀ z ∈ s, ∀ i, z ≠ a i)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hzero : ∀ z ∈ s, finiteCauchySum a u z = 0)
    (hu : u ≠ 0) : s.card + r < Fintype.card ι := by
  by_contra hcard
  apply hu
  apply finiteCauchySum_zero_forces_coefficients a u (fun z : s => (z : F)) r ha
    Subtype.val_injective
  · exact fun z i => hsa z z.property i
  · exact hm
  · simpa using Nat.le_of_not_gt hcard
  · exact fun z => hzero z z.property

end Zeta23.OPICARound20
