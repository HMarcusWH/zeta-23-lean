import Zeta23.OPICASupport.OPICAStep4.FiniteCauchySampling

/-!
# Parity-folded polynomial numerators with a pole root

The parity representation is explicit: `Q.comp (X^2)` or `X * Q.comp (X^2)`.
This module does not prove that a native Fourier moment/pole-neutral slice has
that representation. It proves the resulting factorization and sharp sampling
bound over an arbitrary field, including empty sample and zero-polynomial cases.
-/

noncomputable section

namespace Zeta23.OPICARound20.ParityRational

open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F]

/-- An even-form numerator with a root at `p` has the full quadratic pole factor. -/
theorem even_pole_factorization (Q : F[X]) (p : F)
    (hp : (Q.comp (X ^ 2)).eval p = 0) :
    ∃ R : F[X], Q.comp (X ^ 2) =
      (X ^ 2 - C (p ^ 2)) * R.comp (X ^ 2) := by
  have hq : Q.IsRoot (p ^ 2) := by
    simpa only [IsRoot.def, eval_comp, eval_pow, eval_X] using hp
  obtain ⟨R, hR⟩ := (dvd_iff_isRoot).mpr hq
  refine ⟨R, ?_⟩
  rw [hR, mul_comp, sub_comp, X_comp, C_comp]

/-- For an odd-form numerator, a nonzero pole root gives `X` times the
quadratic pole factor. The hypothesis `p ≠ 0` is essential. -/
theorem odd_pole_factorization (Q : F[X]) (p : F) (hp0 : p ≠ 0)
    (hp : (X * Q.comp (X ^ 2)).eval p = 0) :
    ∃ R : F[X], X * Q.comp (X ^ 2) =
      X * (X ^ 2 - C (p ^ 2)) * R.comp (X ^ 2) := by
  have hq : (Q.comp (X ^ 2)).eval p = 0 := by
    simpa only [eval_mul, eval_X, mul_eq_zero, hp0, false_or] using hp
  obtain ⟨R, hR⟩ := even_pole_factorization Q p hq
  exact ⟨R, by rw [hR, mul_assoc]⟩

/-- The exact degree of a nonzero quadratic-pole factorization. -/
theorem even_pole_factor_natDegree (R : F[X]) (p : F)
    (hR : R.comp (X ^ 2) ≠ 0) :
    ((X ^ 2 - C (p ^ 2)) * R.comp (X ^ 2)).natDegree = 2 + 2 * R.natDegree := by
  rw [natDegree_mul (X_pow_sub_C_ne_zero (by decide) (p ^ 2)) hR,
    natDegree_X_pow_sub_C, natDegree_comp, natDegree_pow, natDegree_X]
  omega

/-- The exact degree of a nonzero odd quadratic-pole factorization. -/
theorem odd_pole_factor_natDegree (R : F[X]) (p : F)
    (hR : R.comp (X ^ 2) ≠ 0) :
    (X * (X ^ 2 - C (p ^ 2)) * R.comp (X ^ 2)).natDegree =
      3 + 2 * R.natDegree := by
  rw [mul_assoc, natDegree_mul X_ne_zero
    (mul_ne_zero (X_pow_sub_C_ne_zero (by decide) (p ^ 2)) hR),
    natDegree_X, even_pole_factor_natDegree R p hR]
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- With `r` vanishing moments, even-form numerator, and a pole root,
`N ≤ 2M+r+2` square-distinct nonpole samples determine the coefficients.
The quadratic pole factor must not vanish at a sample. -/
theorem even_moment_pole_samples_force_coefficients
    {κ : Type*} [Fintype κ] (a u : ι → F) (Q : F[X]) (p : F)
    (hparity : finiteCauchyNumerator a u = Q.comp (X ^ 2))
    (hp : (finiteCauchyNumerator a u).eval p = 0)
    (z : κ → F) (r : ℕ) (ha : Function.Injective a)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hza : ∀ j i, z j ≠ a i) (hzp : ∀ j, z j ^ 2 ≠ p ^ 2)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hcard : Fintype.card ι ≤ 2 * Fintype.card κ + r + 2)
    (hzero : ∀ j, finiteCauchySum a u (z j) = 0) : u = 0 := by
  by_contra hu
  have hP : finiteCauchyNumerator a u ≠ 0 := by
    exact fun h => hu ((finiteCauchyNumerator_eq_zero_iff a u ha).mp h)
  obtain ⟨R, hR⟩ := even_pole_factorization Q p (hparity ▸ hp)
  have hfactor : finiteCauchyNumerator a u =
      (X ^ 2 - C (p ^ 2)) * R.comp (X ^ 2) := hparity.trans hR
  have hR0 : R.comp (X ^ 2) ≠ 0 := by
    intro h
    apply hP
    rw [hfactor, h, mul_zero]
  have hdeg := finiteCauchyNumerator_degree_defect a u r hm hP
  rw [hfactor, even_pole_factor_natDegree R p hR0] at hdeg
  have hsmall : R.natDegree < Fintype.card κ := by omega
  have hReval : ∀ j, R.eval (z j ^ 2) = 0 := by
    intro j
    have he : (finiteCauchyNumerator a u).eval (z j) = 0 := by
      rw [finiteCauchyNumerator_eval a u (z j) (hza j), hzero j, mul_zero]
    rw [hfactor] at he
    simpa only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_comp,
      mul_eq_zero, sub_eq_zero, hzp j, false_or] using he
  have hRzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero R hzsq hReval hsmall
  apply hR0
  simp [hRzero]

/-- Odd-form analogue. Besides the quadratic pole factor, the automatic
zero at `z=0` is excluded from the samples. -/
theorem odd_moment_pole_samples_force_coefficients
    {κ : Type*} [Fintype κ] (a u : ι → F) (Q : F[X]) (p : F) (hp0 : p ≠ 0)
    (hparity : finiteCauchyNumerator a u = X * Q.comp (X ^ 2))
    (hp : (finiteCauchyNumerator a u).eval p = 0)
    (z : κ → F) (r : ℕ) (ha : Function.Injective a)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hza : ∀ j i, z j ≠ a i) (hz0 : ∀ j, z j ≠ 0)
    (hzp : ∀ j, z j ^ 2 ≠ p ^ 2)
    (hm : ∀ k < r, ∑ i, a i ^ k * u i = 0)
    (hcard : Fintype.card ι ≤ 2 * Fintype.card κ + r + 3)
    (hzero : ∀ j, finiteCauchySum a u (z j) = 0) : u = 0 := by
  by_contra hu
  have hP : finiteCauchyNumerator a u ≠ 0 := by
    exact fun h => hu ((finiteCauchyNumerator_eq_zero_iff a u ha).mp h)
  obtain ⟨R, hR⟩ := odd_pole_factorization Q p hp0 (hparity ▸ hp)
  have hfactor : finiteCauchyNumerator a u =
      X * (X ^ 2 - C (p ^ 2)) * R.comp (X ^ 2) := hparity.trans hR
  have hR0 : R.comp (X ^ 2) ≠ 0 := by
    intro h
    apply hP
    rw [hfactor, h, mul_zero]
  have hdeg := finiteCauchyNumerator_degree_defect a u r hm hP
  rw [hfactor, odd_pole_factor_natDegree R p hR0] at hdeg
  have hsmall : R.natDegree < Fintype.card κ := by omega
  have hReval : ∀ j, R.eval (z j ^ 2) = 0 := by
    intro j
    have he : (finiteCauchyNumerator a u).eval (z j) = 0 := by
      rw [finiteCauchyNumerator_eval a u (z j) (hza j), hzero j, mul_zero]
    rw [hfactor] at he
    simpa only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_comp,
      mul_eq_zero, sub_eq_zero, hz0 j, hzp j, false_or, or_false] using he
  have hRzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero R hzsq hReval hsmall
  apply hR0
  simp [hRzero]

/-- For `2*K+1` modes and six cancelled moments, `K-3` samples suffice
under the explicit even parity and pole-root hypotheses. Natural subtraction
retains every low-cutoff case. This is not a native-slice identification. -/
theorem even_six_moment_samples_force_coefficients
    {κ : Type*} [Fintype κ] (K : ℕ) (a u : Fin (2 * K + 1) → F)
    (Q : F[X]) (p : F)
    (hparity : finiteCauchyNumerator a u = Q.comp (X ^ 2))
    (hp : (finiteCauchyNumerator a u).eval p = 0)
    (z : κ → F) (ha : Function.Injective a)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hza : ∀ j i, z j ≠ a i) (hzp : ∀ j, z j ^ 2 ≠ p ^ 2)
    (hm : ∀ k < 6, ∑ i, a i ^ k * u i = 0)
    (hcard : K - 3 ≤ Fintype.card κ)
    (hzero : ∀ j, finiteCauchySum a u (z j) = 0) : u = 0 := by
  apply even_moment_pole_samples_force_coefficients a u Q p hparity hp z 6
    ha hzsq hza hzp hm _ hzero
  simp only [Fintype.card_fin]
  omega

/-- For `2*K+1` modes and seven cancelled moments, `K-4` samples suffice
under the explicit odd parity and nonzero pole-root hypotheses. -/
theorem odd_seven_moment_samples_force_coefficients
    {κ : Type*} [Fintype κ] (K : ℕ) (a u : Fin (2 * K + 1) → F)
    (Q : F[X]) (p : F) (hp0 : p ≠ 0)
    (hparity : finiteCauchyNumerator a u = X * Q.comp (X ^ 2))
    (hp : (finiteCauchyNumerator a u).eval p = 0)
    (z : κ → F) (ha : Function.Injective a)
    (hzsq : Function.Injective (fun j => z j ^ 2))
    (hza : ∀ j i, z j ≠ a i) (hz0 : ∀ j, z j ≠ 0)
    (hzp : ∀ j, z j ^ 2 ≠ p ^ 2)
    (hm : ∀ k < 7, ∑ i, a i ^ k * u i = 0)
    (hcard : K - 4 ≤ Fintype.card κ)
    (hzero : ∀ j, finiteCauchySum a u (z j) = 0) : u = 0 := by
  apply odd_moment_pole_samples_force_coefficients a u Q p hp0 hparity hp z 7
    ha hzsq hza hz0 hzp hm _ hzero
  simp only [Fintype.card_fin]
  omega

/-- The even conditional algebraic carrier is zero at cutoffs at most three. -/
theorem even_six_moment_low_cutoff_zero
    (K : ℕ) (hK : K ≤ 3) (a u : Fin (2 * K + 1) → F) (Q : F[X]) (p : F)
    (hparity : finiteCauchyNumerator a u = Q.comp (X ^ 2))
    (hp : (finiteCauchyNumerator a u).eval p = 0) (ha : Function.Injective a)
    (hm : ∀ k < 6, ∑ i, a i ^ k * u i = 0) : u = 0 := by
  exact even_six_moment_samples_force_coefficients K a u Q p hparity hp
    (fun j : Fin 0 => j.elim0) ha (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) hm (by simp; omega) (fun j => j.elim0)

/-- The odd conditional algebraic carrier is zero at cutoffs at most four. -/
theorem odd_seven_moment_low_cutoff_zero
    (K : ℕ) (hK : K ≤ 4) (a u : Fin (2 * K + 1) → F) (Q : F[X])
    (p : F) (hp0 : p ≠ 0)
    (hparity : finiteCauchyNumerator a u = X * Q.comp (X ^ 2))
    (hp : (finiteCauchyNumerator a u).eval p = 0) (ha : Function.Injective a)
    (hm : ∀ k < 7, ∑ i, a i ^ k * u i = 0) : u = 0 := by
  exact odd_seven_moment_samples_force_coefficients K a u Q p hp0 hparity hp
    (fun j : Fin 0 => j.elim0) ha (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (fun j => j.elim0) hm (by simp; omega) (fun j => j.elim0)

end Zeta23.OPICARound20.ParityRational
