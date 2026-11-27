import Zeta23.OPICASupport.OPICAStep4.FiniteCauchySampling
import Mathlib.Algebra.Polynomial.Expand

/-!
Reversal of a symmetric odd-cardinality pole grid preserves numerator parity.
The operation is substitution `X ↦ -X`, not polynomial coefficient reversal.
No Fourier, pole-neutrality, positivity or zeta-zero premise occurs here.
-/

noncomputable section

namespace Zeta23.OPICARound20.NativeParityRational

open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteCauchyNumerator_reindex (a u : ι → F) (e : ι ≃ ι) :
    finiteCauchyNumerator (fun i => a (e i)) (fun i => u (e i)) =
      finiteCauchyNumerator a u := by
  unfold finiteCauchyNumerator
  calc
    _ = ∑ i, C (u (e i)) * ∏ j ∈ Finset.univ.erase (e i), (X - C (a j)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact Finset.prod_equiv e (by intro j; simp) (by intro j _; rfl)
    _ = _ := Equiv.sum_comp e
      (fun i => C (u i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j)))

theorem finiteCauchyNumerator_neg_coefficients (a u : ι → F) :
    finiteCauchyNumerator a (fun i => -u i) = -finiteCauchyNumerator a u := by
  simp [finiteCauchyNumerator, Finset.sum_neg_distrib]

theorem finiteCauchyNumerator_comp_neg_X (K : ℕ) (a u : Fin (2 * K + 1) → F) :
    (finiteCauchyNumerator a u).comp (-X) =
      finiteCauchyNumerator (fun i => -a i) u := by
  unfold finiteCauchyNumerator
  simp only [sum_comp, mul_comp, C_comp, prod_comp, sub_comp, X_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hterm (j : Fin (2 * K + 1)) :
      (-X - C (a j) : F[X]) = -(X - C (-a j)) := by
    rw [map_neg]
    ring
  simp_rw [hterm]
  rw [Finset.prod_neg]
  have hcard : (Finset.univ.erase i).card = 2 * K := by simp
  rw [hcard, Even.neg_one_pow (show Even (2 * K) from ⟨K, by omega⟩), one_mul]

theorem finiteCauchyNumerator_even_of_reversal (K : ℕ)
    (a u : Fin (2 * K + 1) → F)
    (ha : ∀ i, a i.rev = -a i) (hu : ∀ i, u i.rev = u i) :
    (finiteCauchyNumerator a u).comp (-X) = finiteCauchyNumerator a u := by
  rw [finiteCauchyNumerator_comp_neg_X]
  have he := finiteCauchyNumerator_reindex a u Fin.revPerm
  simpa only [Fin.revPerm_apply, ha, hu] using he

theorem finiteCauchyNumerator_odd_of_reversal (K : ℕ)
    (a u : Fin (2 * K + 1) → F)
    (ha : ∀ i, a i.rev = -a i) (hu : ∀ i, u i.rev = -u i) :
    (finiteCauchyNumerator a u).comp (-X) = -finiteCauchyNumerator a u := by
  rw [finiteCauchyNumerator_comp_neg_X]
  have he := finiteCauchyNumerator_reindex a u Fin.revPerm
  simp only [Fin.revPerm_apply, ha, hu, finiteCauchyNumerator_neg_coefficients] at he
  exact neg_eq_iff_eq_neg.mp he

theorem exists_square_composition_of_odd_coefficients_zero (P : F[X])
    (h : ∀ n, Odd n → P.coeff n = 0) :
    ∃ Q : F[X], P = Q.comp (X ^ 2) := by
  refine ⟨P.contract 2, ?_⟩
  ext n
  rw [← expand_eq_comp_X_pow, coeff_expand (by decide : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, coeff_contract (by decide : 2 ≠ 0), Nat.div_mul_cancel hn]
  · rw [if_neg hn]
    exact h n (Nat.not_even_iff_odd.mp (fun he => hn he.two_dvd))

theorem exists_X_square_composition_of_even_coefficients_zero (P : F[X])
    (h : ∀ n, Even n → P.coeff n = 0) :
    ∃ Q : F[X], P = X * Q.comp (X ^ 2) := by
  obtain ⟨Q, hQ⟩ := exists_square_composition_of_odd_coefficients_zero P.divX
    (fun n hn => by rw [coeff_divX]; exact h (n + 1) (by simpa using hn.add_odd (by decide : Odd 1)))
  refine ⟨Q, ?_⟩
  have h0 := h 0 (by decide)
  have hid := X_mul_divX_add P
  rw [h0, C_0, add_zero, hQ] at hid
  exact hid.symm

variable [CharZero F]

theorem exists_square_composition_of_comp_neg_X_eq (P : F[X])
    (hP : P.comp (-X) = P) : ∃ Q : F[X], P = Q.comp (X ^ 2) := by
  apply exists_square_composition_of_odd_coefficients_zero
  intro n hn
  have h := congrArg (fun Q : F[X] => Q.coeff n) hP
  have hcoeff : (P.comp (-X)).coeff n = P.coeff n * (-1 : F) ^ n := by
    simpa using (comp_C_mul_X_coeff (p := P) (r := (-1 : F)) (n := n))
  rw [hcoeff, hn.neg_one_pow, mul_neg_one] at h
  have hz : (2 : F) * P.coeff n = 0 := by
    simpa only [two_mul] using (eq_neg_iff_add_eq_zero.mp h.symm)
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem exists_X_square_composition_of_comp_neg_X_eq_neg (P : F[X])
    (hP : P.comp (-X) = -P) : ∃ Q : F[X], P = X * Q.comp (X ^ 2) := by
  apply exists_X_square_composition_of_even_coefficients_zero
  intro n hn
  have h := congrArg (fun Q : F[X] => Q.coeff n) hP
  have hcoeff : (P.comp (-X)).coeff n = P.coeff n * (-1 : F) ^ n := by
    simpa using (comp_C_mul_X_coeff (p := P) (r := (-1 : F)) (n := n))
  rw [hcoeff, hn.neg_one_pow, mul_one, coeff_neg] at h
  have hz : (2 : F) * P.coeff n = 0 := by
    simpa only [two_mul] using (eq_neg_iff_add_eq_zero.mp h)
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end Zeta23.OPICARound20.NativeParityRational
