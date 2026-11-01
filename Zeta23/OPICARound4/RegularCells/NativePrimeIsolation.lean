import Zeta23.OPICARound4.RegularCells.PrimeSourceLaurent
import Zeta23.OPICARound4.RegularCells.FinitePrimeLaurentAlgebra
import Mathlib.NumberTheory.Bertrand

noncomputable section
namespace Zeta23.OPICARound4.PrimeIsolation
open CCM RegularCells PrimeSourceLaurent
open scoped BigOperators ArithmeticFunction

theorem exists_prime_below_cutoff_square_above (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ p : ℕ, p.Prime ∧ p ≤ Q ∧ Q < p^2 := by
  by_cases hsmall : Q < 4
  · exact ⟨2,Nat.prime_two,hQ,by omega⟩
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (Q/2) (by omega)
  refine ⟨p,hp,by omega,?_⟩
  have hdiv : Q ≤ 2*(Q/2)+1 := by omega
  have hhalf : 2 ≤ Q/2 := by omega
  nlinarith

theorem prime_pow_below_square_eq {Q p q : ℕ} (hp : p.Prime)
    (hQ : Q < p^2) (hq : q ≤ Q) (hpp : IsPrimePow q) (hd : p ∣ q) : q = p := by
  obtain ⟨r,k,hr,hk,rfl⟩ := (isPrimePow_nat_iff q).mp hpp
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hd)
  subst r
  have hk1 : k = 1 := by
    by_contra hn
    have hk2 : 2 ≤ k := by omega
    have hpow : p^2 ≤ p^k := Nat.pow_le_pow_right hp.pos hk2
    omega
  simp [hk1]

theorem primeSourceWeight_nonzero_isPrimePow {q : ℕ} (hq : primeSourceWeight q ≠ 0) :
    IsPrimePow q := by
  apply ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
  intro h
  apply hq
  simp [primeSourceWeight,h]

theorem weight_factorization_zero {Q p q : ℕ} (hp : p.Prime)
    (hQ : Q < p^2) (hq : q ≤ Q) (hne : q ≠ p) (hw : primeSourceWeight q ≠ 0) :
    q.factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  exact hne (prime_pow_below_square_eq hp hQ hq (primeSourceWeight_nonzero_isPrimePow hw) hd)

def singlePrimePhase (s : Finset ℕ) (p : s) (X : ℂˣ) : s → ℂˣ :=
  fun q => if q = p then X else 1

theorem monomial_singlePrimePhase (s : Finset ℕ) (p : s) (X : ℂˣ) (k : s → ℤ) :
    formalPrimeMonomial s k (singlePrimePhase s p X) = (X : ℂ)^k p := by
  classical
  unfold formalPrimeMonomial
  rw [Finset.prod_eq_single p]
  · simp [singlePrimePhase]
  · intro q hq hne
    simp [singlePrimePhase,hne]
  · simp

/-- The finite source sum collapses only after its actual Mangoldt weights and
prime-power exponents are enforced; no integer is assigned a free phase. -/
theorem weighted_single_prime_sum (Q : ℕ) (s : Finset ℕ) (p : s)
    (hp : p.val.Prime) (hpQ : p.val ≤ Q) (hQ : Q < p.val^2) (X : ℂˣ)
    {A : Type*} [AddCommMonoid A] [Module ℂ A] (F : ℕ → ℂ → A)
    (hF : ∀ q, F q 1 = 0) :
    (∑ q ∈ Finset.Icc 2 Q, primeSourceWeight q •
      F q (formalPrimeMonomial s (fun r => (q.factorization r.val : ℤ))
        (singlePrimePhase s p X))) = primeSourceWeight p.val • F p.val X := by
  classical
  rw [Finset.sum_eq_single p.val]
  · rw [monomial_singlePrimePhase]
    simp [hp.factorization_self]
  · intro q hq hne
    by_cases hw : primeSourceWeight q = 0
    · simp [hw]
    · have hf := weight_factorization_zero hp hQ (Finset.mem_Icc.mp hq).2 hne hw
      rw [monomial_singlePrimePhase]
      simp [hf,hF]
  · intro hn
    exact (hn (Finset.mem_Icc.mpr ⟨hp.two_le,hpQ⟩)).elim

theorem scaledPrimeMatrix_one (q : ℕ) (z : ℂ) (K : ℕ) :
    scaledPrimeMatrix q z 1 K = 0 := by
  ext i j
  norm_num [scaledPrimeMatrix,dividedDifferenceMatrix,dividedDifferenceEntry,
    formalPrimePotential]

theorem scaledFrozenPrimeMatrix_single (Q : ℕ) (s : Finset ℕ) (p : s)
    (hp : p.val.Prime) (hpQ : p.val ≤ Q) (hQ : Q < p.val^2) (X : ℂˣ)
    (z : ℂ) (K : ℕ) :
    scaledFrozenPrimeMatrix Q z (fun q => formalPrimeMonomial s
      (fun r => (q.factorization r.val : ℤ)) (singlePrimePhase s p X)) K =
        primeSourceWeight p.val • scaledPrimeMatrix p.val z X K := by
  exact weighted_single_prime_sum Q s p hp hpQ hQ X
    (fun q V => scaledPrimeMatrix q z V K) (fun q => scaledPrimeMatrix_one q z K)

def circlePhase (theta : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp ((theta : ℂ) * Complex.I)) (Complex.exp_ne_zero _)

theorem circlePhase_zpow (theta : ℝ) (n : ℤ) :
    ((circlePhase theta : ℂˣ) : ℂ)^n =
      Complex.exp ((n : ℂ) * ((theta : ℂ) * Complex.I)) :=
  (Complex.exp_int_mul _ _).symm

theorem circlePhase_symmetric (theta : ℝ) (n : ℤ) :
    ((circlePhase theta : ℂˣ) : ℂ)^(-n) + ((circlePhase theta : ℂˣ) : ℂ)^n =
      2 * (Real.cos ((n : ℝ) * theta) : ℂ) := by
  rw [circlePhase_zpow, circlePhase_zpow]
  rw [Complex.ofReal_cos]
  unfold Complex.cos
  push_cast
  congr 1 <;> ring

def isolatedPrimeCoefficient (p : ℕ) : ℝ := 2 * (Real.log p)^2 / Real.sqrt p

theorem isolatedPrimeCoefficient_pos {p : ℕ} (hp : p.Prime) :
    0 < isolatedPrimeCoefficient p := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold isolatedPrimeCoefficient
  positivity

theorem isolatedPrimeCoefficient_eq {p : ℕ} (hp : p.Prime) :
    (isolatedPrimeCoefficient p : ℂ) = 2 * primeSourceWeight p * (Real.log p : ℂ) := by
  simp only [isolatedPrimeCoefficient,primeSourceWeight,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  ring

/-- Exact complete weighted prime channel at the formal zero anchor. The prime
power relations and the common scalar have already been retained above. -/
theorem neg_scaledFrozen_single_zero (Q : ℕ) (s : Finset ℕ) (p : s)
    (hp : p.val.Prime) (hpQ : p.val ≤ Q) (hQ : Q < p.val^2)
    (theta : ℝ) (K : ℕ) :
    -(scaledFrozenPrimeMatrix Q 0 (fun q => formalPrimeMonomial s
      (fun r => (q.factorization r.val : ℤ)) (singlePrimePhase s p (circlePhase theta))) K) =
      (isolatedPrimeCoefficient p.val : ℂ) •
        (Matrix.diagonal (fun i : Fin (2*K+1) =>
          (Real.cos ((centeredIndex K i : ℝ) * theta) : ℂ)) - 1) := by
  rw [scaledFrozenPrimeMatrix_single Q s p hp hpQ hQ, scaledPrimeMatrix_zero,
    isolatedPrimeCoefficient_eq hp]
  ext i j
  simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true,circlePhase_symmetric]
    ring
  · simp [hij]

end Zeta23.OPICARound4.PrimeIsolation
