import Zeta23.OPICARound4.RegularCells.MeromorphicFrequencyIndependence
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Zeta23.OPICARound4.RegularCells

def primeLogFrequency (s : Finset ℕ) (k : s → ℤ) : ℝ :=
  ∑ p : s, (k p : ℝ) * Real.log (p : ℕ)

theorem finite_prime_product_factorization (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) (k : s → ℕ) (p : s) :
    (∏ q : s, (q : ℕ) ^ k q).factorization (p : ℕ) = k p := by
  classical
  rw [Nat.factorization_prod_apply (g := fun q : s => (q : ℕ)^k q)
    (fun q _ => pow_ne_zero _ (hs q q.property).ne_zero)]
  calc
    (∑ q : s, ((q : ℕ)^k q).factorization (p : ℕ)) =
        ∑ q : s, if q = p then k p else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [(hs q q.property).factorization_pow]
      by_cases h : q = p
      · subst q
        simp
      · have hval : (q : ℕ) ≠ (p : ℕ) := fun he => h (Subtype.ext he)
        simp [hval, h]
    _ = k p := by simp

theorem natural_prime_log_sum_injective (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    Function.Injective (fun k : s → ℕ => ∑ p : s, (k p : ℝ)*Real.log (p : ℕ)) := by
  classical
  intro k l he
  have hpos (v : s → ℕ) : 0 < ∏ p : s, (p : ℕ)^v p :=
    Finset.prod_pos fun p _ => pow_pos (hs p p.property).pos _
  have hlog (v : s → ℕ) :
      Real.log ((∏ p : s, (p : ℕ)^v p : ℕ) : ℝ) =
        ∑ p : s, (v p : ℝ)*Real.log (p : ℕ) := by
    push_cast
    rw [Real.log_prod]
    · simp only [Real.log_pow]
    · intro p _
      exact pow_ne_zero _ (by exact_mod_cast (hs p p.property).ne_zero)
  have hprod : (∏ p : s, (p : ℕ)^k p) = ∏ p : s, (p : ℕ)^l p := by
    have hh := Real.log_injOn_pos
      (show (0 : ℝ) < ((∏ p : s, (p : ℕ)^k p : ℕ) : ℝ) by exact_mod_cast hpos k)
      (show (0 : ℝ) < ((∏ p : s, (p : ℕ)^l p : ℕ) : ℝ) by exact_mod_cast hpos l)
      ((hlog k).trans (he.trans (hlog l).symm))
    exact_mod_cast hh
  funext p
  have hp := congrArg (fun n : ℕ => n.factorization (p : ℕ)) hprod
  simpa only [finite_prime_product_factorization s hs] using hp

/-- Signed Laurent exponents remain distinguishable by genuine prime logarithms. -/
theorem primeLogFrequency_injective (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) : Function.Injective (primeLogFrequency s) := by
  classical
  intro k l he
  let kp : s → ℕ := fun p => (k p).toNat + (-l p).toNat
  let lp : s → ℕ := fun p => (l p).toNat + (-k p).toNat
  have hd (z : ℤ) : ((z.toNat : ℕ) : ℝ) - (((-z).toNat : ℕ) : ℝ) = (z : ℝ) := by
    have hz : (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by omega
    exact_mod_cast hz
  have hp : (∑ p : s, (kp p : ℝ)*Real.log (p : ℕ)) =
      ∑ p : s, (lp p : ℝ)*Real.log (p : ℕ) := by
    have hh : (∑ p : s, ((kp p : ℝ)-(lp p : ℝ))*Real.log (p : ℕ)) = 0 := by
      calc
        _ = ∑ p : s, ((k p : ℝ)-(l p : ℝ))*Real.log (p : ℕ) := by
          apply Finset.sum_congr rfl
          intro p _
          congr 1
          dsimp [kp,lp]
          push_cast
          linarith [hd (k p),hd (l p)]
        _ = primeLogFrequency s k - primeLogFrequency s l := by
          simp only [primeLogFrequency, sub_mul, Finset.sum_sub_distrib]
        _ = 0 := sub_eq_zero.mpr he
    simpa only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using hh
  have hkl := natural_prime_log_sum_injective s hs hp
  funext p
  have hc := congrFun hkl p
  dsimp [kp,lp] at hc
  omega

def primeLaurentFrequency (s : Finset ℕ) (k : s → ℤ) : ℝ :=
  (2*Real.pi)*primeLogFrequency s k

theorem primeLaurentFrequency_injective (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) : Function.Injective (primeLaurentFrequency s) := by
  intro k l h
  apply primeLogFrequency_injective s hs
  exact mul_left_cancel₀ (by positivity : (2:ℝ)*Real.pi ≠ 0) h

def primePhase (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (((2*Real.pi*Real.log p : ℝ) : ℂ)*Complex.I/z)

def primeLaurentMonomial (s : Finset ℕ) (k : s → ℤ) (z : ℂ) : ℂ :=
  ∏ p : s, primePhase p z ^ k p

/-- Includes negative exponents literally; every prime phase is nonzero. -/
theorem primeLaurentMonomial_eq_exp (s : Finset ℕ) (k : s → ℤ) (z : ℂ) :
    primeLaurentMonomial s k z =
      Complex.exp ((primeLaurentFrequency s k : ℂ)*Complex.I/z) := by
  unfold primeLaurentMonomial primePhase
  simp_rw [← Complex.exp_int_mul]
  rw [← Complex.exp_sum]
  congr 1
  unfold primeLaurentFrequency primeLogFrequency
  push_cast
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

def groupedPrimeLaurentCoefficient {ι : Type*} [DecidableEq ι]
    (s : Finset ℕ) (t : Finset ι) (e : ι → s → ℤ) (a : ι → ℂ → ℂ)
    (k : s → ℤ) (z : ℂ) : ℂ :=
  ∑ i ∈ t.filter (fun i => e i = k), a i z

theorem primeLaurent_sum_grouped {ι : Type*} [DecidableEq ι]
    (s : Finset ℕ) (t : Finset ι) (e : ι → s → ℤ) (a : ι → ℂ → ℂ) (z : ℂ) :
    (∑ i ∈ t, a i z * primeLaurentMonomial s (e i) z) =
      ∑ k ∈ t.image e, groupedPrimeLaurentCoefficient s t e a k z *
        primeLaurentMonomial s k z := by
  classical
  calc
    _ = ∑ k ∈ t.image e, ∑ i ∈ t.filter (fun i => e i = k),
        a i z * primeLaurentMonomial s (e i) z :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem e hi)
        (fun i => a i z * primeLaurentMonomial s (e i) z)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold groupedPrimeLaurentCoefficient
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

theorem groupedPrimeLaurentCoefficient_meromorphic {ι : Type*} [DecidableEq ι]
    (s : Finset ℕ) (t : Finset ι) (e : ι → s → ℤ) (a : ι → ℂ → ℂ)
    (ha : ∀ i ∈ t, MeromorphicAt (a i) 0) (k : s → ℤ) :
    MeromorphicAt (groupedPrimeLaurentCoefficient s t e a k) 0 := by
  classical
  unfold groupedPrimeLaurentCoefficient
  exact MeromorphicAt.fun_sum (fun i hi => ha i (Finset.mem_filter.mp hi).1)

/-- Grouping is mandatory: one nonzero raw summand alone does not suffice. -/
theorem primeLaurent_sum_germ_nonzero {ι : Type*} [DecidableEq ι]
    (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    (t : Finset ι) (e : ι → s → ℤ) (a : ι → ℂ → ℂ)
    (ha : ∀ i ∈ t, MeromorphicAt (a i) 0)
    (hne : ∃ k ∈ t.image e, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      groupedPrimeLaurentCoefficient s t e a k z = 0) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ∑ i ∈ t, a i z * primeLaurentMonomial s (e i) z = 0 := by
  classical
  have h := meromorphic_frequency_germ_nonzero (t.image e)
    (groupedPrimeLaurentCoefficient s t e a) (primeLaurentFrequency s)
    (fun k _ => groupedPrimeLaurentCoefficient_meromorphic s t e a ha k)
    (primeLaurentFrequency_injective s hs).injOn hne
  intro hz
  apply h
  filter_upwards [hz] with z hz
  rw [primeLaurent_sum_grouped s t e a z] at hz
  simpa only [primeLaurentMonomial_eq_exp] using hz

/-- The genuine integer factorization supplies every prime multiplicity. -/
theorem primeLogFrequency_factorization (s : Finset ℕ) (q : ℕ)
    (hq : q.primeFactors ⊆ s) :
    primeLogFrequency s (fun p => (q.factorization (p : ℕ) : ℤ)) = Real.log q := by
  classical
  unfold primeLogFrequency
  simp only [Int.cast_natCast]
  rw [Finset.sum_coe_sort s (fun p : ℕ => (q.factorization p : ℝ)*Real.log p),
    Real.log_nat_eq_sum_factorization]
  unfold Finsupp.sum
  symm
  apply Finset.sum_subset (by simpa only [Nat.support_factorization] using hq)
  intro p hp hnp
  have hz : q.factorization p = 0 := Finsupp.notMem_support_iff.mp hnp
  simp [hz]

/-- Exact arithmetic phase-to-Laurent adapter, with full prime-power exponents. -/
theorem primePhase_eq_factorization_monomial (s : Finset ℕ) (q : ℕ)
    (hq : q.primeFactors ⊆ s) (z : ℂ) :
    primePhase q z =
      primeLaurentMonomial s (fun p => (q.factorization (p : ℕ) : ℤ)) z := by
  rw [primeLaurentMonomial_eq_exp]
  unfold primeLaurentFrequency primePhase
  rw [primeLogFrequency_factorization s q hq]

end Zeta23.OPICARound4.RegularCells
