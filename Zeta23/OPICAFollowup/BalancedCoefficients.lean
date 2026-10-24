import Zeta23.OPICA.NativeArithmeticAdapter
import Mathlib.Data.Nat.Choose.Sum

/-!
# The actual J17 coefficients

The multiplication below is Dirichlet convolution of arithmetic functions.  The
cutoff is a real number, and coprimality is imposed on every integer factor.
In particular, no squarefreeness condition is imposed on the total product.

The two coefficients are the literal finite binomial sum and large-factor
convolution from J17.  Their identity is proved from Möbius inversion, rather
than supplied by a field or by a caller.  Physical fields use the existing P0
translated drive, including its inverse square-root weight and causal bound.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Zeta23.OPICAFollowup

open Zeta23.OPICA

/-- Restrict an arithmetic function to integers coprime to the frozen palette. -/
def coprimeCoefficients (Q : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n Q then f n else 0, by simp⟩

/-- The actual unweighted Möbius coefficient on the coprimality palette. -/
def nativeInverseCoefficients (Q : ℕ) : ArithmeticFunction ℝ :=
  coprimeCoefficients Q (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

/-- The actual free positive-integer coefficient on the same palette. -/
def nativeFreeCoefficients (Q : ℕ) : ArithmeticFunction ℝ :=
  coprimeCoefficients Q (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- The real-cutoff small Möbius factors. -/
def nativeSmallCoefficients (Q : ℕ) (Y : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ Y then nativeInverseCoefficients Q n else 0, by simp⟩

/-- The strict complementary real-cutoff large Möbius factors. -/
def nativeLargeCoefficients (Q : ℕ) (Y : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Y < (n : ℝ) then nativeInverseCoefficients Q n else 0, by simp⟩

/-- The literal small-factor J17 binomial sum; its `i` is the paper's `i-1`. -/
def nativeSieveCoefficients (Q : ℕ) (Y : ℝ) (r : ℕ) : ArithmeticFunction ℝ :=
  ∑ i ∈ range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) •
    (nativeSmallCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i)

/-- The literal balanced large-factor coefficient, with all free integer convolutions. -/
def nativeBalancedCoefficients (Q : ℕ) (Y : ℝ) (r : ℕ) : ArithmeticFunction ℝ :=
  nativeLargeCoefficients Q Y ^ r * nativeFreeCoefficients Q ^ (r - 1)

/-- Canonical build interface: the actual small inverse factor `μ_{≤Y,Q}`. -/
def smallInverseCoefficients (Q : ℕ) (Y : ℝ) : ArithmeticFunction ℝ :=
  nativeSmallCoefficients Q Y

/-- Canonical build interface: the balanced coefficient `c_r`. -/
def balancedInverseCoefficients (Q : ℕ) (Y : ℝ) (r : ℕ) : ArithmeticFunction ℝ :=
  nativeBalancedCoefficients Q Y r

/-- Canonical build interface: the full finite Type-I/binomial coefficient `s_r`. -/
def typeICoefficients (Q : ℕ) (Y : ℝ) (r : ℕ) : ArithmeticFunction ℝ :=
  nativeSieveCoefficients Q Y r

private theorem coprimeCoefficients_one (Q : ℕ) :
    coprimeCoefficients Q 1 = 1 := by
  ext n
  by_cases hn : n = 1 <;> simp [coprimeCoefficients, ArithmeticFunction.one_apply, hn]

private theorem coprimeCoefficients_mul (Q : ℕ) (f g : ArithmeticFunction ℝ) :
    coprimeCoefficients Q (f * g) = coprimeCoefficients Q f * coprimeCoefficients Q g := by
  ext n
  change (if Nat.Coprime n Q then (f * g) n else 0) =
    ∑ p ∈ n.divisorsAntidiagonal,
      (if Nat.Coprime p.1 Q then f p.1 else 0) *
        (if Nat.Coprime p.2 Q then g p.2 else 0)
  by_cases hn : Nat.Coprime n Q
  · rw [if_pos hn, ArithmeticFunction.mul_apply]
    apply sum_congr rfl
    intro p hp
    have hc : Nat.Coprime p.1 Q ∧ Nat.Coprime p.2 Q := by
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.coprime_mul_iff_left] at hn
      exact hn
    rw [if_pos hc.1, if_pos hc.2]
  · rw [if_neg hn]
    symm
    apply sum_eq_zero
    intro p hp
    have hc : ¬(Nat.Coprime p.1 Q ∧ Nat.Coprime p.2 Q) := by
      intro h
      apply hn
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.coprime_mul_iff_left]
      exact h
    by_cases h₁ : Nat.Coprime p.1 Q
    · have h₂ : ¬Nat.Coprime p.2 Q := fun h₂ => hc ⟨h₁, h₂⟩
      simp [h₂]
    · simp [h₁]

/-- The actual coprimality-restricted Möbius and free coefficients are convolution inverses. -/
theorem native_coefficients_moebius_inverse (Q : ℕ) :
    nativeInverseCoefficients Q * nativeFreeCoefficients Q = 1 := by
  rw [nativeInverseCoefficients, nativeFreeCoefficients, ← coprimeCoefficients_mul,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, coprimeCoefficients_one]

theorem native_small_large_split (Q : ℕ) (Y : ℝ) :
    nativeSmallCoefficients Q Y + nativeLargeCoefficients Q Y = nativeInverseCoefficients Q := by
  ext n
  change (if (n : ℝ) ≤ Y then nativeInverseCoefficients Q n else 0) +
    (if Y < (n : ℝ) then nativeInverseCoefficients Q n else 0) = nativeInverseCoefficients Q n
  by_cases hn : (n : ℝ) ≤ Y
  · simp [hn, not_lt_of_ge hn]
  · simp [hn, lt_of_not_ge hn]

set_option maxRecDepth 2048 in
private theorem finite_binomial_complement (x : ArithmeticFunction ℝ) (r : ℕ) :
    (∑ i ∈ range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) • x ^ (i + 1)) =
      1 - (1 - x) ^ r := by
  have h := add_pow (-x) (1 : ArithmeticFunction ℝ) r
  rw [sum_range_succ'] at h
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one] at h
  have hs : (∑ i ∈ range r, (-x) ^ (i + 1) * (r.choose (i + 1) : ArithmeticFunction ℝ)) =
      -(∑ i ∈ range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) • x ^ (i + 1)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    rw [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast]
    have hneg : -x = (-1 : ArithmeticFunction ℝ) * x := by ring
    rw [hneg, mul_pow, pow_succ (-1 : ArithmeticFunction ℝ) i]
    ring
  rw [hs] at h
  have he : -x + 1 = 1 - x := by ring
  rw [he] at h
  linear_combination h

private theorem native_j17_coefficient_identity (Q : ℕ) (Y : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    nativeInverseCoefficients Q =
      nativeSieveCoefficients Q Y r + nativeBalancedCoefficients Q Y r := by
  let v := nativeInverseCoefficients Q
  let u := nativeFreeCoefficients Q
  let a := nativeSmallCoefficients Q Y
  let b := nativeLargeCoefficients Q Y
  have hvu : v * u = 1 := native_coefficients_moebius_inverse Q
  have huv : u * v = 1 := by rw [mul_comm]; exact hvu
  have hbu : b * u = 1 - a * u := by
    have hsplit : a + b = v := native_small_large_split Q Y
    calc b * u = (a + b) * u - a * u := by ring
         _ = 1 - a * u := by rw [hsplit, hvu]
  have hsmall : nativeSieveCoefficients Q Y r * u = 1 - (1 - a * u) ^ r := by
    rw [nativeSieveCoefficients, sum_mul]
    have he : (∑ i ∈ range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) •
        (nativeSmallCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i) * u) =
        ∑ i ∈ range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) • (a * u) ^ (i + 1) := by
      apply sum_congr rfl
      intro i hi
      rw [smul_mul_assoc]
      congr 1
      simp only [a, u, mul_pow, pow_succ]
      ring
    rw [he, finite_binomial_complement]
  have hlarge : nativeBalancedCoefficients Q Y r * u = (1 - a * u) ^ r := by
    change b ^ r * u ^ (r - 1) * u = _
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr, ← mul_pow, hbu]
  have hsum : (nativeSieveCoefficients Q Y r + nativeBalancedCoefficients Q Y r) * u = 1 := by
    rw [add_mul, hsmall, hlarge]
    ring
  calc v = 1 * v := by rw [one_mul]
       _ = ((nativeSieveCoefficients Q Y r + nativeBalancedCoefficients Q Y r) * u) * v := by rw [hsum]
       _ = nativeSieveCoefficients Q Y r + nativeBalancedCoefficients Q Y r := by
         rw [mul_assoc, huv, mul_one]

/-- The full J17 identity, with the common finite horizon for the actual P0 physical fields.
The causal statement proves local finiteness before taking the infinite sum. -/
theorem native_binomial_inverse_identity (Q : ℕ) (Y : ℝ) (_hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) :
    nativeInverseCoefficients Q =
        typeICoefficients Q Y r + balancedInverseCoefficients Q Y r ∧
    (∀ (U : BoundedCausalDrive) (T t : ℝ), t ≤ T →
      (∀ n : ℕ, driveIndexBound T < n →
        nativeInverseCoefficients Q n * translatedDrive U n t = 0) ∧
      (∑' n : ℕ, nativeInverseCoefficients Q n * translatedDrive U n t) =
        finiteDriveField U (driveIndexBound T) (typeICoefficients Q Y r) t +
        finiteDriveField U (driveIndexBound T) (balancedInverseCoefficients Q Y r) t) := by
  have hid := native_j17_coefficient_identity Q Y r (by omega)
  refine ⟨hid, ?_⟩
  intro U T t ht
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [translatedDrive_zero_of_index_gt U ht hn, mul_zero]
  · rw [drive_sum_eq_finite U _ ht]
    change finiteDriveField U (driveIndexBound T) (nativeInverseCoefficients Q) t = _
    rw [hid]
    exact finiteDriveField_add U _ _ _ t

/-! The tuple count below includes every ordered positive factorization. -/

private theorem arithmetic_sum_apply (s : Finset ℕ) (f : ℕ → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ArithmeticFunction.add_apply, ih]

/-- An exact finite tuple expansion of convolution powers, with zero factors excluded by
the positive product, rather than by a squarefree-product assumption. -/
theorem dirichlet_power_tuple_expansion (f : ArithmeticFunction ℝ) (k n : ℕ) :
    (f ^ k) n = ∑ w ∈ Nat.finMulAntidiag k n, ∏ i, f (w i) := by
  classical
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 1
    · subst n
      simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left hn, hn]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    simp_rw [ih, mul_sum]
    let S : Finset (Σ p : ℕ × ℕ, Fin k → ℕ) :=
      n.divisorsAntidiagonal.sigma (fun p => Nat.finMulAntidiag k p.2)
    calc (∑ p ∈ n.divisorsAntidiagonal, ∑ w ∈ Nat.finMulAntidiag k p.2,
          f p.1 * ∏ i, f (w i)) = ∑ a ∈ S, f a.1.1 * ∏ i, f (a.2 i) := by
           rw [show S = n.divisorsAntidiagonal.sigma (fun p => Nat.finMulAntidiag k p.2) from rfl,
             Finset.sum_sigma]
         _ = ∑ w ∈ Nat.finMulAntidiag (k + 1) n, ∏ i, f (w i) := by
           apply sum_bij (fun a _ => Fin.cons a.1.1 a.2)
           · intro a ha
             obtain ⟨ha₁, ha₂⟩ := mem_sigma.mp ha
             apply Nat.mem_finMulAntidiag.mpr
             constructor
             · simpa [Fin.prod_univ_succ, Nat.prod_eq_of_mem_finMulAntidiag ha₂] using
                 (Nat.mem_divisorsAntidiagonal.mp ha₁).1
             · exact (Nat.mem_divisorsAntidiagonal.mp ha₁).2
           · intro a ha b hb hab
             have hfirst : a.1.1 = b.1.1 := by simpa using congrArg (fun w => w 0) hab
             have htail : a.2 = b.2 := by simpa using congrArg Fin.tail hab
             have hsecond : a.1.2 = b.1.2 :=
               (Nat.prod_eq_of_mem_finMulAntidiag (mem_sigma.mp ha).2).symm.trans
                 ((congrArg (fun w : Fin k → ℕ => ∏ i, w i) htail).trans
                   (Nat.prod_eq_of_mem_finMulAntidiag (mem_sigma.mp hb).2))
             exact Sigma.ext (Prod.ext hfirst hsecond) (heq_of_eq htail)
           · intro w hw
             let p : ℕ × ℕ := (w 0, ∏ i : Fin k, w i.succ)
             have hp : p.1 * p.2 = n := by
               simpa [p, Fin.prod_univ_succ] using Nat.prod_eq_of_mem_finMulAntidiag hw
             have hn := (Nat.mem_finMulAntidiag.mp hw).2
             refine ⟨⟨p, Fin.tail w⟩, mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
             · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hp, hn⟩
             · exact Nat.mem_finMulAntidiag.mpr ⟨rfl, right_ne_zero_of_mul (by rw [hp]; exact hn)⟩
             · exact Fin.cons_self_tail w
           · intro a ha
             simp [Fin.prod_univ_succ]

/-- The existing P0 divisor count is exactly a convolution power of the free coefficient. -/
theorem zeta_power_eq_divisorCount (k n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k) n = (divisorCount k n : ℝ) := by
  rw [dirichlet_power_tuple_expansion]
  have hweight : ∀ w ∈ Nat.finMulAntidiag k n,
      (∏ i, (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (w i)) = 1 := by
    intro w hw
    apply prod_eq_one
    intro i hi
    simp [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (Nat.ne_zero_of_mem_finMulAntidiag hw i)]
  rw [sum_congr rfl hweight]
  simp [divisorCount]

private theorem zeta_power_nonneg (k n : ℕ) :
    0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k) n := by
  rw [zeta_power_eq_divisorCount]
  positivity

private theorem zeta_power_step (k n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k) n ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (k + 1)) n := by
  by_cases hn : n = 0
  · subst n; simp
  · rw [pow_succ, ArithmeticFunction.coe_mul_zeta_apply]
    exact single_le_sum (fun d hd => zeta_power_nonneg k d)
      (Nat.mem_divisors.mpr ⟨dvd_refl n, hn⟩)

private theorem zeta_power_mono {k l : ℕ} (hkl : k ≤ l) (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k) n ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ l) n := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih => exact ih.trans (zeta_power_step l n)

private theorem convolution_abs_bound (f g F G : ArithmeticFunction ℝ)
    (hf : ∀ n, |f n| ≤ F n) (hg : ∀ n, |g n| ≤ G n) (n : ℕ) :
    |(f * g) n| ≤ (F * G) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  calc |∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2| ≤
      ∑ p ∈ n.divisorsAntidiagonal, |f p.1 * g p.2| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ p ∈ n.divisorsAntidiagonal, F p.1 * G p.2 := by
         apply sum_le_sum
         intro p hp
         rw [abs_mul]
         exact mul_le_mul (hf p.1) (hg p.2) (abs_nonneg _) ((abs_nonneg _).trans (hf p.1))

private theorem convolution_power_abs_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, |f n| ≤ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n) (k n : ℕ) :
    |(f ^ k) n| ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ k) n := by
  induction k generalizing n with
  | zero => by_cases hn : n = 1 <;> simp [hn]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact convolution_abs_bound _ _ _ _ ih hf n

private theorem native_inverse_abs_le_zeta (Q n : ℕ) :
    |nativeInverseCoefficients Q n| ≤ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  by_cases hn : n = 0
  · subst n; simp
  · by_cases hQ : Nat.Coprime n Q
    · simp only [nativeInverseCoefficients, coprimeCoefficients, ArithmeticFunction.coe_mk,
        if_pos hQ, ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne hn, Nat.cast_one]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    · simp [nativeInverseCoefficients, coprimeCoefficients, hQ,
        ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn]

private theorem native_free_abs_le_zeta (Q n : ℕ) :
    |nativeFreeCoefficients Q n| ≤ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  change |if Nat.Coprime n Q then (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n else 0| ≤
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n
  by_cases hn : n = 0
  · subst n; simp
  · by_cases hQ : Nat.Coprime n Q
    · rw [if_pos hQ]
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn]
    · rw [if_neg hQ]
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn]

private theorem native_small_abs_le_zeta (Q : ℕ) (Y : ℝ) (n : ℕ) :
    |nativeSmallCoefficients Q Y n| ≤ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  by_cases hn : (n : ℝ) ≤ Y
  · simpa [nativeSmallCoefficients, hn] using native_inverse_abs_le_zeta Q n
  · simp only [nativeSmallCoefficients, ArithmeticFunction.coe_mk, if_neg hn, abs_zero]
    simpa using zeta_power_nonneg 1 n

private theorem native_large_abs_le_zeta (Q : ℕ) (Y : ℝ) (n : ℕ) :
    |nativeLargeCoefficients Q Y n| ≤ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
  by_cases hn : Y < (n : ℝ)
  · simpa [nativeLargeCoefficients, hn] using native_inverse_abs_le_zeta Q n
  · simp only [nativeLargeCoefficients, ArithmeticFunction.coe_mk, if_neg hn, abs_zero]
    simpa using zeta_power_nonneg 1 n

private theorem native_factor_block_abs_bound (Q : ℕ) (_Y : ℝ) (i j n : ℕ)
    (b : ArithmeticFunction ℝ)
    (hb : ∀ n, |b n| ≤ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n) :
    |(b ^ i * nativeFreeCoefficients Q ^ j) n| ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (i + j)) n := by
  rw [pow_add]
  exact convolution_abs_bound _ _ _ _
    (convolution_power_abs_bound b hb i)
    (convolution_power_abs_bound (nativeFreeCoefficients Q) (native_free_abs_le_zeta Q) j) n

private theorem shifted_choose_sum (r : ℕ) :
    (∑ i ∈ range r, (r.choose (i + 1) : ℝ)) = (2 : ℝ) ^ r - 1 := by
  have h := Nat.sum_range_choose r
  rw [sum_range_succ'] at h
  simp only [Nat.choose_zero_right] at h
  have h' : (∑ i ∈ range r, (r.choose (i + 1) : ℝ)) + 1 = (2 : ℝ) ^ r := by
    exact_mod_cast h
  linarith

/-- The actual J17 coefficient envelopes for every positive or nonsquarefree product.
The proof counts unrestricted ordered integer tuples and includes repeated primes across factors. -/
theorem balanced_coeff_divisor_bound (Q : ℕ) (Y : ℝ) (_hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    |balancedInverseCoefficients Q Y r n| ≤ (divisorCount (2 * r - 1) n : ℝ) ∧
    |typeICoefficients Q Y r n| ≤
      ((2 : ℝ) ^ r - 1) * (divisorCount (2 * r - 1) n : ℝ) := by
  change |nativeBalancedCoefficients Q Y r n| ≤ (divisorCount (2 * r - 1) n : ℝ) ∧
    |nativeSieveCoefficients Q Y r n| ≤
      ((2 : ℝ) ^ r - 1) * (divisorCount (2 * r - 1) n : ℝ)
  have hc := native_factor_block_abs_bound Q Y r (r - 1) n
    (nativeLargeCoefficients Q Y) (native_large_abs_le_zeta Q Y)
  have horder : r + (r - 1) = 2 * r - 1 := by omega
  refine ⟨?_, ?_⟩
  · simpa [nativeBalancedCoefficients, horder, zeta_power_eq_divisorCount] using hc
  · rw [nativeSieveCoefficients, arithmetic_sum_apply]
    calc |∑ i ∈ range r, (((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) •
          (nativeSmallCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i)) n| ≤
        ∑ i ∈ range r, |(((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) •
          (nativeSmallCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i)) n| :=
            abs_sum_le_sum_abs _ _
         _ ≤ ∑ i ∈ range r, (r.choose (i + 1) : ℝ) * (divisorCount (2 * r - 1) n : ℝ) := by
           apply sum_le_sum
           intro i hi
           have hib := native_factor_block_abs_bound Q Y (i + 1) i n
             (nativeSmallCoefficients Q Y) (native_small_abs_le_zeta Q Y)
           have hiorder : i + 1 + i ≤ 2 * r - 1 := by have := mem_range.mp hi; omega
           have hib' : |(nativeSmallCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i) n| ≤
               (divisorCount (2 * r - 1) n : ℝ) := by
             exact hib.trans (by simpa [zeta_power_eq_divisorCount] using zeta_power_mono hiorder n)
           simp only [ArithmeticFunction.smul_map, smul_eq_mul, abs_mul, abs_pow,
             abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
           exact mul_le_mul_of_nonneg_left hib' (Nat.cast_nonneg _)
         _ = ((2 : ℝ) ^ r - 1) * (divisorCount (2 * r - 1) n : ℝ) := by
           rw [← sum_mul, shifted_choose_sum]

end Zeta23.OPICAFollowup
