import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Scalar stretched exponential Fourier tails

The summability and tail integral below are proved from positive decay and
scale parameters. No summability or Fourier reconstruction assumption is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Zeta23.CCM

/-- The scalar stretched exponential used by the actual Fourier estimates. -/
def originalDetectorScalarFourierDecay (L d x : ℝ) : ℝ :=
  Real.exp (-d * Real.sqrt (x / L))

/-- The exact integral of the scalar majorant from `x` to infinity. -/
def originalDetectorScalarFourierTailIntegral (L d x : ℝ) : ℝ :=
  2 * L * Real.exp (-d * Real.sqrt (x / L)) *
    (Real.sqrt (x / L) / d + 1 / d ^ 2)

private theorem scalarFourierTailIntegral_hasDerivAt {L d x : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hx : 0 < x) :
    HasDerivAt (originalDetectorScalarFourierTailIntegral L d)
      (-originalDetectorScalarFourierDecay L d x) x := by
  have hq : 0 < x / L := div_pos hx hL
  have hsqrt : 0 < Real.sqrt (x / L) := Real.sqrt_pos.2 hq
  have hr := ((hasDerivAt_id x).div_const L).sqrt hq.ne'
  have he := (hr.const_mul (-d)).exp
  have hp := (he.mul ((hr.div_const d).add_const (1 / d ^ 2))).const_mul (2 * L)
  convert! hp using 1
  · ext y
    simp only [originalDetectorScalarFourierTailIntegral, Pi.mul_apply, id_eq]
    ring
  · simp only [originalDetectorScalarFourierDecay, id_eq]
    field_simp [hL.ne', hd.ne', hsqrt.ne']
    ring

private theorem scalarFourierTailIntegral_tendsto_zero {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) :
    Tendsto (originalDetectorScalarFourierTailIntegral L d) atTop (𝓝 0) := by
  have hu : Tendsto (fun x : ℝ => d * Real.sqrt (x / L)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hL)).const_mul_atTop hd
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hu
  have hye := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have hsum := hye.add he
  have hfinal := hsum.const_mul (2 * L / d ^ 2)
  convert hfinal using 1
  · ext x
    simp only [originalDetectorScalarFourierTailIntegral, pow_one, Function.comp_apply]
    field_simp [hd.ne']
  · simp

/-- The scalar majorant is integrable on every nonnegative half-line,
including the square-root boundary at zero. -/
theorem originalDetectorScalarFourierDecay_integrableOn {L d a : ℝ}
    (hL : 0 < L) (hd : 0 < d) (ha : 0 ≤ a) :
    IntegrableOn (originalDetectorScalarFourierDecay L d) (Ioi a) := by
  have hcont : Continuous (originalDetectorScalarFourierTailIntegral L d) := by
    unfold originalDetectorScalarFourierTailIntegral
    fun_prop
  have hi := integrableOn_Ioi_deriv_of_nonpos hcont.continuousWithinAt
    (fun x hx => scalarFourierTailIntegral_hasDerivAt hL hd (lt_of_le_of_lt ha hx))
    (fun x _ => neg_nonpos.2 (Real.exp_pos _).le)
    (scalarFourierTailIntegral_tendsto_zero hL hd)
  exact integrable_neg_iff.1 hi

/-- Exact evaluation of the improper scalar tail integral. -/
theorem originalDetectorScalarFourierDecay_integral_Ioi {L d a : ℝ}
    (hL : 0 < L) (hd : 0 < d) (ha : 0 ≤ a) :
    (∫ x in Ioi a, originalDetectorScalarFourierDecay L d x) =
      originalDetectorScalarFourierTailIntegral L d a := by
  have hcont : Continuous (originalDetectorScalarFourierTailIntegral L d) := by
    unfold originalDetectorScalarFourierTailIntegral
    fun_prop
  have hi := integral_Ioi_of_hasDerivAt_of_nonpos hcont.continuousWithinAt
    (fun x hx => scalarFourierTailIntegral_hasDerivAt hL hd (lt_of_le_of_lt ha hx))
    (fun x _ => neg_nonpos.2 (Real.exp_pos _).le)
    (scalarFourierTailIntegral_tendsto_zero hL hd)
  simpa only [integral_neg, zero_sub, neg_inj] using hi

private theorem scalarFourierDecay_antitone {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    Antitone (originalDetectorScalarFourierDecay L d) := by
  intro x y hxy
  unfold originalDetectorScalarFourierDecay
  apply Real.exp_le_exp.2
  exact mul_le_mul_of_nonpos_left
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hxy hL.le)) (neg_nonpos.2 hd.le)

/-- Summability is derived from the explicit primitive and the integral test. -/
theorem originalDetectorScalarFourierDecay_summable {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) :
    Summable (fun n : ℕ => originalDetectorScalarFourierDecay L d n) := by
  exact ((scalarFourierDecay_antitone hL hd).antitoneOn (Ici 0)).summable_of_integrableOn_Ioi_zero
    (originalDetectorScalarFourierDecay_integrableOn hL hd (by norm_num))
    (fun x _ => (Real.exp_pos _).le)

/-- The sum over the strict tail `n > N` is at most the exact integral
starting at `N`, with no index shift in the bound. -/
theorem originalDetectorScalarFourierDecay_tsum_tail_le {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ) :
    (∑' n : ℕ, originalDetectorScalarFourierDecay L d ((n + N + 1 : ℕ) : ℝ)) ≤
      2 * L * Real.exp (-d * Real.sqrt ((N : ℝ) / L)) *
        (Real.sqrt ((N : ℝ) / L) / d + 1 / d ^ 2) := by
  have hi := AntitoneOn.tsum_comp_add_le_integral N
    ((scalarFourierDecay_antitone hL hd).antitoneOn (Ici (N : ℝ)))
    (originalDetectorScalarFourierDecay_integrableOn hL hd (Nat.cast_nonneg N))
    (fun x _ => (Real.exp_pos _).le)
  rw [originalDetectorScalarFourierDecay_integral_Ioi hL hd (Nat.cast_nonneg N)] at hi
  exact hi

/-- Every polynomial factor can be absorbed by an exponential using its
Taylor term. The factorial and reciprocal decay rate are explicit. -/
theorem originalDetectorScalarPower_mul_exp_neg_le {d t : ℝ}
    (hd : 0 < d) (ht : 0 ≤ t) (k : ℕ) :
    t ^ k * Real.exp (-d * t) ≤ (k.factorial : ℝ) / d ^ k := by
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpow := Real.pow_div_factorial_le_exp (d * t) (mul_nonneg hd.le ht) k
  have hle := (div_le_iff₀ hf).1 hpow
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-d * t)).le
  have he : Real.exp (d * t) * Real.exp (-d * t) = 1 := by
    rw [← Real.exp_add]
    have : d * t + -d * t = 0 := by ring
    rw [this, Real.exp_zero]
  apply (le_div_iff₀ (pow_pos hd k)).2
  calc
    _ = (d * t) ^ k * Real.exp (-d * t) := by rw [mul_pow]; ring
    _ ≤ (Real.exp (d * t) * (k.factorial : ℝ)) * Real.exp (-d * t) := hmul
    _ = (k.factorial : ℝ) := by rw [mul_right_comm, he, one_mul]

/-- Absorb an arbitrary derivative weight into half of the stretched
exponential decay. -/
theorem originalDetectorScalarWeightedDecay_le {c t : ℝ}
    (hc : 0 < c) (ht : 0 ≤ t) (r : ℕ) :
    t ^ r * Real.exp (-c * Real.sqrt t) ≤
      ((2 * r).factorial : ℝ) * (2 / c) ^ (2 * r) *
        Real.exp (-(c / 2) * Real.sqrt t) := by
  have hhalf : 0 < c / 2 := by positivity
  have hp := originalDetectorScalarPower_mul_exp_neg_le hhalf
    (Real.sqrt_nonneg t) (2 * r)
  have hm := mul_le_mul_of_nonneg_right hp
    (Real.exp_pos (-(c / 2) * Real.sqrt t)).le
  have he : Real.exp (-(c / 2) * Real.sqrt t) *
      Real.exp (-(c / 2) * Real.sqrt t) = Real.exp (-c * Real.sqrt t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : (Real.sqrt t) ^ (2 * r) = t ^ r := by
    rw [pow_mul, Real.sq_sqrt ht]
  have hi : (c / 2)⁻¹ = 2 / c := by field_simp
  calc
    _ = (Real.sqrt t) ^ (2 * r) * Real.exp (-(c / 2) * Real.sqrt t) *
        Real.exp (-(c / 2) * Real.sqrt t) := by rw [hs, mul_assoc, he]
    _ ≤ ((2 * r).factorial : ℝ) / (c / 2) ^ (2 * r) *
        Real.exp (-(c / 2) * Real.sqrt t) := hm
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow, hi]

/-- If the square-root cutoff dominates the aperture, the exact scalar
tail is bounded by a pure stretched exponential with source-independent
factor `20 / d^3`. -/
theorem originalDetectorScalarFourierTailIntegral_le_exp {L d a : ℝ}
    (_hL : 0 < L) (hd : 0 < d) (_ha : 0 ≤ a)
    (hu : L ≤ Real.sqrt (a / L)) :
    originalDetectorScalarFourierTailIntegral L d a ≤
      20 / d ^ 3 * Real.exp (-(d / 2) * Real.sqrt (a / L)) := by
  let u := Real.sqrt (a / L)
  let e := d / 2
  have he : 0 < e := by dsimp [e]; positivity
  have hun : 0 ≤ u := Real.sqrt_nonneg _
  have h1 := originalDetectorScalarPower_mul_exp_neg_le he hun 1
  have h2 := originalDetectorScalarPower_mul_exp_neg_le he hun 2
  norm_num only [Nat.factorial, pow_one, Nat.cast_one, Nat.cast_ofNat] at h1 h2
  have hm : 2 * (u ^ 2 / d + u / d ^ 2) * Real.exp (-e * u) ≤ 20 / d ^ 3 := by
    have h1' := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / d ^ 2 by positivity)
    have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 / d by positivity)
    have hc : 2 / d * (2 / e ^ 2) + 2 / d ^ 2 * (1 / e) = 20 / d ^ 3 := by
      dsimp [e]
      field_simp
      ring
    calc
      _ = 2 / d * (u ^ 2 * Real.exp (-e * u)) +
          2 / d ^ 2 * (u * Real.exp (-e * u)) := by ring
      _ ≤ 2 / d * (2 / e ^ 2) + 2 / d ^ 2 * (1 / e) := add_le_add h2' h1'
      _ = _ := hc
  have hex : Real.exp (-d * u) = Real.exp (-e * u) * Real.exp (-e * u) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [e]
    ring
  change 2 * L * Real.exp (-d * u) * (u / d + 1 / d ^ 2) ≤ _
  calc
    _ ≤ 2 * u * Real.exp (-d * u) * (u / d + 1 / d ^ 2) := by
      gcongr
    _ = (2 * (u ^ 2 / d + u / d ^ 2) * Real.exp (-e * u)) *
        Real.exp (-e * u) := by rw [hex]; ring
    _ ≤ (20 / d ^ 3) * Real.exp (-e * u) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le

/-- The strict natural tail with the aperture dominated by its square-root
cutoff has a pure exponential bound. -/
theorem originalDetectorScalarFourierDecay_tsum_tail_le_exp {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ)
    (hu : L ≤ Real.sqrt ((N : ℝ) / L)) :
    (∑' n : ℕ, originalDetectorScalarFourierDecay L d ((n + N + 1 : ℕ) : ℝ)) ≤
      20 / d ^ 3 * Real.exp (-(d / 2) * Real.sqrt ((N : ℝ) / L)) :=
  (originalDetectorScalarFourierDecay_tsum_tail_le hL hd N).trans
    (originalDetectorScalarFourierTailIntegral_le_exp hL hd (Nat.cast_nonneg N) hu)

private theorem scalarFourierDecay_nat_tail_summable {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ) :
    Summable (fun n : ℕ => if N < n then originalDetectorScalarFourierDecay L d n else 0) := by
  let f : ℕ → ℝ := fun n => if N < n then originalDetectorScalarFourierDecay L d n else 0
  have hshift : (fun n : ℕ => f (n + (N + 1))) =
      (fun n : ℕ => originalDetectorScalarFourierDecay L d ((n + (N + 1) : ℕ) : ℝ)) := by
    ext n
    simp only [f, if_pos (show N < n + (N + 1) by omega)]
  change Summable f
  apply (summable_nat_add_iff (f := f) (N + 1)).1
  rw [hshift]
  exact (summable_nat_add_iff (N + 1)).2
    (originalDetectorScalarFourierDecay_summable hL hd)

private theorem scalarFourierDecay_nat_tsum_tail_eq {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ) :
    (∑' n : ℕ, if N < n then originalDetectorScalarFourierDecay L d n else 0) =
      ∑' n : ℕ, originalDetectorScalarFourierDecay L d ((n + N + 1 : ℕ) : ℝ) := by
  let f : ℕ → ℝ := fun n => if N < n then originalDetectorScalarFourierDecay L d n else 0
  have hs : Summable f := scalarFourierDecay_nat_tail_summable hL hd N
  have hsum : ∑ n ∈ Finset.range (N + 1), f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [f, if_neg (show ¬ N < n by omega)]
  have ht := hs.sum_add_tsum_nat_add (N + 1)
  rw [hsum, zero_add] at ht
  change (∑' n : ℕ, f n) = _
  rw [← ht]
  apply tsum_congr
  intro n
  simp only [f, if_pos (show N < n + (N + 1) by omega), Nat.add_assoc]

/-- Summability of the literal signed scalar tail, derived by the positive
and negative natural-frequency decomposition. -/
theorem originalDetectorScalarFourierDecay_signed_tail_summable {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ) :
    Summable (fun n : ℤ => if N < n.natAbs then
      originalDetectorScalarFourierDecay L d |(n : ℝ)| else 0) := by
  let f : ℕ → ℝ := fun n => if N < n then originalDetectorScalarFourierDecay L d n else 0
  let g : ℤ → ℝ := fun n => if N < n.natAbs then
    originalDetectorScalarFourierDecay L d |(n : ℝ)| else 0
  have hs : Summable f := scalarFourierDecay_nat_tail_summable hL hd N
  have hpos : (fun n : ℕ => g n) = f := by
    ext n
    simp [g, f]
  have hneg : (fun n : ℕ => g (-(n + 1))) = (fun n : ℕ => f (n + 1)) := by
    ext n
    dsimp only [g, f]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast,
      abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
  change Summable g
  apply Summable.of_nat_of_neg_add_one
  · rw [hpos]
    exact hs
  · rw [hneg]
    exact (summable_nat_add_iff 1).2 hs

/-- The exact signed-frequency tail equals twice the positive strict tail;
zero is absent for every natural cutoff. -/
theorem originalDetectorScalarFourierDecay_signed_tsum_tail_eq {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ) :
    (∑' n : ℤ, if N < n.natAbs then
      originalDetectorScalarFourierDecay L d |(n : ℝ)| else 0) =
      2 * ∑' n : ℕ, originalDetectorScalarFourierDecay L d ((n + N + 1 : ℕ) : ℝ) := by
  let f : ℕ → ℝ := fun n => if N < n then originalDetectorScalarFourierDecay L d n else 0
  let g : ℤ → ℝ := fun n => if N < n.natAbs then
    originalDetectorScalarFourierDecay L d |(n : ℝ)| else 0
  have hs : Summable f := scalarFourierDecay_nat_tail_summable hL hd N
  have hpos : (fun n : ℕ => g n) = f := by
    ext n
    simp [g, f]
  have hneg : (fun n : ℕ => g (-(n + 1))) = (fun n : ℕ => f (n + 1)) := by
    ext n
    dsimp only [g, f]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast,
      abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
  have hgpos : Summable (fun n : ℕ => g n) := by rw [hpos]; exact hs
  have hgneg : Summable (fun n : ℕ => g (-(n + 1))) := by
    rw [hneg]
    exact (summable_nat_add_iff 1).2 hs
  have hz : f 0 = 0 := by simp [f]
  have hnat := hs.tsum_eq_zero_add
  rw [hz, zero_add] at hnat
  change (∑' n : ℤ, g n) = _
  rw [tsum_of_nat_of_neg_add_one hgpos hgneg, hpos, hneg, ← hnat]
  have ht := scalarFourierDecay_nat_tsum_tail_eq hL hd N
  change (∑' n : ℕ, f n) = _ at ht
  rw [ht]
  ring

/-- The explicit signed scalar tail estimate used for derivative errors. -/
theorem originalDetectorScalarFourierDecay_signed_tsum_tail_le_exp {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (N : ℕ)
    (hu : L ≤ Real.sqrt ((N : ℝ) / L)) :
    (∑' n : ℤ, if N < n.natAbs then
      originalDetectorScalarFourierDecay L d |(n : ℝ)| else 0) ≤
      40 / d ^ 3 * Real.exp (-(d / 2) * Real.sqrt ((N : ℝ) / L)) := by
  rw [originalDetectorScalarFourierDecay_signed_tsum_tail_eq hL hd N]
  have hb := mul_le_mul_of_nonneg_left
    (originalDetectorScalarFourierDecay_tsum_tail_le_exp hL hd N hu) (by norm_num : (0 : ℝ) ≤ 2)
  convert! hb using 1
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_integrableOn
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_integral_Ioi
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_summable
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_tsum_tail_le
#print axioms Zeta23.CCM.originalDetectorScalarWeightedDecay_le
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_tsum_tail_le_exp
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_signed_tail_summable
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_signed_tsum_tail_eq
#print axioms Zeta23.CCM.originalDetectorScalarFourierDecay_signed_tsum_tail_le_exp
