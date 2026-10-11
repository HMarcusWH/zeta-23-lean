import Zeta23.CCM.CanonicalPrimeRemainder
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

noncomputable section

/-!
# M55 and M38: weighted Chebyshev partial summation and finite remainder extrema

For the classical weighted remainder already used by the canonical prime
channel (`CanonicalPrimeRemainder`),

```text
R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x,
```

finite Abel summation gives, for every real `x ≥ 1`,

```text
ψ(x) - x = 1 + √x R(x) - (1/2) ∫₁ˣ R(t)/√t dt.          (96.1)
```

The floor convention is the one of `Chebyshev.psi` and of the weighted sum
(`n ≤ ⌊x⌋`), so the identity holds at integer `x` with the right-continuous
values.  At `x = 1` both sides are `-1`.

**M38 (Step 75).**  `R` decreases strictly inside each cell `[m, m+1)` and jumps
up by `Λ(m)/√m ≥ 0` at integers, so its extrema on `[1, X]` are finite:

```text
sup_{1 ≤ x ≤ X} R(x) = max_{1 ≤ m ≤ ⌊X⌋} R(m)                      (attained),
inf_{1 ≤ x ≤ X} R(x) = min_{1 ≤ m ≤ ⌊X⌋} (W_m - 2√(min(m+1, X)))   (IsGLB),
```

with `W_m = ∑_{n ≤ m} Λ(n)/√n`.  The infimum may be only a left limit before a
jump; it is stated as a greatest lower bound, not as an attained minimum.

The transfer bound `abs_psi_sub_self_sub_one_le` makes the claim firewall
explicit: a bound `|R| ≤ M` on `[1, x]` gives `|ψ(x) - x - 1| ≤ 2M√x`.  A
bound `R(x) = O_ε(x^ε)` for every `ε > 0` is therefore RH-strength, and nothing
in this project may assume it.  Everything here is unconditional finite
arithmetic plus one integral; no sign or size of `R` is proved or used.
-/

namespace Zeta23.CCM

open MeasureTheory Set Finset
open scoped ArithmeticFunction

/-- The weighted coefficients `c n = Λ(n)/√n`. -/
def weightedVonMangoldtSqrtCoeff (n : ℕ) : ℝ := Λ n / Real.sqrt n

theorem weightedVonMangoldtSqrtSum_eq_sum_Icc_zero (x : ℝ) :
    weightedVonMangoldtSqrtSum x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, weightedVonMangoldtSqrtCoeff n := by
  unfold weightedVonMangoldtSqrtSum weightedVonMangoldtSqrtCoeff
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp

theorem weightedVonMangoldtSqrtSum_one : weightedVonMangoldtSqrtSum 1 = 0 := by
  unfold weightedVonMangoldtSqrtSum
  simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- Sanity value `R(1) = -2`. -/
theorem weightedVonMangoldtSqrtRemainder_one : weightedVonMangoldtSqrtRemainder 1 = -2 := by
  unfold weightedVonMangoldtSqrtRemainder
  rw [weightedVonMangoldtSqrtSum_one, Real.sqrt_one]
  ring

theorem deriv_sqrt_of_pos {t : ℝ} (ht : 0 < t) :
    deriv Real.sqrt t = 1 / (2 * Real.sqrt t) :=
  (Real.hasDerivAt_sqrt ht.ne').deriv

theorem integrableOn_deriv_sqrt_Icc_one (x : ℝ) :
    IntegrableOn (deriv Real.sqrt) (Icc 1 x) := by
  have hc : ContinuousOn (fun t : ℝ => 1 / (2 * Real.sqrt t)) (Icc 1 x) := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_const.mul Real.continuous_sqrt).continuousOn
    · intro t ht
      have : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos ht.1)
      positivity
  refine (hc.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
  exact (deriv_sqrt_of_pos (lt_of_lt_of_le one_pos ht.1)).symm

/-- Abel summation in the raw form: for `x ≥ 1`,
`ψ(x) = √x A(x) - ∫_{(1,x]} A(t)/(2√t) dt`, with `A(x) = ∑_{n ≤ x} Λ(n)/√n`. -/
theorem psi_eq_sqrt_mul_sum_sub_integral {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x =
      Real.sqrt x * weightedVonMangoldtSqrtSum x -
        ∫ t in Ioc 1 x, 1 / (2 * Real.sqrt t) * weightedVonMangoldtSqrtSum t := by
  have habel := sum_mul_eq_sub_sub_integral_mul weightedVonMangoldtSqrtCoeff
    (f := Real.sqrt) zero_le_one hx
    (fun t ht => (Real.hasDerivAt_sqrt (lt_of_lt_of_le one_pos ht.1).ne').differentiableAt)
    (integrableOn_deriv_sqrt_Icc_one x)
  have hlhs : ∑ k ∈ Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊, Real.sqrt k * weightedVonMangoldtSqrtCoeff k =
      Chebyshev.psi x := by
    rw [Chebyshev.psi, Nat.floor_one]
    have h1 : ∑ k ∈ Ioc 1 ⌊x⌋₊, Real.sqrt k * weightedVonMangoldtSqrtCoeff k =
        ∑ k ∈ Ioc 1 ⌊x⌋₊, Λ k := by
      refine sum_congr rfl fun k hk => ?_
      have hk1 : 1 < k := (Finset.mem_Ioc.mp hk).1
      have hk0 : (0 : ℝ) < Real.sqrt k :=
        Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
      unfold weightedVonMangoldtSqrtCoeff
      field_simp
    rw [h1]
    apply sum_subset (Ioc_subset_Ioc_left zero_le_one)
    intro k hk hk'
    have : k = 1 := by
      simp only [Finset.mem_Ioc] at hk hk'
      omega
    subst this
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  rw [hlhs] at habel
  rw [habel, ← weightedVonMangoldtSqrtSum_eq_sum_Icc_zero,
    ← weightedVonMangoldtSqrtSum_eq_sum_Icc_zero, weightedVonMangoldtSqrtSum_one, mul_zero,
    sub_zero]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [deriv_sqrt_of_pos (lt_trans one_pos ht.1), ← weightedVonMangoldtSqrtSum_eq_sum_Icc_zero]

theorem continuousOn_const_div_sqrt_Icc_one (M x : ℝ) :
    ContinuousOn (fun t : ℝ => M / Real.sqrt t) (Icc 1 x) := by
  apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
  intro t ht
  exact (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos ht.1)).ne'

theorem continuousOn_one_div_sqrt_Icc_one (x : ℝ) :
    ContinuousOn (fun t : ℝ => 1 / Real.sqrt t) (Icc 1 x) :=
  continuousOn_const_div_sqrt_Icc_one 1 x

theorem integrableOn_one_div_sqrt_mul_weightedSum (x : ℝ) :
    IntegrableOn (fun t => 1 / Real.sqrt t * weightedVonMangoldtSqrtSum t) (Icc 1 x) := by
  have h := integrableOn_mul_sum_Icc weightedVonMangoldtSqrtCoeff (m := 0) zero_le_one
    (continuousOn_one_div_sqrt_Icc_one x).integrableOn_Icc
  refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
  rw [weightedVonMangoldtSqrtSum_eq_sum_Icc_zero]

theorem integrableOn_weightedRemainder_div_sqrt (x : ℝ) :
    IntegrableOn (fun t => weightedVonMangoldtSqrtRemainder t / Real.sqrt t) (Icc 1 x) := by
  have h := (integrableOn_one_div_sqrt_mul_weightedSum x).sub
    (continuousOn_const (c := (2 : ℝ))).integrableOn_Icc
  refine h.congr_fun (fun t ht => ?_) measurableSet_Icc
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos ht.1)
  unfold weightedVonMangoldtSqrtRemainder
  simp only [Pi.sub_apply]
  field_simp

/-- **M55, (96.1).**  Exact weighted Chebyshev partial summation: for `x ≥ 1`,
`ψ(x) - x = 1 + √x R(x) - (1/2) ∫₁ˣ R(t)/√t dt`. -/
theorem psi_sub_self_eq_weightedRemainder {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - x =
      1 + Real.sqrt x * weightedVonMangoldtSqrtRemainder x -
        (1 / 2) * ∫ t in (1 : ℝ)..x, weightedVonMangoldtSqrtRemainder t / Real.sqrt t := by
  rw [psi_eq_sqrt_mul_sum_sub_integral hx, ← intervalIntegral.integral_of_le hx]
  have hR : IntervalIntegrable (fun t => weightedVonMangoldtSqrtRemainder t / Real.sqrt t)
      volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (integrableOn_weightedRemainder_div_sqrt x)
  have hcongr : ∫ t in (1 : ℝ)..x, 1 / (2 * Real.sqrt t) * weightedVonMangoldtSqrtSum t =
      ∫ t in (1 : ℝ)..x,
        ((1 / 2) * (weightedVonMangoldtSqrtRemainder t / Real.sqrt t) + 1) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos ht.1)
    unfold weightedVonMangoldtSqrtRemainder
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_add (hR.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  unfold weightedVonMangoldtSqrtRemainder
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  linear_combination (2 : ℝ) * hsq

theorem integral_const_div_sqrt {x : ℝ} (hx : 1 ≤ x) (M : ℝ) :
    ∫ t in (1 : ℝ)..x, M / Real.sqrt t = 2 * M * Real.sqrt x - 2 * M := by
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t => 2 * M * Real.sqrt t) (M / Real.sqrt t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos ht.1)
    have h := (Real.hasDerivAt_sqrt (lt_of_lt_of_le one_pos ht.1).ne').const_mul (2 * M)
    refine h.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun t => M / Real.sqrt t) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (continuousOn_const_div_sqrt_Icc_one M x).integrableOn_Icc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.sqrt_one, mul_one]

/-- **Claim firewall, made quantitative.**  A bound `|R| ≤ M` on `[1, x]` gives
`|ψ(x) - x - 1| ≤ 2M√x`.  So `R(x) = O_ε(x^ε)` for every `ε > 0` would give
`ψ(x) = x + O_ε(x^{1/2+ε})`, which is RH-strength; it is never assumed. -/
theorem abs_psi_sub_self_sub_one_le {x M : ℝ} (hx : 1 ≤ x)
    (hM : ∀ t ∈ Icc 1 x, |weightedVonMangoldtSqrtRemainder t| ≤ M) :
    |Chebyshev.psi x - x - 1| ≤ 2 * M * Real.sqrt x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 ⟨le_rfl, hx⟩)
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  have hI : |∫ t in (1 : ℝ)..x, weightedVonMangoldtSqrtRemainder t / Real.sqrt t| ≤
      2 * M * Real.sqrt x - 2 * M := by
    rw [← integral_const_div_sqrt hx M, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hx
      (Filter.Eventually.of_forall fun t ht => ?_) ?_
    · have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_trans one_pos ht.1)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right (hM t ⟨ht.1.le, ht.2⟩) hs.le
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
        (continuousOn_const_div_sqrt_Icc_one M x).integrableOn_Icc
  have hRx : |weightedVonMangoldtSqrtRemainder x| ≤ M := hM x ⟨hx, le_rfl⟩
  rw [psi_sub_self_eq_weightedRemainder hx]
  have hsplit : 1 + Real.sqrt x * weightedVonMangoldtSqrtRemainder x -
        (1 / 2) * (∫ t in (1 : ℝ)..x, weightedVonMangoldtSqrtRemainder t / Real.sqrt t) - 1 =
      Real.sqrt x * weightedVonMangoldtSqrtRemainder x +
        (-(1 / 2)) * (∫ t in (1 : ℝ)..x, weightedVonMangoldtSqrtRemainder t / Real.sqrt t) := by
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (lt_of_lt_of_le one_pos hsx),
    show |(-(1 / 2) : ℝ)| = 1 / 2 by norm_num]
  have h1 : Real.sqrt x * |weightedVonMangoldtSqrtRemainder x| ≤ Real.sqrt x * M :=
    mul_le_mul_of_nonneg_left hRx (by linarith)
  nlinarith

/-! ## M38: exact finite extrema of the weighted remainder (Step 75) -/

theorem weightedVonMangoldtSqrtSum_floor (x : ℝ) :
    weightedVonMangoldtSqrtSum (⌊x⌋₊ : ℝ) = weightedVonMangoldtSqrtSum x := by
  unfold weightedVonMangoldtSqrtSum
  rw [Nat.floor_natCast]

theorem one_le_floor_of_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ ⌊x⌋₊ :=
  Nat.le_floor (by exact_mod_cast hx)

theorem Icc_one_floor_nonempty {X : ℝ} (hX : 1 ≤ X) : (Finset.Icc 1 ⌊X⌋₊).Nonempty :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, one_le_floor_of_one_le hX⟩⟩

/-- **M38, supremum.**  On `[1, X]` the weighted remainder attains its supremum
at an integer: `sup_{1 ≤ x ≤ X} R(x) = max_{1 ≤ m ≤ ⌊X⌋} R(m)`. -/
theorem isGreatest_weightedRemainder {X : ℝ} (hX : 1 ≤ X) :
    IsGreatest (weightedVonMangoldtSqrtRemainder '' Icc 1 X)
      ((Finset.Icc 1 ⌊X⌋₊).sup' (Icc_one_floor_nonempty hX)
        fun m => weightedVonMangoldtSqrtRemainder (m : ℝ)) := by
  constructor
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup' (Icc_one_floor_nonempty hX)
      fun m => weightedVonMangoldtSqrtRemainder (m : ℝ)
    rw [Finset.mem_Icc] at hm
    refine ⟨m, ⟨by exact_mod_cast hm.1, ?_⟩, hmax.symm⟩
    exact (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by linarith))
  · rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hm : ⌊x⌋₊ ∈ Finset.Icc 1 ⌊X⌋₊ :=
      Finset.mem_Icc.mpr ⟨one_le_floor_of_one_le hx.1, Nat.floor_le_floor hx.2⟩
    refine le_trans ?_
      (Finset.le_sup' (fun m : ℕ => weightedVonMangoldtSqrtRemainder (m : ℝ)) hm)
    unfold weightedVonMangoldtSqrtRemainder
    rw [weightedVonMangoldtSqrtSum_floor]
    have := Real.sqrt_le_sqrt (Nat.floor_le hx0)
    linarith

/-- **M38, infimum.**  On `[1, X]` the infimum of the weighted remainder is the
finite minimum `min_{1 ≤ m ≤ ⌊X⌋} (W_m - 2√(min(m+1, X)))`.  It may be only a
left limit before an upward jump, not a value of the right-continuous staircase. -/
theorem isGLB_weightedRemainder {X : ℝ} (hX : 1 ≤ X) :
    IsGLB (weightedVonMangoldtSqrtRemainder '' Icc 1 X)
      ((Finset.Icc 1 ⌊X⌋₊).inf' (Icc_one_floor_nonempty hX)
        fun m => weightedVonMangoldtSqrtSum (m : ℝ) - 2 * Real.sqrt (min ((m : ℝ) + 1) X)) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hm : ⌊x⌋₊ ∈ Finset.Icc 1 ⌊X⌋₊ :=
      Finset.mem_Icc.mpr ⟨one_le_floor_of_one_le hx.1, Nat.floor_le_floor hx.2⟩
    refine le_trans (Finset.inf'_le _ hm) ?_
    unfold weightedVonMangoldtSqrtRemainder
    rw [weightedVonMangoldtSqrtSum_floor]
    have hle : x ≤ min ((⌊x⌋₊ : ℝ) + 1) X := le_min (Nat.lt_floor_add_one x).le hx.2
    have := Real.sqrt_le_sqrt hle
    linarith
  · intro b hb
    refine Finset.le_inf' _ _ fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmX : (m : ℝ) ≤ X := (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by linarith))
    rcases lt_or_ge X ((m : ℝ) + 1) with hlt | hge
    · -- the cell of `m` is cut off by `X`: the bound is attained at `x = X`
      have hfl : ⌊X⌋₊ = m := (Nat.floor_eq_iff (by linarith)).mpr ⟨hmX, hlt⟩
      have hRX := hb ⟨X, ⟨hX, le_rfl⟩, rfl⟩
      rw [min_eq_right hlt.le]
      unfold weightedVonMangoldtSqrtRemainder at hRX
      rw [← weightedVonMangoldtSqrtSum_floor X, hfl] at hRX
      exact hRX
    · -- full cell: the bound is the left limit at `m + 1`
      rw [min_eq_left hge]
      have hT : Filter.Tendsto
          (fun x : ℝ => weightedVonMangoldtSqrtSum (m : ℝ) - 2 * Real.sqrt x)
          (nhdsWithin ((m : ℝ) + 1) (Iio ((m : ℝ) + 1)))
          (nhds (weightedVonMangoldtSqrtSum (m : ℝ) - 2 * Real.sqrt ((m : ℝ) + 1))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        exact ((continuous_const.sub (continuous_const.mul Real.continuous_sqrt)).tendsto _)
      refine ge_of_tendsto hT ?_
      filter_upwards [Ioo_mem_nhdsLT (show (m : ℝ) < (m : ℝ) + 1 by linarith)] with x hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hfl : ⌊x⌋₊ = m := (Nat.floor_eq_iff hx0).mpr ⟨hx.1.le, hx.2⟩
      have hR := hb ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
      unfold weightedVonMangoldtSqrtRemainder at hR
      rw [← weightedVonMangoldtSqrtSum_floor x, hfl] at hR
      exact hR

end Zeta23.CCM

#print axioms Zeta23.CCM.weightedVonMangoldtSqrtRemainder_one
#print axioms Zeta23.CCM.psi_eq_sqrt_mul_sum_sub_integral
#print axioms Zeta23.CCM.psi_sub_self_eq_weightedRemainder
#print axioms Zeta23.CCM.abs_psi_sub_self_sub_one_le
#print axioms Zeta23.CCM.isGreatest_weightedRemainder
#print axioms Zeta23.CCM.isGLB_weightedRemainder
