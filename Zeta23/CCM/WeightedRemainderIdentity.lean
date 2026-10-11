import Zeta23.CCM.CanonicalRegularizedEnergyIdentity
import Zeta23.CCM.CanonicalWeightedChebyshevAbel
import Zeta23.CCM.CanonicalPrimeFreeF04
import Zeta23.CCM.FirstCrossingProductionRemainder
import Zeta23.CCM.FirstCrossingProductionRemainderAuthority
import Zeta23.CCM.CanonicalLocalBirdfishie

noncomputable section

/-!
# M09 and M03: weighted remainder identity, contact-weighted balance, fixed staircase

For a `C¹` test `h` with `h(0) = h(L) = 0`, the zero-endpoint production value
`A_L[h] = dictionaryCompletePhysicalRHS h L` satisfies

```text
A_L[h] = ∫₀ᴸ R(e^t) h'(t) dt + ∫₀ᴸ (e^{-t/2} - ρ(t)) h(t) dt,
R(x)   = ∑_{n ≤ x} Λ(n)/√n - 2√x,          ρ(t) = e^{t/2}/(e^t - e^{-t}).
```

* The prime channel is a finite summation by parts: on the aperture the
  staircase `canonicalPrimeCumulativeWeight` is `S(e^t)`
  (`canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum`), and each
  step is one fundamental-theorem rewrite using `h(L) = 0`.
* The pole main term `2√(e^t) = 2e^{t/2}` is integrated by parts once; both
  boundary terms vanish because `h(0) = h(L) = 0`.
* `h(0) = 0` also removes the scalar `wCorrection` term of the regularized
  value (M05).  For a nonzero endpoint that scalar correction stays and this
  identity does not apply as stated.

**Contact-weighted form.**  At a stationary generated strict-even contact
(`GeneratedStrictEvenContact`: simple even kernel, positive odd complement,
normalized `z`, stationary response `w` with `A w = -A' z`), the complete second
physical value is `2C` with `C = ⟪A w, w⟫ ≥ 0`
(`GeneratedStrictEvenContact.secondPhysicalValue_eq_two_mul_responseCost`, using
F04 at every `L > 0`).  Since the second-derivative test is
`-(2π)² t²/L⁴ · e_{Dz}(1 - t/L)` on `[0, L]`,

```text
A_{L*}[t² e_{Dz}(1 - t/L*)] = -2 L*⁴ C/(2π)² ≤ 0,
```

and substituting `h(t) = t² e_{Dz}(1 - t/L*)` gives the exact contact-weighted
von-Mangoldt remainder balance `GeneratedStrictEvenContact.weightedRemainder_balance`.

**M03 fixed staircase.**  On the aperture the canonical pole-prime discrepancy
is `D(t) = 4 sinh(t/2) - B(t)` with `B(t) = ∑_{n ≤ e^t} Λ(n)/√n`, and the
pole-minus-prime energy is `(1/L) ∫₀ᴸ D(t) e'_u(1 - t/L) dt`.

Claim firewall: the balance is a necessary condition satisfied by every such
contact, not a contradiction.  No sign or size of `R` is used or claimed, no
universal weighted positivity is inferred, and nothing here concerns zeta
zeros or RH.
-/

namespace Zeta23.CCM

open MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Interval

/-- A step times an interval-integrable function is interval integrable. -/
theorem intervalIntegrable_ite_le_mul {a L : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L) (c : ℂ)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 L) :
    IntervalIntegrable (fun t => (if a ≤ t then c else 0) * f t) volume 0 L := by
  have hfa : IntervalIntegrable f volume a L := hf.mono_set (by
    rw [uIcc_of_le haL, uIcc_of_le (ha0.trans haL)]; exact Icc_subset_Icc ha0 le_rfl)
  have hleft : IntervalIntegrable (fun t => (if a ≤ t then c else 0) * f t) volume 0 a := by
    refine (continuous_const.intervalIntegrable (0 : ℝ) a (μ := volume)
      (u := fun _ : ℝ => (0 : ℂ))).congr_uIoo ?_
    intro t ht
    rw [uIoo_of_le ha0] at ht
    simp [not_le.mpr ht.2]
  have hright : IntervalIntegrable (fun t => (if a ≤ t then c else 0) * f t) volume a L := by
    refine (hfa.const_mul c).congr_uIoo ?_
    intro t ht
    rw [uIoo_of_le haL] at ht
    simp [le_of_lt ht.1]
  exact hleft.trans hright

/-- Step-function integral: `∫₀ᴸ 1_{a ≤ t} c f(t) dt = c ∫ₐᴸ f`. -/
theorem intervalIntegral_ite_le_mul {a L : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L) (c : ℂ)
    {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 L) :
    (∫ t in (0 : ℝ)..L, (if a ≤ t then c else 0) * f t) = c * ∫ t in a..L, f t := by
  have hfa : IntervalIntegrable f volume a L := hf.mono_set (by
    rw [uIcc_of_le haL, uIcc_of_le (ha0.trans haL)]; exact Icc_subset_Icc ha0 le_rfl)
  have hall := intervalIntegrable_ite_le_mul ha0 haL c hf
  have hleft : IntervalIntegrable (fun t => (if a ≤ t then c else 0) * f t) volume 0 a :=
    hall.mono_set (by rw [uIcc_of_le ha0, uIcc_of_le (ha0.trans haL)]
                      exact Icc_subset_Icc le_rfl haL)
  have hright : IntervalIntegrable (fun t => (if a ≤ t then c else 0) * f t) volume a L :=
    hall.mono_set (by rw [uIcc_of_le haL, uIcc_of_le (ha0.trans haL)]
                      exact Icc_subset_Icc ha0 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hz : (∫ t in (0 : ℝ)..a, (if a ≤ t then c else 0) * f t) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0 : ℂ)) ?_]
    · simp
    intro t ht
    rw [uIoo_of_le ha0] at ht
    simp [not_le.mpr ht.2]
  have hr : (∫ t in a..L, (if a ≤ t then c else 0) * f t) = ∫ t in a..L, c * f t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le haL] at ht
    simp [le_of_lt ht.1]
  rw [hz, hr, zero_add, intervalIntegral.integral_const_mul]

private theorem log_mem_aperture_m09 {L : ℝ} {q : ℕ} (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    0 ≤ Real.log q ∧ Real.log q ≤ L := by
  have hqmem := Finset.mem_Icc.mp hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1
  have hqexp : (q : ℝ) ≤ Real.exp L := (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
  exact ⟨Real.log_natCast_nonneg q, by rw [← Real.log_exp L]; exact Real.log_le_log hqpos hqexp⟩

/-- On the aperture the weighted staircase `S(e^t)` is a finite sum of steps. -/
theorem weightedSum_exp_mul_eq_sum_ite {L t : ℝ} (htL : t ≤ L) (y : ℂ) :
    (weightedVonMangoldtSqrtSum (Real.exp t) : ℂ) * y =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (if Real.log q ≤ t then primeSourceWeight q else 0) * y := by
  rw [← canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum htL, ← Finset.sum_mul]
  congr 1
  unfold canonicalPrimeCumulativeWeight primeSourceWeight
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

/-- `S(e^t) h'(t)` is interval integrable on the aperture. -/
theorem intervalIntegrable_weightedSum_exp_mul {h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hh' : IntervalIntegrable h' volume 0 L) :
    IntervalIntegrable (fun t => (weightedVonMangoldtSqrtSum (Real.exp t) : ℂ) * h' t)
      volume 0 L := by
  have hsum : IntervalIntegrable (fun t => ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (if Real.log q ≤ t then primeSourceWeight q else 0) * h' t) volume 0 L := by
    have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := L) (Finset.Icc 2 ⌊Real.exp L⌋₊)
      (f := fun q t => (if Real.log q ≤ t then primeSourceWeight q else 0) * h' t)
      fun q hq => by
        obtain ⟨h0, hl⟩ := log_mem_aperture_m09 hq
        exact intervalIntegrable_ite_le_mul h0 hl _ hh'
    simpa only [Finset.sum_fn] using this
  refine hsum.congr_uIoo fun t ht => ?_
  rw [uIoo_of_le hL] at ht
  exact (weightedSum_exp_mul_eq_sum_ite ht.2.le (h' t)).symm

/-- **Prime channel by parts.**  For `h(L) = 0`,
`∑_{2 ≤ q ≤ e^L} Λ(q)/√q h(log q) = -∫₀ᴸ S(e^t) h'(t) dt`, with
`S(x) = ∑_{n ≤ x} Λ(n)/√n`. -/
theorem sum_primeSourceWeight_eq_neg_integral_weightedSum
    {h h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume 0 L) (hLz : h L = 0) :
    ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * h (Real.log q) =
      -∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtSum (Real.exp t) : ℂ) * h' t := by
  rw [intervalIntegral.integral_congr (g := fun t => ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (if Real.log q ≤ t then primeSourceWeight q else 0) * h' t) fun t ht => by
        rw [uIcc_of_le hL] at ht
        exact weightedSum_exp_mul_eq_sum_ite ht.2 (h' t),
    intervalIntegral.integral_finsetSum fun q hq => by
      obtain ⟨h0, hl⟩ := log_mem_aperture_m09 hq
      exact intervalIntegrable_ite_le_mul h0 hl _ hh',
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨h0, hl⟩ := log_mem_aperture_m09 hq
  rw [intervalIntegral_ite_le_mul h0 hl _ hh']
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := h) (f' := h') (a := Real.log q) (b := L)
    (fun t ht => hderiv t (by rw [uIcc_of_le hl] at ht; exact ⟨h0.trans ht.1, ht.2⟩))
    (hh'.mono_set (by rw [uIcc_of_le hl, uIcc_of_le hL]; exact Icc_subset_Icc h0 le_rfl))
  rw [hftc, hLz]
  ring

/-- **Pole main term by parts.**  For `h(0) = h(L) = 0`,
`∫₀ᴸ 2 e^{t/2} h'(t) dt = -∫₀ᴸ e^{t/2} h(t) dt`. -/
theorem integral_two_exp_half_mul_deriv
    {h h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume 0 L) (h0 : h 0 = 0) (hLz : h L = 0) :
    (∫ t in (0 : ℝ)..L, ((2 * Real.exp (t / 2) : ℝ) : ℂ) * h' t) =
      -∫ t in (0 : ℝ)..L, ((Real.exp (t / 2) : ℝ) : ℂ) * h t := by
  have hu : ∀ t ∈ uIcc 0 L, HasDerivAt (fun s : ℝ => ((2 * Real.exp (s / 2) : ℝ) : ℂ))
      ((Real.exp (t / 2) : ℝ) : ℂ) t := by
    intro t _
    have hr : HasDerivAt (fun s : ℝ => 2 * Real.exp (s / 2)) (Real.exp (t / 2)) t := by
      have := (((hasDerivAt_id t).div_const 2).exp).const_mul 2
      refine this.congr_deriv ?_
      simp only [id_eq]
      ring
    exact hr.ofReal_comp
  have hv : ∀ t ∈ uIcc 0 L, HasDerivAt h (h' t) t := fun t ht =>
    hderiv t (by rwa [uIcc_of_le hL] at ht)
  have hu' : IntervalIntegrable (fun t : ℝ => ((Real.exp (t / 2) : ℝ) : ℂ)) volume 0 L :=
    (by fun_prop : Continuous fun t : ℝ => ((Real.exp (t / 2) : ℝ) : ℂ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hh', h0, hLz]
  simp

private theorem sqrt_exp_eq_exp_half_m09 (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  have h : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- **M09, weighted remainder identity.**  For an endpoint-zero test
`h(0) = h(L) = 0` with derivative `h'` integrable on `[0, L]` and `h ρ`
integrable, the regularized complete physical value is

`A_L[h] = ∫₀ᴸ R(e^t) h'(t) dt + ∫₀ᴸ (e^{-t/2} - ρ(t)) h(t) dt`,

with `R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x`.  The endpoint `h(0) = 0` removes the
scalar `wCorrection` term; for a nonzero endpoint the scalar correction of
M05 stays. -/
theorem regularizedCompletePhysicalRHS_eq_weightedRemainder
    {h h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume 0 L) (h0 : h 0 = 0) (hLz : h L = 0)
    (hρ : IntervalIntegrable (fun t => h t * (archDensity t : ℂ)) volume 0 L) :
    regularizedCompletePhysicalRHS h L =
      (∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtRemainder (Real.exp t) : ℂ) * h' t) +
        ∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) - archDensity t : ℝ) : ℂ) * h t := by
  have hcont : ContinuousOn h (uIcc 0 L) := by
    rw [uIcc_of_le hL]
    exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hEm : IntervalIntegrable (fun t => ((Real.exp (-t / 2) : ℝ) : ℂ) * h t) volume 0 L :=
    ((by fun_prop : Continuous fun t : ℝ => ((Real.exp (-t / 2) : ℝ) : ℂ)).continuousOn.mul
      hcont).intervalIntegrable
  have hEp : IntervalIntegrable (fun t => ((Real.exp (t / 2) : ℝ) : ℂ) * h t) volume 0 L :=
    ((by fun_prop : Continuous fun t : ℝ => ((Real.exp (t / 2) : ℝ) : ℂ)).continuousOn.mul
      hcont).intervalIntegrable
  have hS := intervalIntegrable_weightedSum_exp_mul hL hh'
  have hP : IntervalIntegrable (fun t => ((2 * Real.exp (t / 2) : ℝ) : ℂ) * h' t) volume 0 L :=
    hh'.continuousOn_mul (by fun_prop : Continuous fun t : ℝ =>
      ((2 * Real.exp (t / 2) : ℝ) : ℂ)).continuousOn
  -- remainder channel
  have hR : (∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtRemainder (Real.exp t) : ℂ) * h' t) =
      (∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtSum (Real.exp t) : ℂ) * h' t) -
        ∫ t in (0 : ℝ)..L, ((2 * Real.exp (t / 2) : ℝ) : ℂ) * h' t := by
    rw [← intervalIntegral.integral_sub hS hP]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [weightedVonMangoldtSqrtRemainder, sqrt_exp_eq_exp_half_m09]
    push_cast
    ring
  -- pole channel
  have hW : (∫ t in (0 : ℝ)..L, h t * (completeSourcePoleWeight t : ℂ)) =
      (∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) : ℝ) : ℂ) * h t) +
        ∫ t in (0 : ℝ)..L, ((Real.exp (t / 2) : ℝ) : ℂ) * h t := by
    rw [← intervalIntegral.integral_add hEm hEp]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [completeSourcePoleWeight]
    push_cast
    ring
  -- archimedean channel
  have hA : (∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) - archDensity t : ℝ) : ℂ) * h t) =
      (∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) : ℝ) : ℂ) * h t) -
        ∫ t in (0 : ℝ)..L, h t * (archDensity t : ℂ) := by
    rw [← intervalIntegral.integral_sub hEm hρ]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast
    ring
  have hρ' : (∫ t in (0 : ℝ)..L, (h t - h 0 * (Real.exp (-t / 2) : ℂ)) * (archDensity t : ℂ)) =
      ∫ t in (0 : ℝ)..L, h t * (archDensity t : ℂ) := by
    simp [h0]
  have hprime := sum_primeSourceWeight_eq_neg_integral_weightedSum hL hderiv hh' hLz
  have hpole := integral_two_exp_half_mul_deriv hL hderiv hh' h0 hLz
  unfold regularizedCompletePhysicalRHS
  rw [hW, hρ', h0, hprime, hR, hA, hpole]
  ring

/-- A `C¹` endpoint-zero test has `h ρ` integrable on the aperture: `|h(t)| ≤ M t`
and `t ρ(t)` is bounded. -/
theorem intervalIntegrable_mul_archDensity_of_hasDerivAt
    {h h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt h (h' t) t)
    (hcont' : ContinuousOn h' (Icc 0 L)) (h0 : h 0 = 0) :
    IntervalIntegrable (fun t => h t * (archDensity t : ℂ)) volume 0 L := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hcont'
  obtain ⟨CR, hCR, hCRb⟩ := exists_abs_bound_Icc continuous_regularizedArchScale 0 L
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hlin : ∀ t ∈ Icc (0 : ℝ) L, ‖h t‖ ≤ max M 0 * t := by
    intro t ht
    have := (convex_Icc (0 : ℝ) L).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := h) (f' := h') (fun y hy => (hderiv y hy).hasDerivWithinAt)
      (fun y hy => (hM y hy).trans (le_max_left M 0)) ⟨le_rfl, hL⟩ ht
    rwa [h0, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
  have hcont : ContinuousOn h (Icc 0 L) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  refine (intervalIntegrable_const (c := max M 0 * CR)).mono_fun' ?_ ?_
  · rw [uIoc_of_le hL]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (hcont.mono Ioc_subset_Icc_self).mul ?_
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_archDensity.mono fun t ht => ht.1))
  · rw [uIoc_of_le hL]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have hρpos : 0 < archDensity t := archDensity_pos_of_pos ht.1
    have hR := abs_mul_archDensity_le (T := L) hCRb (t := t) ht
    rw [abs_mul, abs_of_pos ht.1, abs_of_pos hρpos] at hR
    show ‖h t * (archDensity t : ℂ)‖ ≤ max M 0 * CR
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    calc ‖h t‖ * archDensity t ≤ max M 0 * t * archDensity t :=
          mul_le_mul_of_nonneg_right (hlin t ⟨ht.1.le, ht.2⟩) hρpos.le
      _ = max M 0 * (t * archDensity t) := by ring
      _ ≤ max M 0 * CR := mul_le_mul_of_nonneg_left hR hM0

/-- **M09, `C¹` form.**  For a continuously differentiable endpoint-zero test the
weighted remainder identity holds with no separate integrability premise. -/
theorem regularizedCompletePhysicalRHS_eq_weightedRemainder_of_continuousOn
    {h h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt h (h' t) t)
    (hcont' : ContinuousOn h' (Icc 0 L)) (h0 : h 0 = 0) (hLz : h L = 0) :
    regularizedCompletePhysicalRHS h L =
      (∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtRemainder (Real.exp t) : ℂ) * h' t) +
        ∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) - archDensity t : ℝ) : ℂ) * h t :=
  regularizedCompletePhysicalRHS_eq_weightedRemainder hL hderiv
    (by rw [← uIcc_of_le hL] at hcont'; exact hcont'.intervalIntegrable) h0 hLz
    (intervalIntegrable_mul_archDensity_of_hasDerivAt hL hderiv hcont' h0)

/-- At an endpoint-zero test the regularized value is the zero-endpoint
production value `A_L[h]`. -/
theorem regularizedCompletePhysicalRHS_eq_dictionary_of_zero
    {h : ℝ → ℂ} (L : ℝ) (h0 : h 0 = 0) :
    regularizedCompletePhysicalRHS h L = dictionaryCompletePhysicalRHS h L := by
  simp [regularizedCompletePhysicalRHS, dictionaryCompletePhysicalRHS, h0]

/-- **M09 on the production functional.**  For a `C¹` test with
`h(0) = h(L) = 0`,
`A_L[h] = ∫₀ᴸ R(e^t) h'(t) dt + ∫₀ᴸ (e^{-t/2} - ρ(t)) h(t) dt`. -/
theorem productionArithmeticComplexValue_eq_weightedRemainder
    {h h' : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt h (h' t) t)
    (hcont' : ContinuousOn h' (Icc 0 L)) (h0 : h 0 = 0) (hLz : h L = 0) :
    productionArithmeticComplexValue L h =
      (∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtRemainder (Real.exp t) : ℂ) * h' t) +
        ∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) - archDensity t : ℝ) : ℂ) * h t := by
  rw [productionArithmeticComplexValue, ← regularizedCompletePhysicalRHS_eq_dictionary_of_zero L h0]
  exact regularizedCompletePhysicalRHS_eq_weightedRemainder_of_continuousOn hL hderiv hcont' h0 hLz

/-- **M09, real production form.**  For a real `C¹` test with
`f(0) = f(L) = 0`,
`productionArithmeticRealValue L f = ∫₀ᴸ R(e^t) f'(t) dt + ∫₀ᴸ (e^{-t/2} - ρ(t)) f(t) dt`. -/
theorem productionArithmeticRealValue_eq_weightedRemainder
    {f f' : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc 0 L, HasDerivAt f (f' t) t)
    (hcont' : ContinuousOn f' (Icc 0 L)) (h0 : f 0 = 0) (hLz : f L = 0) :
    productionArithmeticRealValue L f =
      (∫ t in (0 : ℝ)..L, weightedVonMangoldtSqrtRemainder (Real.exp t) * f' t) +
        ∫ t in (0 : ℝ)..L, (Real.exp (-t / 2) - archDensity t) * f t := by
  have hc := productionArithmeticComplexValue_eq_weightedRemainder (h := fun t => (f t : ℂ))
    (h' := fun t => (f' t : ℂ)) hL (fun t ht => (hderiv t ht).ofReal_comp)
    (Complex.continuous_ofReal.comp_continuousOn hcont') (by simp [h0]) (by simp [hLz])
  unfold productionArithmeticRealValue
  rw [hc]
  have e1 : (∫ t in (0 : ℝ)..L, (weightedVonMangoldtSqrtRemainder (Real.exp t) : ℂ) *
      (f' t : ℂ)) = ((∫ t in (0 : ℝ)..L, weightedVonMangoldtSqrtRemainder (Real.exp t) * f' t :
        ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  have e2 : (∫ t in (0 : ℝ)..L, ((Real.exp (-t / 2) - archDensity t : ℝ) : ℂ) * (f t : ℂ)) =
      ((∫ t in (0 : ℝ)..L, (Real.exp (-t / 2) - archDensity t) * f t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [e1, e2, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]

/-- **M09, contact-weighted form.**  For `L > 0`, the index-energy test
`t² e_{Dz}(1 - t/L)` of the production second-derivative channel satisfies the
exact weighted von-Mangoldt remainder balance
`A_L[t² e_{Dz}(1 - t/L)] = ∫₀ᴸ R(e^t) (2t e_{Dz}(1 - t/L) - (t²/L) e'_{Dz}(1 - t/L)) dt
    + ∫₀ᴸ (e^{-t/2} - ρ(t)) t² e_{Dz}(1 - t/L) dt`.
This is an identity, not a sign: no contact hypothesis and no positivity of
`R` is used. -/
theorem productionArithmeticRealValue_sq_mul_indexEnergy_eq_weightedRemainder
    {L : ℝ} (hL : 0 < L) (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (fun t => t ^ 2 * productionContactIndexEnergy L K v t) =
      (∫ t in (0 : ℝ)..L, weightedVonMangoldtSqrtRemainder (Real.exp t) *
          (2 * t * productionContactIndexEnergy L K v t -
            t ^ 2 / L * sourceAtomRealEnergyDerivative K
              (sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) (1 - t / L))) +
        ∫ t in (0 : ℝ)..L, (Real.exp (-t / 2) - archDensity t) *
          (t ^ 2 * productionContactIndexEnergy L K v t) := by
  set x := sourceIndexAction K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
  have hd : ∀ t, HasDerivAt (fun s => s ^ 2 * productionContactIndexEnergy L K v s)
      (2 * t * productionContactIndexEnergy L K v t -
        t ^ 2 / L * sourceAtomRealEnergyDerivative K x (1 - t / L)) t := by
    intro t
    have he : HasDerivAt (fun s => productionContactIndexEnergy L K v s)
        (sourceAtomRealEnergyDerivative K x (1 - t / L) * (-(1 / L))) t := by
      have := (hasDerivAt_sourceAtomRealEnergy_transport K x (1 - t / L)).comp t
        (((hasDerivAt_id t).div_const L).const_sub 1)
      simpa [productionContactIndexEnergy, x, Function.comp_def] using this
    have := (hasDerivAt_pow 2 t).mul he
    refine this.congr_deriv ?_
    simp only [productionContactIndexEnergy]
    push_cast
    ring
  refine productionArithmeticRealValue_eq_weightedRemainder hL.le (fun t _ => hd t) ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    have : Continuous fun t : ℝ => sourceAtomRealEnergy K x (1 - t / L) :=
      (continuous_sourceAtomRealEnergy K x).comp (by fun_prop)
    have h2 : Continuous fun t : ℝ => sourceAtomRealEnergyDerivative K x (1 - t / L) :=
      (continuous_sourceAtomRealEnergyDerivative K x).comp (by fun_prop)
    simp only [productionContactIndexEnergy]
    fun_prop
  · simp
  · simp [productionContactIndexEnergy, div_self hL.ne']

/-- The real production value is homogeneous for constant multiples (no
admissibility premise: every channel is linear in the test). -/
theorem productionArithmeticRealValue_const_mul (L a : ℝ) (f : ℝ → ℝ) :
    productionArithmeticRealValue L (fun t => a * f t) = a * productionArithmeticRealValue L f := by
  unfold productionArithmeticRealValue productionArithmeticComplexValue dictionaryCompletePhysicalRHS
  have h1 : ∀ w : ℝ → ℂ, (∫ x in (0 : ℝ)..L, (((a * f x : ℝ)) : ℂ) * w x) =
      (a : ℂ) * ∫ x in (0 : ℝ)..L, (f x : ℂ) * w x := by
    intro w
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast
    ring
  have h2 : (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      primeSourceWeight q * (((a * f (Real.log q) : ℝ)) : ℂ)) =
      (a : ℂ) * ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * (f (Real.log q) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    ring
  rw [h1 (fun x => (completeSourcePoleWeight x : ℂ)), h1 (fun x => (archDensity x : ℂ)), h2,
    ← mul_sub, ← mul_sub, Complex.re_ofReal_mul]

/-- **M09, contact-weighted value.**  At a stationary generated strict-even
contact, with `C = ⟪A w, w⟫ ≥ 0` the response cost of the stationary response,
`A_{L*}[t² e_{Dz}(1 - t/L*)] = -2 L*⁴ C / (2π)²`. -/
theorem GeneratedStrictEvenContact.indexEnergyValue_eq_neg_responseCost
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    productionArithmeticRealValue c.generated.shell.Lstar
        (fun t => t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z t) =
      -(2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2) *
        productionContactResponseCost c.generated.shell.Lstar (c.generated.shell.k + 1)
          (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
            c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) := by
  set L := c.generated.shell.Lstar
  set K := c.generated.shell.k + 1
  have hL : 0 < L := c.Lstar_pos
  have h2 := c.secondPhysicalValue_eq_two_mul_responseCost hstationary
  have hcongr : productionArithmeticRealValue L (productionSecondDerivativePhysicalTest L K c.z) =
      productionArithmeticRealValue L
        (fun t => (-(2 * Real.pi) ^ 2 / L ^ 4) *
          (t ^ 2 * productionContactIndexEnergy L K c.z t)) := by
    refine productionArithmeticRealValue_congr_on_Icc hL fun t ht => ?_
    rw [productionSecondDerivativePhysicalTest_eq_neg_indexEnergy hL K c.z ht]
    ring
  rw [hcongr, productionArithmeticRealValue_const_mul] at h2
  have hπ : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  have hL4 : L ^ 4 ≠ 0 := by positivity
  field_simp at h2 ⊢
  linarith

/-- The contact-weighted value is nonpositive (necessary condition only). -/
theorem GeneratedStrictEvenContact.indexEnergyValue_nonpos
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    productionArithmeticRealValue c.generated.shell.Lstar
        (fun t => t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z t) ≤ 0 := by
  rw [c.indexEnergyValue_eq_neg_responseCost hstationary]
  have hC := productionContactResponseCost_nonnegative c.evenGround_zero
    (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary)
  have hk : 0 ≤ 2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2 := by positivity
  nlinarith

/-- **M09, exact contact-weighted von-Mangoldt remainder balance.**  At a
stationary generated strict-even contact,
`∫₀^{L*} R(e^t) (2t e_{Dz}(1 - t/L*) - (t²/L*) e'_{Dz}(1 - t/L*)) dt
   + ∫₀^{L*} (e^{-t/2} - ρ(t)) t² e_{Dz}(1 - t/L*) dt = -2 L*⁴ C/(2π)² ≤ 0`.
This is a necessary condition satisfied by every such contact, not a
contradiction: no sign of `R` is known that would violate it. -/
theorem GeneratedStrictEvenContact.weightedRemainder_balance
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    (∫ t in (0 : ℝ)..c.generated.shell.Lstar,
        weightedVonMangoldtSqrtRemainder (Real.exp t) *
          (2 * t * productionContactIndexEnergy c.generated.shell.Lstar
              (c.generated.shell.k + 1) c.z t -
            t ^ 2 / c.generated.shell.Lstar * sourceAtomRealEnergyDerivative
              (c.generated.shell.k + 1)
              (sourceIndexAction (c.generated.shell.k + 1)
                (c.z : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))))
              (1 - t / c.generated.shell.Lstar))) +
      (∫ t in (0 : ℝ)..c.generated.shell.Lstar, (Real.exp (-t / 2) - archDensity t) *
          (t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
            (c.generated.shell.k + 1) c.z t)) =
      -(2 * c.generated.shell.Lstar ^ 4 / (2 * Real.pi) ^ 2) *
        productionContactResponseCost c.generated.shell.Lstar (c.generated.shell.k + 1)
          (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
            c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) ∧
    (∫ t in (0 : ℝ)..c.generated.shell.Lstar,
        weightedVonMangoldtSqrtRemainder (Real.exp t) *
          (2 * t * productionContactIndexEnergy c.generated.shell.Lstar
              (c.generated.shell.k + 1) c.z t -
            t ^ 2 / c.generated.shell.Lstar * sourceAtomRealEnergyDerivative
              (c.generated.shell.k + 1)
              (sourceIndexAction (c.generated.shell.k + 1)
                (c.z : EuclideanSpace ℂ (Fin (2 * (c.generated.shell.k + 1) + 1))))
              (1 - t / c.generated.shell.Lstar))) +
      (∫ t in (0 : ℝ)..c.generated.shell.Lstar, (Real.exp (-t / 2) - archDensity t) *
          (t ^ 2 * productionContactIndexEnergy c.generated.shell.Lstar
            (c.generated.shell.k + 1) c.z t)) ≤ 0 := by
  rw [← productionArithmeticRealValue_sq_mul_indexEnergy_eq_weightedRemainder c.Lstar_pos]
  exact ⟨c.indexEnergyValue_eq_neg_responseCost hstationary, c.indexEnergyValue_nonpos hstationary⟩

/-! ## M03: fixed staircase re-expression of the pole-prime discrepancy -/

/-- **M03, fixed staircase.**  On the aperture the canonical pole-prime
discrepancy is `D(t) = 4 sinh(t/2) - B(t)` with the aperture-free staircase
`B(t) = ∑_{n ≤ e^t} Λ(n)/√n` (right-continuous, every `q = p^k` counted at
`log q ≤ t`, zero-von-Mangoldt integers contributing nothing). -/
theorem canonicalPolePrimeDiscrepancy_eq_fixedStaircase {L t : ℝ} (htL : t ≤ L) :
    canonicalPolePrimeDiscrepancy L t =
      4 * Real.sinh (t / 2) - weightedVonMangoldtSqrtSum (Real.exp t) := by
  unfold canonicalPolePrimeDiscrepancy canonicalPoleCumulativeWeight
  rw [canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum htL]

/-- **M03, energy form.**  The pole-minus-prime source energy is
`(1/L) ∫₀ᴸ D(t) e'_u(1 - t/L) dt` with the fixed staircase `D`. -/
theorem matrixRealEnergy_pole_sub_prime_eq_fixedStaircase {L : ℝ} (hL : 0 < L) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPoleMatrix L K) x - matrixRealEnergy (canonicalPrimeMatrix L K) x =
      (1 / L) * ∫ t in (0 : ℝ)..L,
        (4 * Real.sinh (t / 2) - weightedVonMangoldtSqrtSum (Real.exp t)) *
          deriv (sourceAtomRealEnergy K x) (1 - t / L) := by
  rw [matrixRealEnergy_pole_sub_prime_eq_discrepancy hL, canonicalPolePrimeDiscrepancyEnergy]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hL.le] at ht
  simp only [canonicalPolePrimeDiscrepancy_eq_fixedStaircase ht.2]

end Zeta23.CCM

#print axioms Zeta23.CCM.intervalIntegrable_ite_le_mul
#print axioms Zeta23.CCM.intervalIntegral_ite_le_mul
#print axioms Zeta23.CCM.weightedSum_exp_mul_eq_sum_ite
#print axioms Zeta23.CCM.intervalIntegrable_weightedSum_exp_mul
#print axioms Zeta23.CCM.sum_primeSourceWeight_eq_neg_integral_weightedSum
#print axioms Zeta23.CCM.integral_two_exp_half_mul_deriv
#print axioms Zeta23.CCM.regularizedCompletePhysicalRHS_eq_weightedRemainder
#print axioms Zeta23.CCM.intervalIntegrable_mul_archDensity_of_hasDerivAt
#print axioms Zeta23.CCM.regularizedCompletePhysicalRHS_eq_weightedRemainder_of_continuousOn
#print axioms Zeta23.CCM.regularizedCompletePhysicalRHS_eq_dictionary_of_zero
#print axioms Zeta23.CCM.productionArithmeticComplexValue_eq_weightedRemainder
#print axioms Zeta23.CCM.productionArithmeticRealValue_eq_weightedRemainder
#print axioms Zeta23.CCM.productionArithmeticRealValue_sq_mul_indexEnergy_eq_weightedRemainder
#print axioms Zeta23.CCM.productionArithmeticRealValue_const_mul
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.indexEnergyValue_eq_neg_responseCost
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.indexEnergyValue_nonpos
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.weightedRemainder_balance
#print axioms Zeta23.CCM.canonicalPolePrimeDiscrepancy_eq_fixedStaircase
#print axioms Zeta23.CCM.matrixRealEnergy_pole_sub_prime_eq_fixedStaircase
