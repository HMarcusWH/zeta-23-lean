import Zeta23.OPICARound4.SourceDiscrepancy
import Zeta23.CCM.WeightedRemainderIdentity

noncomputable section
namespace Zeta23.OPICARound4
open CCM MeasureTheory Set
open scoped BigOperators ArithmeticFunction Interval

theorem psi_eq_sum_Icc_two (x : ℝ) :
    Chebyshev.psi x = ∑ q ∈ Finset.Icc 2 ⌊x⌋₊, Λ q := by
  unfold Chebyshev.psi
  symm
  apply Finset.sum_subset
  · intro q hq
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hq ⊢
    omega
  · intro q hq hn
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hq hn
    have : q = 1 := by omega
    simp [this]

theorem prime_log_mem_interval {L : ℝ} {q : ℕ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    Real.log q ∈ Icc (0 : ℝ) L := by
  have hq' := Finset.mem_Icc.mp hq
  have hp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  refine ⟨Real.log_natCast_nonneg _, ?_⟩
  rw [← Real.log_exp L]
  exact Real.log_le_log hp ((Nat.le_floor_iff (Real.exp_pos _).le).mp hq'.2)

theorem psi_exp_eq_sum_steps {L y : ℝ} (hy : y ≤ L) :
    Chebyshev.psi (Real.exp y) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, if Real.log q ≤ y then Λ q else 0 := by
  rw [psi_eq_sum_Icc_two]
  calc
    _ = ∑ q ∈ Finset.Icc 2 ⌊Real.exp y⌋₊, if Real.log q ≤ y then Λ q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos (prime_log_mem_interval hq).2]
    _ = _ := by
      apply Finset.sum_subset
      · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (Real.exp_le_exp.mpr hy))
      · intro q hq hqn
        rw [if_neg]
        intro hlog
        have hq' := Finset.mem_Icc.mp hq
        have hp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        have hqe : (q : ℝ) ≤ Real.exp y := (Real.log_le_iff_le_exp hp).mp hlog
        exact hqn (Finset.mem_Icc.mpr ⟨hq'.1,
          (Nat.le_floor_iff (Real.exp_pos _).le).mpr hqe⟩)

/-- Finite summation by parts against the actual right-continuous Chebyshev
staircase. No estimate for that staircase is used. -/
theorem prime_log_abel {L : ℝ} (hL : 0 ≤ L) {g g' : ℝ → ℂ}
    (hg : ∀ y ∈ Icc 0 L, HasDerivAt g (g' y) y)
    (hgi : IntervalIntegrable g' volume 0 L) (hgL : g L = 0) :
    ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q : ℂ) * g (Real.log q) =
      -∫ y in (0 : ℝ)..L, (Chebyshev.psi (Real.exp y) : ℂ) * g' y := by
  have hs (y : ℝ) (hy : y ≤ L) :
      (Chebyshev.psi (Real.exp y) : ℂ) * g' y =
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          (if Real.log q ≤ y then (Λ q : ℂ) else 0) * g' y := by
    rw [psi_exp_eq_sum_steps hy]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  rw [intervalIntegral.integral_congr (g := fun y =>
    ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (if Real.log q ≤ y then (Λ q : ℂ) else 0) * g' y)
    (fun y hy => hs y (by rw [uIcc_of_le hL] at hy; exact hy.2)),
    intervalIntegral.integral_finsetSum (fun q hq =>
      intervalIntegrable_ite_le_mul (prime_log_mem_interval hq).1
        (prime_log_mem_interval hq).2 _ hgi), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h0, h1⟩ := prime_log_mem_interval hq
  rw [intervalIntegral_ite_le_mul h0 h1 _ hgi]
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := g) (f' := g') (a := Real.log q) (b := L)
    (fun y hy => hg y (by
      rw [uIcc_of_le h1] at hy
      exact ⟨h0.trans hy.1, hy.2⟩))
    (hgi.mono_set (by
      rw [uIcc_of_le h1, uIcc_of_le hL]
      exact Icc_subset_Icc h0 le_rfl))
  rw [hf, hgL]
  ring

theorem intervalIntegrable_psi_exp_mul {L : ℝ} (hL : 0 ≤ L) {g' : ℝ → ℂ}
    (hgi : IntervalIntegrable g' volume 0 L) :
    IntervalIntegrable (fun y => (Chebyshev.psi (Real.exp y) : ℂ) * g' y) volume 0 L := by
  have hs : IntervalIntegrable (fun y =>
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        (if Real.log q ≤ y then (Λ q : ℂ) else 0) * g' y) volume 0 L := by
    have hi := IntervalIntegrable.sum (μ := volume) (a := 0) (b := L)
      (Finset.Icc 2 ⌊Real.exp L⌋₊)
      (f := fun q y => (if Real.log q ≤ y then (Λ q : ℂ) else 0) * g' y)
      (fun q hq => intervalIntegrable_ite_le_mul (prime_log_mem_interval hq).1
        (prime_log_mem_interval hq).2 _ hgi)
    simpa only [Finset.sum_fn] using hi
  apply hs.congr_uIoo
  intro y hy
  rw [uIoo_of_le hL] at hy
  dsimp only
  rw [psi_exp_eq_sum_steps hy.2.le]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp

theorem exp_neg_log_half_eq_inv_sqrt {q : ℕ} (hq : 0 < q) :
    Real.exp (-Real.log q / 2) = (Real.sqrt q)⁻¹ := by
  have hp : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : Real.exp (Real.log q / 2) = Real.sqrt q := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [neg_div, Real.exp_neg, hs]

/-- Exact logarithmic discrepancy identity for a C¹ endpoint-zero complex
test. The integrability hypotheses are proved from continuity; the discrepancy
is the actual Chebyshev function, not a definition chosen for this identity. -/
theorem prime_discrepancy_log_integral {L : ℝ} (hL : 0 ≤ L) {F F' : ℝ → ℂ}
    (hF : ∀ y : ℝ, HasDerivAt F (F' y) y) (hF' : Continuous F')
    (hF0 : F 0 = 0) (hFL : F L = 0) :
    (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * F (Real.log q)) -
      (∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * F y) =
      -∫ y in (0 : ℝ)..L,
        ((Chebyshev.psi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
          (Real.exp (-y / 2) : ℂ) * (F' y - F y / 2) := by
  let g : ℝ → ℂ := fun y => (Real.exp (-y / 2) : ℂ) * F y
  let g' : ℝ → ℂ := fun y => (Real.exp (-y / 2) : ℂ) * (F' y - F y / 2)
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun y => (hF y).continuousAt
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hg'c : Continuous g' := by dsimp [g']; fun_prop
  have hgd (y : ℝ) : HasDerivAt g (g' y) y := by
    have he := ((((hasDerivAt_id y).neg).div_const 2).exp).ofReal_comp
    have hd := he.mul (hF y)
    change HasDerivAt g _ y at hd
    apply hd.congr_deriv
    dsimp [g']
    push_cast
    ring
  have hgi : IntervalIntegrable g' volume 0 L := hg'c.intervalIntegrable (0 : ℝ) L
  have hp := prime_log_abel hL (fun y _ => hgd y) hgi (by simp [g, hFL])
  have hsum : (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, (Λ q : ℂ) * g (Real.log q)) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊, primeSourceWeight q * F (Real.log q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    simp only [g, exp_neg_log_half_eq_inv_sqrt hq0, primeSourceWeight]
    push_cast
    ring
  rw [hsum] at hp
  have he (y : ℝ) : HasDerivAt (fun y : ℝ => (Real.exp y : ℂ)) (Real.exp y : ℂ) y :=
    (Real.hasDerivAt_exp y).ofReal_comp
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := L) (u := fun y : ℝ => (Real.exp y : ℂ))
    (u' := fun y => (Real.exp y : ℂ)) (v := g) (v' := g')
    (fun y _ => he y) (fun y _ => hgd y)
    ((by fun_prop : Continuous fun y : ℝ => (Real.exp y : ℂ)).intervalIntegrable 0 L) hgi
  simp only [g, hF0, hFL, mul_zero, sub_zero, zero_sub] at hi
  have hexp (y : ℝ) : Real.exp y * Real.exp (-y / 2) = Real.exp (y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hm : (∫ y in (0 : ℝ)..L, (Real.exp y : ℂ) * g y) =
      ∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * F y := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [g]
    rw [← mul_assoc, ← Complex.ofReal_mul, hexp]
  rw [hm] at hi
  have hpi := intervalIntegrable_psi_exp_mul hL hgi
  have hei : IntervalIntegrable (fun y => (Real.exp y : ℂ) * g' y) volume 0 L :=
    ((by fun_prop : Continuous fun y : ℝ => (Real.exp y : ℂ)).mul hg'c).intervalIntegrable 0 L
  have hr : (∫ y in (0 : ℝ)..L,
      ((Chebyshev.psi (Real.exp y) - Real.exp y : ℝ) : ℂ) *
        (Real.exp (-y / 2) : ℂ) * (F' y - F y / 2)) =
      (∫ y in (0 : ℝ)..L, (Chebyshev.psi (Real.exp y) : ℂ) * g' y) -
        ∫ y in (0 : ℝ)..L, (Real.exp y : ℂ) * g' y := by
    rw [← intervalIntegral.integral_sub hpi hei]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [g']
    push_cast
    ring
  rw [hp, hr]
  rw [hi]
  ring

/-- The exact derivative of the same native source-dependent test. -/
def correctedSourceTestDerivative (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (y : ℝ) : ℂ :=
  (-(1 / L) : ℝ) • sourceAtomPairingDerivative K (correctedSourceRow L K)
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - y / L)

theorem correctedSourceTestDerivative_continuous (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : Continuous (correctedSourceTestDerivative L K u) := by
  have hc : Continuous (sourceAtomPairingDerivative K (correctedSourceRow L K)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hasDerivAt_sourceAtomPairingDerivative K _ _ y).continuousAt
  change Continuous (fun y : ℝ => (-(1 / L) : ℝ) •
    sourceAtomPairingDerivative K (correctedSourceRow L K)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - y / L))
  exact (continuous_const : Continuous (fun _ : ℝ => (-(1 / L) : ℝ))).smul (hc.comp
    (show Continuous (fun y : ℝ => 1 - y / L) by fun_prop))

theorem native_prime_discrepancy_integral {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      primeSourceWeight q * correctedSourceTest L K u (Real.log q)) -
      (∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * correctedSourceTest L K u y) =
      -∫ y in (0 : ℝ)..L,
        ((Chebyshev.psi (Real.exp y) - Real.exp y : ℝ) : ℂ) * (Real.exp (-y / 2) : ℂ) *
          (correctedSourceTestDerivative L K u y - correctedSourceTest L K u y / 2) :=
  prime_discrepancy_log_integral hL.le
    (correctedSourceTest_hasDerivAt L K u) (correctedSourceTestDerivative_continuous L K u)
    (correctedSourceTest_lower_endpoint L K u) (correctedSourceTest_upper_endpoint hL K u)

end Zeta23.OPICARound4
