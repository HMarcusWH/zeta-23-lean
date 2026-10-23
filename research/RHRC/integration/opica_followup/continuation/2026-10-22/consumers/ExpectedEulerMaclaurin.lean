import Zeta23.OPICAFollowup.ProfileEulerMaclaurin
import Zeta23.OPICAFollowup.RenormalizedCoPoisson

/- Independent consumers for the original root
`Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform` (R2-S1a, R2-H1, F3; display S1.3).

Definition audits pin the periodic Bernoulli functions, the right-endpoint power sum and the
explicit remainder to their constructions. The root is restated in full. Domain consumers check:
- the paper's O-form for every fixed parameter in `0 < Re s`, `s ≠ 1`;
- that the finite sum is right-closed: crossing an integer `n` adds exactly `n^(-s)`;
- composition with the actual CP1 construction `finiteSumSrho` at `s = ρ` and `s = 1 - ρ`:
  the two `B₁/x` terms cancel and the exact S1a identity holds for every strip parameter;
- at an actual zero in the strip (with the functional equation for `ζ(1 - ρ) = 0`),
  `S_ρ(x) = b_ρ + (2ρ - 1) B₂({x}) / (2x²) + O(x^(-3))`, uniformly in real cutoffs `x ≥ 1`;
- the exact differentiated remainder is `O(x^(-Re s - 2))` inside every cell;
- non-vacuity at the critical point `s = 1/2` and the integer cutoff `x = 1`. -/
noncomputable section
open Set MeasureTheory Filter Complex Asymptotics
open scoped Topology
open Zeta23.OPICAFollowup
namespace OPICAEulerMaclaurinIndependent

/-! ### Definition audits -/

theorem audit_bernoulliOneRight (x : ℝ) : bernoulliOneRight x = Int.fract x - 1 / 2 := rfl

theorem audit_bernoulliTwo (x : ℝ) :
    bernoulliTwo x = Int.fract x ^ 2 - Int.fract x + 1 / 6 := rfl

theorem audit_rightPowerSum (s : ℂ) (x : ℝ) :
    rightPowerSum s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s) := rfl

theorem audit_remainder (s : ℂ) (x : ℝ) : eulerMaclaurinRemainder s x =
    -(s * (s + 1) / 6) * (bernoulliThree x : ℂ) * (x : ℂ) ^ (-s - 2) +
      s * (s + 1) * (s + 2) / 6 * ∫ t in Ioi x, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3) := rfl

theorem audit_bernoulliThree (x : ℝ) : bernoulliThree x =
    Int.fract x ^ 3 - 3 / 2 * Int.fract x ^ 2 + 1 / 2 * Int.fract x := rfl

/-! ### Restated root -/

theorem expected_finite_sum_euler_maclaurin_uniform :
    (∀ (s : ℂ) (n : ℕ) (y : ℝ), y ∈ Ico (n : ℝ) (n + 1) →
      rightPowerSum s y = ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-s)) ∧
    (∀ n : ℕ, bernoulliOneRight n = -1 / 2 ∧ bernoulliTwo n = 1 / 6) ∧
    (∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
        (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
          s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x) ∧
    (∀ s : ℂ, 0 < s.re → ∀ x : ℝ, 0 < x →
      ‖eulerMaclaurinRemainder s x‖ ≤
        (‖s‖ * (‖s‖ + 1) / 6 + ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 12) * x ^ (-s.re - 2)) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | 0 < s.re ∧ s ≠ 1} → ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ K, ∀ x : ℝ, 1 ≤ x →
        ‖rightPowerSum s x - (riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
          (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
            s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2)‖ ≤ C * x ^ (-s.re - 2)) ∧
    (∀ x : ℝ, 1 ≤ x →
      DifferentiableOn ℂ (fun s => eulerMaclaurinRemainder s x) {s : ℂ | 0 < s.re ∧ s ≠ 1}) ∧
    (∀ (s : ℂ) (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → HasDerivAt (rightPowerSum s) 0 x) ∧
    (∀ s : ℂ, 0 < s.re → ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (eulerMaclaurinRemainder s)
        (-(s * (s + 1) / 2) * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 2)) x) :=
  finite_sum_euler_maclaurin_uniform

/-! ### Domain consumers -/

/-- The paper's O-form (S1.3) for every fixed parameter of the domain. -/
theorem expected_isBigO {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    (fun x : ℝ => rightPowerSum s x - (riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2)) =O[atTop]
      (fun x : ℝ => x ^ (-s.re - 2)) := by
  obtain ⟨C, -, hC⟩ := finite_sum_euler_maclaurin_uniform.2.2.2.2.1 {s} isCompact_singleton
    (by simpa using ⟨h0, h1⟩)
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact hC s rfl x hx

/-- Right-closed convention: crossing the integer `n ≥ 1` adds exactly the endpoint term. -/
theorem expected_right_endpoint_jump (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    rightPowerSum s n = rightPowerSum s ((n : ℝ) - 1 / 2) + (n : ℂ) ^ (-s) := by
  have hroot := finite_sum_euler_maclaurin_uniform.1
  have h1 := hroot s n n ⟨le_rfl, by linarith⟩
  have h2 := hroot s (n - 1) ((n : ℝ) - 1 / 2) (by
    constructor <;> push_cast [Nat.cast_sub hn] <;> linarith)
  rw [h1, h2]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]

lemma cpow_sub_one {x : ℝ} (hx : 0 < x) (a : ℂ) : (x : ℂ) ^ (a - 1) = (x : ℂ) ^ a / x := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]

/-- Composition with the actual CP1 construction: at `s = ρ` and `s = 1 - ρ` the `B₁/x` terms
cancel and the exact S1a identity holds for every strip parameter and real cutoff `x ≥ 1`. -/
theorem expected_srho_expansion {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ} (hx : 1 ≤ x) :
    finiteSumSrho ρ x = riemannZeta (1 - ρ) * (x : ℂ) ^ (-ρ) - riemannZeta ρ * (x : ℂ) ^ (ρ - 1) +
      (1 / ρ - 1 / (1 - ρ)) + (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) +
        ((x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x -
          (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x) := by
  have hx0 : 0 < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  have hσ1 : 1 - ρ ≠ 1 := fun h => hρ0 (by linear_combination -h)
  have hroot := finite_sum_euler_maclaurin_uniform.2.2.1
  have eA := hroot (1 - ρ) hσ0 hσ1 x hx
  have eB := hroot ρ h0 hρ1 x hx
  have hS : finiteSumSrho ρ x = (x : ℂ) ^ (-ρ) * rightPowerSum (1 - ρ) x -
      (x : ℂ) ^ (ρ - 1) * rightPowerSum ρ x := by
    simp only [finiteSumSrho, coPoissonPowerSums, rightPowerSum, neg_sub]
  have hv : (x : ℂ) ^ ρ ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hρ0).mpr hxne
  have hneg : (x : ℂ) ^ (-ρ) = ((x : ℂ) ^ ρ)⁻¹ := Complex.cpow_neg _ _
  have p1 : (x : ℂ) ^ (1 - (1 - ρ)) = (x : ℂ) ^ ρ := by ring_nf
  have p2 : (x : ℂ) ^ (-(1 - ρ)) = (x : ℂ) ^ ρ / x := by
    rw [show -(1 - ρ) = ρ - 1 by ring, cpow_sub_one hx0]
  have p3 : (x : ℂ) ^ (-(1 - ρ) - 1) = (x : ℂ) ^ ρ / x / x := by
    rw [cpow_sub_one hx0, p2]
  have p4 : (x : ℂ) ^ (1 - ρ) = x * ((x : ℂ) ^ ρ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hxne, Complex.cpow_one, div_eq_mul_inv]
  have p5 : (x : ℂ) ^ (-ρ - 1) = ((x : ℂ) ^ ρ)⁻¹ / x := by rw [cpow_sub_one hx0, hneg]
  have p6 : (x : ℂ) ^ (ρ - 1) = (x : ℂ) ^ ρ / x := cpow_sub_one hx0 ρ
  have hs1 : (1 : ℂ) - (1 - ρ) = ρ := by ring
  have hs2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  rw [hS, eA, eB, p1, p2, p3, p4, p5, p6, hneg, hs1]
  field_simp
  ring

/-- At an actual zero in the strip, `S_ρ(x) = b_ρ + (2ρ - 1) B₂({x}) / (2x²) + O(x^(-3))`
uniformly in real cutoffs `x ≥ 1` (paper, proof of S1.1). -/
theorem expected_srho_tail_at_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖finiteSumSrho ρ x - (1 / ρ - 1 / (1 - ρ)) -
        (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)‖ ≤ C * x ^ (-3 : ℝ) := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hz' : riemannZeta (1 - ρ) = 0 := by
    have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
  set A := ‖1 - ρ‖ * (‖1 - ρ‖ + 1) / 6 + ‖1 - ρ‖ * (‖1 - ρ‖ + 1) * (‖1 - ρ‖ + 2) / 12
  set B := ‖ρ‖ * (‖ρ‖ + 1) / 6 + ‖ρ‖ * (‖ρ‖ + 1) * (‖ρ‖ + 2) / 12
  refine ⟨A + B, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hroot := finite_sum_euler_maclaurin_uniform.2.2.2.1
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  rw [expected_srho_expansion h0 h1 hx, hz, hz']
  have hcancel : (0 : ℂ) * (x : ℂ) ^ (-ρ) - 0 * (x : ℂ) ^ (ρ - 1) + (1 / ρ - 1 / (1 - ρ)) +
      (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) +
        ((x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x -
          (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x) - (1 / ρ - 1 / (1 - ρ)) -
        (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) =
      (x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x -
        (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x := by ring
  rw [hcancel]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hA := hroot (1 - ρ) hσ0 x hx0
  have hB := hroot ρ h0 x hx0
  have e1 : x ^ (-ρ).re * x ^ (-(1 - ρ).re - 2) = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx0]; congr 1; simp; ring
  have e2 : x ^ (ρ - 1).re * x ^ (-ρ.re - 2) = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx0]; congr 1; simp; ring
  have hp1 : 0 ≤ x ^ (-ρ).re := Real.rpow_nonneg hx0.le _
  have hp2 : 0 ≤ x ^ (ρ - 1).re := Real.rpow_nonneg hx0.le _
  calc x ^ (-ρ).re * ‖eulerMaclaurinRemainder (1 - ρ) x‖ +
        x ^ (ρ - 1).re * ‖eulerMaclaurinRemainder ρ x‖
      ≤ x ^ (-ρ).re * (A * x ^ (-(1 - ρ).re - 2)) + x ^ (ρ - 1).re * (B * x ^ (-ρ.re - 2)) := by
        gcongr
    _ = (A + B) * x ^ (-3 : ℝ) := by
        rw [mul_left_comm, e1, mul_left_comm, e2]; ring

/-- The exact differentiated remainder is `O(x^(-Re s - 2))` inside every cell. -/
theorem expected_remainder_derivative_bound {s : ℂ} (h0 : 0 < s.re) {n : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    ‖deriv (eulerMaclaurinRemainder s) x‖ ≤ ‖s‖ * (‖s‖ + 1) / 2 * x ^ (-s.re - 2) := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx.1
  rw [(finite_sum_euler_maclaurin_uniform.2.2.2.2.2.2.2 s h0 n x hx).deriv, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs, norm_neg,
    norm_div, norm_mul]
  have hB2 : |bernoulliTwo x| ≤ 1 := by
    unfold bernoulliTwo
    have h0' := Int.fract_nonneg x
    have h1' := Int.fract_lt_one x
    rw [abs_le]; constructor <;> nlinarith
  have hre : (-s - 2).re = -s.re - 2 := by simp
  rw [hre]
  have hn1 : ‖s + 1‖ ≤ ‖s‖ + 1 := (norm_add_le _ _).trans (by simp)
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have hp : 0 ≤ x ^ (-s.re - 2) := Real.rpow_nonneg hx0.le _
  calc ‖s‖ * ‖s + 1‖ / 2 * |bernoulliTwo x| * x ^ (-s.re - 2)
      ≤ ‖s‖ * (‖s‖ + 1) / 2 * 1 * x ^ (-s.re - 2) := by gcongr
    _ = ‖s‖ * (‖s‖ + 1) / 2 * x ^ (-s.re - 2) := by ring

/-- Non-vacuity at the critical point `s = 1/2` and the integer cutoff `x = 1`:
`1 = ζ(1/2) + 2 + 1/2 - 1/24 + R(1/2, 1)`. -/
theorem expected_nonvacuous_half :
    (1 : ℂ) = riemannZeta (1 / 2) + 2 + 1 / 2 - 1 / 24 + eulerMaclaurinRemainder (1 / 2) 1 := by
  have h := finite_sum_euler_maclaurin_uniform.2.2.1 (1 / 2) (by norm_num) (by norm_num) 1 le_rfl
  have hint := finite_sum_euler_maclaurin_uniform.2.1 1
  have hsum : rightPowerSum (1 / 2) 1 = 1 := by simp [rightPowerSum]
  rw [hsum] at h
  simp only [Nat.cast_one] at hint
  rw [hint.1, hint.2] at h
  simp only [Complex.ofReal_one, Complex.one_cpow] at h
  push_cast at h
  linear_combination h

end OPICAEulerMaclaurinIndependent
#print axioms Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform
#print axioms OPICAEulerMaclaurinIndependent.audit_rightPowerSum
#print axioms OPICAEulerMaclaurinIndependent.audit_remainder
#print axioms OPICAEulerMaclaurinIndependent.expected_finite_sum_euler_maclaurin_uniform
#print axioms OPICAEulerMaclaurinIndependent.expected_isBigO
#print axioms OPICAEulerMaclaurinIndependent.expected_right_endpoint_jump
#print axioms OPICAEulerMaclaurinIndependent.expected_srho_expansion
#print axioms OPICAEulerMaclaurinIndependent.expected_srho_tail_at_zero
#print axioms OPICAEulerMaclaurinIndependent.expected_remainder_derivative_bound
#print axioms OPICAEulerMaclaurinIndependent.expected_nonvacuous_half
