import Zeta23.OPICAFollowup.SawtoothForce

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.sawtooth_integrable_force_identity`,
`Zeta23.OPICAFollowup.sawtooth_actual_mellin_fourier` and
`Zeta23.OPICAFollowup.sawtooth_norm_weighted_zeta_moment` (F1).

Definition audits pin w(t) = e^(-t/2){e^t} and the tempered force 𝔤 = -(∂_t + 1/2) w built from
Mathlib's tempered-distribution derivative. All three roots are restated in full. Domain consumers
check:
- an independent compactly supported test around log 2 isolates the single atom 2^(-1/2)
  (the arithmetic part of 𝔤 is seen by an actual test, not assumed);
- the jump of w at log 2 equals minus that atom weight;
- the two transform conventions agree: 𝓕_log w(2πη) = 𝓕 w(η);
- the budget is a positive constant independent of any zero: 1/2 < log(2π) - γ < 2;
- the H⁻¹ bound applies to actual Schwartz tests. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup
namespace OPICASawtoothForceIndependent

/-! ### Definition audits -/

theorem audit_sawtoothWeight (t : ℝ) :
    sawtoothWeight t = ((Real.exp (-t / 2) * Int.fract (Real.exp t) : ℝ) : ℂ) := rfl

theorem audit_nativeLogForce :
    nativeLogForce = -(TemperedDistribution.derivCLM ℂ sawtoothWeightTD) - (1 / 2 : ℂ) • sawtoothWeightTD :=
  rfl

/-! ### Restated roots -/

theorem expected_sawtooth_integrable_force_identity :
    Integrable sawtoothWeight ∧ MemLp sawtoothWeight 2 ∧
    (∀ t : ℝ, t < 0 → sawtoothWeight t = (Real.exp (t / 2) : ℂ)) ∧
    (∀ t : ℝ, ‖sawtoothWeight t‖ ≤ Real.exp (-t / 2)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), nativeLogForce φ = ∫ t, sawtoothWeight t * (deriv φ t - φ t / 2)) ∧
    (∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      nativeLogForce (hc.toSchwartzMap hφ) =
        ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
          ∫ t, (Real.exp (t / 2) : ℂ) * φ t) ∧
    (∀ n : ℕ, 1 ≤ n →
      Tendsto sawtoothWeight (𝓝[<] (Real.log n)) (𝓝 ((((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ∧
        sawtoothWeight (Real.log n) = 0) :=
  sawtooth_integrable_force_identity

theorem expected_sawtooth_actual_mellin_fourier :
    (∀ s : ℂ, 0 < s.re → s.re < 1 →
      IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = -riemannZeta s / s) ∧
    (∀ ξ : ℝ, logFourier sawtoothWeight ξ = -riemannZeta (1 / 2 + ξ * I) / (1 / 2 + ξ * I)) ∧
    (∀ ξ : ℝ, -(1 / 2 + ξ * I) * logFourier sawtoothWeight ξ = riemannZeta (1 / 2 + ξ * I)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 nativeLogForce) φ =
      ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η) :=
  sawtooth_actual_mellin_fourier

theorem expected_sawtooth_norm_weighted_zeta_moment :
    (∫ x in (0 : ℝ)..1, Int.fract x ^ 2 / x ^ 2) = 1 ∧
    (∀ n : ℕ, 1 ≤ n → ∫ x in (n : ℝ)..(n + 1), Int.fract x ^ 2 / x ^ 2 =
      1 + n / (n + 1) - 2 * n * Real.log (1 + 1 / n)) ∧
    (∀ L : ℕ, 1 ≤ L → ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2 =
      2 * L - harmonic L - 2 * (L - 1) * Real.log L + 2 * Real.log (Real.Gamma L)) ∧
    Tendsto (fun L : ℕ => ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2) atTop
      (𝓝 (Real.log (2 * π) - Real.eulerMascheroniConstant)) ∧
    (∫ t, ‖sawtoothWeight t‖ ^ 2) = Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    Integrable (fun ξ : ℝ => ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4)) ∧
    1 / (2 * π) * ∫ ξ : ℝ, ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4) =
      Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    (∀ φ φ' : ℝ → ℂ, LogH1 φ φ' →
      ‖∫ t, sawtoothWeight t * (φ' t - φ t / 2)‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), ‖nativeLogForce φ‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖deriv φ t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) :=
  sawtooth_norm_weighted_zeta_moment

/-! ### Domain consumers -/

/-- An independent bump of radius 1/4 centred at log 2. -/
def bumpLog2 : ContDiffBump (Real.log 2) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

lemma tsupport_bumpLog2 :
    tsupport (fun t => ((bumpLog2 t : ℝ) : ℂ)) ⊆ Icc (Real.log 2 - 1 / 4) (Real.log 2 + 1 / 4) := by
  refine (tsupport_comp_subset Complex.ofReal_zero bumpLog2).trans ?_
  rw [bumpLog2.tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(1 / 4 : ℝ) ≤ x - Real.log 2 ∧ x - Real.log 2 ≤ 1 / 4 at hx
  constructor <;> linarith [hx.1, hx.2]

/-- On the bump at log 2 the arithmetic part of 𝔤 is exactly the single atom 2^(-1/2). -/
theorem expected_single_atom :
    ∃ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      φ (Real.log 2) = 1 ∧
      nativeLogForce (hc.toSchwartzMap hφ) =
        (((2 : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) - ∫ t, (Real.exp (t / 2) : ℂ) * φ t := by
  set φ : ℝ → ℂ := fun t => ((bumpLog2 t : ℝ) : ℂ)
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp bumpLog2.contDiff
  have hc : HasCompactSupport φ := bumpLog2.hasCompactSupport.comp_left Complex.ofReal_zero
  have h1 : φ (Real.log 2) = 1 := by
    simp only [φ, bumpLog2.one_of_mem_closedBall (Metric.mem_closedBall_self bumpLog2.rIn_pos.le),
      Complex.ofReal_one]
  refine ⟨φ, hφ, hc, h1, ?_⟩
  rw [(sawtooth_integrable_force_identity).2.2.2.2.2.1 φ hφ hc]
  congr 1
  rw [tsum_eq_single 1 fun n hn => ?_]
  · norm_num [h1]
  · refine mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (f := φ) fun h => ?_)
    have hb := tsupport_bumpLog2 h
    have hl2 : (0.69 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2' : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
    rcases Nat.lt_or_gt_of_ne hn with h0 | h2
    · have : n = 0 := by omega
      subst this; simp only [CharP.cast_eq_zero, zero_add, Real.log_one] at hb; linarith [hb.1]
    · have h3 : Real.log 3 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by norm_num)
          (by have h2' : (2 : ℝ) ≤ n := (by exact_mod_cast h2); linarith)
      have h32 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have hl32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
        have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
        norm_num at this ⊢; linarith
      linarith [hb.2]

/-- The jump of w at log 2 is minus the atom weight 2^(-1/2) of the compact-test identity. -/
theorem expected_jump_matches_atom :
    Tendsto sawtoothWeight (𝓝[<] (Real.log 2)) (𝓝 ((((2 : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ∧
      sawtoothWeight (Real.log 2) = 0 := by
  have := (sawtooth_integrable_force_identity).2.2.2.2.2.2 2 (by norm_num)
  simpa using this

/-- The two conventions agree: 𝓕_log w(2πη) = 𝓕 w(η). -/
theorem expected_conventions (η : ℝ) :
    logFourier sawtoothWeight (2 * π * η) = 𝓕 sawtoothWeight η := by
  rw [logFourier_eq_fourier]; field_simp

/-- The source budget is a positive zero-free constant: 1/2 < log(2π) - γ < 2. -/
theorem expected_budget_bounds :
    1 / 2 < Real.log (2 * π) - Real.eulerMascheroniConstant ∧
      Real.log (2 * π) - Real.eulerMascheroniConstant < 2 := by
  have hg1 := Real.one_half_lt_eulerMascheroniConstant
  have hg2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi := Real.two_le_pi
  have hpi' := Real.pi_le_four
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlo : 2 * Real.log 2 ≤ Real.log (2 * π) := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hhi : Real.log (2 * π) ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  constructor <;> linarith

end OPICASawtoothForceIndependent
#print axioms Zeta23.OPICAFollowup.sawtooth_integrable_force_identity
#print axioms Zeta23.OPICAFollowup.sawtooth_actual_mellin_fourier
#print axioms Zeta23.OPICAFollowup.sawtooth_norm_weighted_zeta_moment
#print axioms OPICASawtoothForceIndependent.audit_nativeLogForce
#print axioms OPICASawtoothForceIndependent.expected_sawtooth_integrable_force_identity
#print axioms OPICASawtoothForceIndependent.expected_sawtooth_actual_mellin_fourier
#print axioms OPICASawtoothForceIndependent.expected_sawtooth_norm_weighted_zeta_moment
#print axioms OPICASawtoothForceIndependent.expected_single_atom
#print axioms OPICASawtoothForceIndependent.expected_jump_matches_atom
#print axioms OPICASawtoothForceIndependent.expected_conventions
#print axioms OPICASawtoothForceIndependent.expected_budget_bounds
