import Zeta23.OPICAFollowup.LogFourierSobolev
import Zeta23.OPICAFollowup.ZeroProfiles

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.log_unitary_form_identity`
and `Zeta23.OPICAFollowup.log_fourier_plancherel` (R2-S1b, F1, F2, F3).

Definition audits pin the log transform, the log unitary, the form and the form domain. Both
roots are restated in full. Domain consumers check:
- the two roots fit together: ψ' - ψ/2 = e^(3t/2) h'(e^t), and the H¹ shift norm of ψ = U h equals
  the log form of h;
- the actual form domain is nonempty and non-degenerate (h = e^(-x));
- the actual zero profile at an actual zero lies in the form domain with its explicit
  right derivative, so the paper's identity (S1.5) holds for it:
  ∫_0^∞ x²|h'|² = ∫ |ψ'|² + (1/4) ∫_0^∞ |h|². -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform Real
open Zeta23.OPICAFollowup
namespace OPICALogFourierSobolevIndependent

/-! ### Definition audits -/

theorem audit_logFourier (f : ℝ → ℂ) (ξ : ℝ) :
    logFourier f ξ = ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t := rfl

theorem audit_logUnitary (h : ℝ → ℂ) (t : ℝ) :
    logUnitary h t = (Real.exp (t / 2) : ℂ) * h (Real.exp t) := rfl

theorem audit_logForm (h' : ℝ → ℂ) : logForm h' = ∫ x in Ioi 0, x ^ 2 * ‖h' x‖ ^ 2 := rfl

theorem audit_logFormDomain (h h' : ℝ → ℂ) : LogFormDomain h h' ↔
    ((∀ a b : ℝ, 0 < a → 0 < b → h b - h a = ∫ x in a..b, h' x) ∧
      (∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable h' volume a b) ∧ Measurable h' ∧
      MemLp h 2 (volume.restrict (Ioi 0)) ∧
      MemLp (fun x : ℝ => (x : ℂ) * h' x) 2 (volume.restrict (Ioi 0))) :=
  ⟨fun hD => ⟨hD.1, hD.2, hD.3, hD.4, hD.5⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-! ### Restated roots -/

theorem expected_log_unitary_form_identity (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    MemLp (logUnitary h) 2 ∧
    (∫ t, ‖logUnitary h t‖ ^ 2) = ∫ x in Ioi 0, ‖h x‖ ^ 2 ∧
    (∀ a b : ℝ, logUnitary h b - logUnitary h a = ∫ t in a..b, logUnitaryDeriv h h' t) ∧
    MemLp (logUnitaryDeriv h h') 2 ∧
    logForm h' = (∫ t, ‖logUnitaryDeriv h h' t‖ ^ 2) + 1 / 4 * ∫ x in Ioi 0, ‖h x‖ ^ 2 ∧
    LogH1 (logUnitary h) (logUnitaryDeriv h h') :=
  log_unitary_form_identity h h' hD

theorem expected_log_fourier_plancherel :
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t) ∧
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = 𝓕 f (ξ / (2 * π))) ∧
    (∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
      Integrable (fun ξ => ‖logFourier f ξ‖ ^ 2) ∧
        ∫ t, ‖f t‖ ^ 2 = 1 / (2 * π) * ∫ ξ, ‖logFourier f ξ‖ ^ 2) ∧
    (∀ f : ℝ → ℂ, Integrable f → Differentiable ℝ f → Integrable (deriv f) →
      ∀ ξ : ℝ, logFourier (deriv f) ξ = (ξ : ℂ) * I * logFourier f ξ) ∧
    (∀ f : ℝ → ℂ, Integrable f → MemLp f 2 → Differentiable ℝ f → Integrable (deriv f) →
      MemLp (deriv f) 2 →
        (∫ t, ‖deriv f t‖ ^ 2) + 1 / 4 * ∫ t, ‖f t‖ ^ 2 =
          1 / (2 * π) * ∫ ξ, (ξ ^ 2 + 1 / 4) * ‖logFourier f ξ‖ ^ 2) ∧
    (∀ φ φ' : ℝ → ℂ, LogH1 φ φ' →
      ∫ t, ‖φ' t - φ t / 2‖ ^ 2 = (∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ∧
    (∀ w φ φ' : ℝ → ℂ, MemLp w 2 → LogH1 φ φ' →
      ‖∫ t, w t * (φ' t - φ t / 2)‖ ≤
        (∫ t, ‖w t‖ ^ 2) ^ (1 / 2 : ℝ) * ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) :=
  log_fourier_plancherel

/-! ### Domain consumers -/

/-- ψ' - ψ/2 = e^(3t/2) h'(e^t) pointwise. -/
lemma shift_eq (h h' : ℝ → ℂ) (t : ℝ) :
    logUnitaryDeriv h h' t - logUnitary h t / 2 =
      (Real.exp (t / 2) : ℂ) * ((Real.exp t : ℂ) * h' (Real.exp t)) := by
  simp only [logUnitaryDeriv, logUnitary]; ring

/-- The roots fit together: the H¹ shift norm of ψ = U h is the log form of h. -/
theorem expected_shift_norm_eq_logForm (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    ∫ t, ‖logUnitaryDeriv h h' t - logUnitary h t / 2‖ ^ 2 = logForm h' := by
  obtain ⟨-, hU, -, -, hF, hH1⟩ := log_unitary_form_identity h h' hD
  rw [(log_fourier_plancherel.2.2.2.2.2.1) _ _ hH1, hU, hF]

/-- The form domain is non-degenerate: h(x) = e^(-x), h' = -e^(-x). -/
theorem expected_domain_nonempty :
    LogFormDomain (fun x => (Real.exp (-x) : ℂ)) (fun x => -(Real.exp (-x) : ℂ)) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (Real.exp (-x) : ℂ)) (-(Real.exp (-x) : ℂ)) x := by
    intro x
    have h := ((hasDerivAt_neg x).exp).ofReal_comp
    simpa using h
  have hcont : Continuous (fun x : ℝ => -(Real.exp (-x) : ℂ)) := by fun_prop
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)
  refine ⟨fun a b _ _ => ?_, fun a b _ _ => hcont.intervalIntegrable a b, hcont.measurable, ?_, ?_⟩
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable a b)]
  · refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_
    refine hint.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun x hx => ?_)))
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_
    refine (hint.const_mul 2).mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun x hx => ?_)))
    have hx0 : (0 : ℝ) < x := hx
    have hq : x ^ 2 ≤ 2 * Real.exp x := by
      have := Real.pow_div_factorial_le_exp x hx0.le 2
      norm_num [Nat.factorial] at this; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_real, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0,
      abs_of_pos (Real.exp_pos _), mul_pow, sq (Real.exp (-x)), ← Real.exp_add]
    calc x ^ 2 * Real.exp (-x + -x) ≤ 2 * Real.exp x * Real.exp (-x + -x) :=
          mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
      _ = 2 * Real.exp (-x) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-! ### The actual zero profile is in the form domain (paper S1.5) -/

/-- The explicit right derivative of the zero profile on (0, ∞). -/
def zeroProfileRightDeriv (ρ : ℂ) (x : ℝ) : ℂ := -(srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ)

lemma measurable_zeroProfileRightDeriv (ρ : ℂ) : Measurable (zeroProfileRightDeriv ρ) := by
  have hA : Measurable (fun x : ℝ => cellSumA ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumA ρ)).comp Nat.measurable_floor
  have hB : Measurable (fun x : ℝ => cellSumB ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumB ρ)).comp Nat.measurable_floor
  unfold zeroProfileRightDeriv srhoCellDeriv
  have h1 : Measurable (fun x : ℝ => (x : ℂ) ^ (-ρ - 1)) := Complex.measurable_ofReal.pow_const _
  have h2 : Measurable (fun x : ℝ => (x : ℂ) ^ (ρ - 1 - 1)) := Complex.measurable_ofReal.pow_const _
  exact (((measurable_const.mul h1).mul hA).sub ((measurable_const.mul h2).mul hB)).div_const _ |>.neg

lemma hasDerivWithinAt_zeroProfile_Ioi (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (zeroProfile ρ) (zeroProfileRightDeriv ρ x) (Ioi x) x := by
  by_cases hn : x ∈ Set.range (fun n : ℕ => (n : ℝ))
  · obtain ⟨m, rfl⟩ := hn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hx
      · exact h
    have h := hasDerivWithinAt_zeroProfile_right ρ hm
    rw [zeroProfileRightDeriv, Nat.floor_natCast]
    exact h.mono Ioi_subset_Ici_self
  · have hcell := mem_cell_of_not_nat hx hn
    exact (hasDerivAt_zeroProfile_cell ρ hcell).hasDerivWithinAt

lemma zeroProfileRightDeriv_bound {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖zeroProfileRightDeriv ρ x‖ ≤ C * min 1 (x ^ (-2 : ℝ)) := by
  set C := (‖2 * ρ - 1‖ + srhoDerivRemainderConst ρ) / ‖normalizationBrho ρ‖
  have hC0 : 0 ≤ C := by
    have : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
    positivity
  refine ⟨C, hC0, fun x hx => ?_⟩
  rw [zeroProfileRightDeriv, norm_neg]
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [Nat.floor_eq_zero.mpr hx1, srhoCellDeriv_zero, zero_div, norm_zero]
    exact mul_nonneg hC0 (le_min zero_le_one (Real.rpow_nonneg hx.le _))
  · have hcell : x ∈ Ico (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1) := ⟨Nat.floor_le hx.le, Nat.lt_floor_add_one x⟩
    have hb := zeroProfile_deriv_bound hz h0 h1 hcell hx1
    have hmin : min 1 (x ^ (-2 : ℝ)) = x ^ (-2 : ℝ) :=
      min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
    rw [hmin]; exact hb

/-- At an actual zero the zero profile, with its explicit right derivative, lies in the actual
log form domain. -/
theorem expected_zero_profile_in_form_domain {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : LogFormDomain (zeroProfile ρ) (zeroProfileRightDeriv ρ) := by
  obtain ⟨C, hC0, hC⟩ := zeroProfileRightDeriv_bound hz h0 h1
  have hm := measurable_zeroProfileRightDeriv ρ
  have hII : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (zeroProfileRightDeriv ρ) volume a b := by
    intro a b ha hb
    refine (intervalIntegrable_const (c := C)).mono_fun hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : 0 < x := by
      rcases le_total a b with hab | hab
      · rw [uIoc_of_le hab] at hx; linarith [hx.1]
      · rw [uIoc_of_ge hab] at hx; linarith [hx.1]
    refine (hC x hx0).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hC0]
    exact mul_le_of_le_one_right hC0 (min_le_left _ _)
  have hFTC : ∀ a b : ℝ, 0 < a → a ≤ b →
      zeroProfile ρ b - zeroProfile ρ a = ∫ x in a..b, zeroProfileRightDeriv ρ x := by
    intro a b ha hab
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
      ((continuous_zeroProfile ρ).continuousOn)
      (fun x hx => hasDerivWithinAt_zeroProfile_Ioi ρ (lt_trans ha hx.1))
      (hII a b ha (lt_of_lt_of_le ha hab))]
  refine ⟨fun a b ha hb => ?_, hII, hm, (memLp_two_zeroProfile hz h0 h1).restrict _, ?_⟩
  · rcases le_total a b with hab | hab
    · exact hFTC a b ha hab
    · rw [intervalIntegral.integral_symm, ← hFTC b a hb hab]; ring
  · set g : ℝ → ℝ := fun x => C * min x (x ^ (-1 : ℝ)) with hg
    have hgL : MemLp g 2 (volume.restrict (Ioi 0)) := by
      have hgm : Measurable g := by fun_prop
      refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
      have hdom : Integrable (fun x : ℝ => C ^ 2 * (Ioc 0 1).indicator (fun _ => (1 : ℝ)) x +
          C ^ 2 * (Ioi 1).indicator (fun x => x ^ (-2 : ℝ)) x) (volume.restrict (Ioi 0)) := by
        refine Integrable.add ?_ ?_
        · refine Integrable.const_mul ?_ _
          refine ((integrable_indicator_iff measurableSet_Ioc).mpr ?_).mono_measure
            Measure.restrict_le_self
          exact integrableOn_const (by simp) (by simp)
        · refine Integrable.const_mul ?_ _
          exact ((integrable_indicator_iff measurableSet_Ioi).mpr
            (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).mono_measure Measure.restrict_le_self
      refine hdom.mono' (hgm.pow_const 2).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg, mul_pow]
      rcases le_or_gt x 1 with hx1 | hx1
      · have hmin : min x (x ^ (-1 : ℝ)) = x := by
          refine min_eq_left ?_
          rw [Real.rpow_neg_one]; exact le_trans hx1 (one_le_inv₀ hx0 |>.mpr hx1)
        rw [hmin, indicator_of_mem (show x ∈ Ioc 0 1 from ⟨hx0, hx1⟩),
          indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx1), mul_zero, add_zero, mul_one]
        exact mul_le_of_le_one_right (sq_nonneg C) (by nlinarith)
      · have hmin : min x (x ^ (-1 : ℝ)) = x ^ (-1 : ℝ) := by
          refine min_eq_right ?_
          rw [Real.rpow_neg_one]; exact le_trans (inv_le_one_of_one_le₀ hx1.le) hx1.le
        rw [hmin, indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => absurd h.2 (not_le.mpr hx1)),
          indicator_of_mem (show x ∈ Ioi 1 from hx1), mul_zero, zero_add,
          ← Real.rpow_natCast (x ^ (-1 : ℝ)) 2, ← Real.rpow_mul hx0.le]
        norm_num
    refine hgL.of_le ((Complex.measurable_ofReal.mul hm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC0 (le_min hx0.le (Real.rpow_nonneg hx0.le _)))]
    calc x * ‖zeroProfileRightDeriv ρ x‖ ≤ x * (C * min 1 (x ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hC x hx0) hx0.le
      _ = C * min x (x ^ (-1 : ℝ)) := by
          rw [show x * (C * min 1 (x ^ (-2 : ℝ))) = C * (min 1 (x ^ (-2 : ℝ)) * x) by ring,
            min_mul_of_nonneg _ _ hx0.le, one_mul,
            show x ^ (-2 : ℝ) * x = x ^ (-1 : ℝ) by
              rw [← Real.rpow_add_one hx0.ne']; norm_num]

/-- Paper S1.5 for the actual zero profile: ∫_0^∞ x²|h'|² = ∫ |ψ'|² + (1/4) ∫_0^∞ |h|². -/
theorem expected_zero_profile_form_identity {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    logForm (zeroProfileRightDeriv ρ) =
      (∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileRightDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ x in Ioi 0, ‖zeroProfile ρ x‖ ^ 2 :=
  (log_unitary_form_identity _ _ (expected_zero_profile_in_form_domain hz h0 h1)).2.2.2.2.1

end OPICALogFourierSobolevIndependent
#print axioms Zeta23.OPICAFollowup.log_unitary_form_identity
#print axioms Zeta23.OPICAFollowup.log_fourier_plancherel
#print axioms OPICALogFourierSobolevIndependent.audit_logFourier
#print axioms OPICALogFourierSobolevIndependent.audit_logFormDomain
#print axioms OPICALogFourierSobolevIndependent.expected_log_unitary_form_identity
#print axioms OPICALogFourierSobolevIndependent.expected_log_fourier_plancherel
#print axioms OPICALogFourierSobolevIndependent.expected_shift_norm_eq_logForm
#print axioms OPICALogFourierSobolevIndependent.expected_domain_nonempty
#print axioms OPICALogFourierSobolevIndependent.expected_zero_profile_in_form_domain
#print axioms OPICALogFourierSobolevIndependent.expected_zero_profile_form_identity
