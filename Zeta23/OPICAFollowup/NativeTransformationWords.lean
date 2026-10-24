import Zeta23.OPICAFollowup.NativeFilters
import Zeta23.OPICA.LocalObstruction
import Mathlib.Analysis.Meromorphic.Order

/-! Finite products of the concrete native generators. The algebraic helpers
below retain every affine addition. Physical transform and native pole roots
require the actual causal-state and source adapters in addition to this algebra. -/

noncomputable section
open Filter Complex Set MeasureTheory
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup

abbrev NativeWord := List NativeGenerator

/-- Independently established analytic continuation of an actual causal
history. The connecting domain prevents patching unrelated values near the pole
onto an integral identity on a distant half-plane. No preservation, pole,
coefficient, rate, or range conclusion is a field of this input. -/
structure NativeAnalyticHistory (center : ℂ) where
  state : NativeCausalState
  continuation : ℂ → ℂ
  safeThreshold : ℝ
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  center_mem : center ∈ domain
  safe_mem : ∀ z : ℂ, safeThreshold < z.re → z ∈ domain
  analytic : AnalyticOnNhd ℂ continuation domain
  initial_integrable : ∀ term ∈ state, ∀ z : ℂ, safeThreshold < z.re →
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)
  initial_identity : ∀ z : ℂ, safeThreshold < z.re → continuation z = state.laplace z

/-- Compact smooth causal histories supply the general certificate
constructively on the entire complex plane. -/
def NativeCompactHistory.analyticHistory (history : NativeCompactHistory) (center : ℂ) :
    NativeAnalyticHistory center where
  state := history.toCausalState
  continuation := history.laplace
  safeThreshold := 0
  domain := univ
  domain_open := isOpen_univ
  domain_connected := isConnected_univ
  center_mem := mem_univ _
  safe_mem := fun z _ => mem_univ z
  analytic := fun z _ => history.laplace_analyticAt z
  initial_integrable := by
    intro term hterm z _
    simp only [NativeCompactHistory.toCausalState, List.mem_singleton] at hterm
    subst term
    exact history.laplace_integrable z
  initial_identity := fun z _ => (history.toCausalState_laplace z).symm

lemma NativeAnalyticHistory.analyticAt {center : ℂ} (history : NativeAnalyticHistory center) :
    AnalyticAt ℂ history.continuation center := history.analytic center history.center_mem

/-- Analytic continuation on the connected domain is fixed by the actual
initial transform. A separately patched analytic germ cannot satisfy this
domain certificate with a different value. -/
lemma NativeAnalyticHistory.continuation_unique {center : ℂ}
    (history : NativeAnalyticHistory center) {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B history.domain)
    (hactual : ∀ z : ℂ, history.safeThreshold < z.re → B z = history.state.laplace z) :
    EqOn history.continuation B history.domain := by
  let z0 : ℂ := (history.safeThreshold+1 : ℝ)
  have hz0 : history.safeThreshold < z0.re := by
    simp only [z0, Complex.ofReal_re]
    linarith
  have hopen : IsOpen {z : ℂ | history.safeThreshold < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : history.continuation =ᶠ[𝓝 z0] B := by
    filter_upwards [hopen.mem_nhds hz0] with z hz
    exact (history.initial_identity z hz).trans (hactual z hz).symm
  exact history.analytic.eqOn_of_preconnected_of_eventuallyEq hB
    history.domain_connected.isPreconnected (history.safe_mem z0 hz0) heq

/-- Every correction retains its actual physical state and independently
proved continuation, including any weak endpoint derivative terms. -/
abbrev NativeWordHistory (center : ℂ) := ℕ → NativeAnalyticHistory center

/-- A finite, explicit common initial half-plane for all histories actually
used by this word. This is a domain threshold, not an asymptotic rate claim. -/
def wordHistorySafeThreshold {center : ℂ} (w : NativeWord)
    (history : NativeWordHistory center) : ℝ :=
  ∑ i ∈ Finset.range w.length, max 0 (history i).safeThreshold

lemma wordHistory_threshold_le {center : ℂ} (w : NativeWord)
    (history : NativeWordHistory center) {i : ℕ} (hi : i < w.length) :
    (history i).safeThreshold ≤ wordHistorySafeThreshold w history := by
  exact (le_max_right 0 _).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (history j).safeThreshold)
      (Finset.mem_range.mpr hi))

lemma wordHistory_actual_initial_identity {center : ℂ} (w : NativeWord)
    (history : NativeWordHistory center) {z : ℂ}
    (hz : wordHistorySafeThreshold w history < z.re) {i : ℕ} (hi : i < w.length) :
    (history i).continuation z = (history i).state.laplace z :=
  (history i).initial_identity z (lt_of_le_of_lt (wordHistory_threshold_le w history hi) hz)

/-- Individually connected continuation domains need not have a connected
intersection. A physical word therefore retains an independently established
common domain for all active histories; it is not inferred from their separate
certificates. -/
structure NativeWordHistoryContinuationDomain {center : ℂ} (w : NativeWord)
    (history : NativeWordHistory center) where
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  center_mem : center ∈ domain
  safeThreshold : ℝ
  threshold_le : wordHistorySafeThreshold w history ≤ safeThreshold
  safe_mem : ∀ z : ℂ, safeThreshold < z.re → z ∈ domain
  active_analytic : ∀ i, i < w.length → AnalyticOnNhd ℂ (history i).continuation domain

def NativeWordHistoryContinuationDomain.activeHistory {center : ℂ} {w : NativeWord}
    {history : NativeWordHistory center} (D : NativeWordHistoryContinuationDomain w history)
    (i : ℕ) (hi : i < w.length) : NativeAnalyticHistory center where
  state := (history i).state
  continuation := (history i).continuation
  safeThreshold := D.safeThreshold
  domain := D.domain
  domain_open := D.domain_open
  domain_connected := D.domain_connected
  center_mem := D.center_mem
  safe_mem := D.safe_mem
  analytic := D.active_analytic i hi
  initial_integrable := fun term hterm z hz =>
    (history i).initial_integrable term hterm z
      (lt_of_le_of_lt ((wordHistory_threshold_le w history hi).trans D.threshold_le) hz)
  initial_identity := fun z hz => wordHistory_actual_initial_identity w history (z := z)
    (lt_of_le_of_lt D.threshold_le hz) hi

/-- A family of actual compact histories supplies the joint domain univ. -/
def NativeCompactHistory.wordContinuationDomain (w : NativeWord)
    (history : ℕ → NativeCompactHistory) (center : ℂ) :
    NativeWordHistoryContinuationDomain w (fun i => (history i).analyticHistory center) where
  domain := univ
  domain_open := isOpen_univ
  domain_connected := isConnected_univ
  center_mem := mem_univ _
  safeThreshold := wordHistorySafeThreshold w (fun i => (history i).analyticHistory center)
  threshold_le := le_rfl
  safe_mem := fun z _ => mem_univ z
  active_analytic := fun i _ z _ => (history i).laplace_analyticAt z

def wordCompletionCount : NativeWord → ℕ
  | [] => 0
  | g :: w => g.completionCount + wordCompletionCount w

def wordUnitFactor : NativeWord → ℂ → ℂ
  | [], _ => 1
  | g :: w, z => g.unitMultiplier z * wordUnitFactor w z

def wordMultiplier : NativeWord → ℂ → ℂ
  | [], _ => 1
  | g :: w, z => g.multiplier z * wordMultiplier w z

lemma wordUnitFactor_analytic (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    AnalyticAt ℂ (wordUnitFactor w) ((rho : ℂ)-1/2) := by
  induction w with
  | nil => exact analyticAt_const
  | cons g w ih => exact (g.unit_analytic rho hright).mul ih

lemma wordUnitFactor_ne_zero (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    wordUnitFactor w ((rho : ℂ)-1/2) ≠ 0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons g w ih => exact mul_ne_zero (g.unit_ne_zero rho hright) ih

/-- Leading-value cost uses the explicit concrete multiplier formulas. It says
nothing about a global operator norm or derivatives away from the pole. -/
def wordUnitLogCost (w : NativeWord) (c : ℂ) : ℝ :=
  (w.map fun g => |Real.log ‖g.unitMultiplier c‖|).sum

lemma wordUnitFactor_log_norm (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    Real.log ‖wordUnitFactor w ((rho : ℂ)-1/2)‖ =
      (w.map fun g => Real.log ‖g.unitMultiplier ((rho : ℂ)-1/2)‖).sum := by
  induction w with
  | nil => simp [wordUnitFactor]
  | cons g w ih =>
    rw [wordUnitFactor, norm_mul, Real.log_mul
      (norm_ne_zero_iff.mpr (g.unit_ne_zero rho hright))
      (norm_ne_zero_iff.mpr (wordUnitFactor_ne_zero w rho hright)), ih]
    rfl

lemma wordUnitFactor_abs_log_norm_le (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    |Real.log ‖wordUnitFactor w ((rho : ℂ)-1/2)‖| ≤ wordUnitLogCost w ((rho : ℂ)-1/2) := by
  rw [wordUnitFactor_log_norm w rho hright]
  unfold wordUnitLogCost
  induction w with
  | nil => simp
  | cons g w ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

lemma sourceDerivative_unit_log_cost (d : ℕ) (c : ℂ) :
    |Real.log ‖(NativeGenerator.sourceDerivative d).unitMultiplier c‖| =
      (d : ℝ)*|Real.log ‖c^2-1/4‖| := by
  change |Real.log ‖(c^2-1/4)^d‖| = _
  rw [norm_pow, Real.log_pow, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]

lemma delay_unit_log_cost (tau : ℝ) (htau : 0 ≤ tau) (c : ℂ) :
    |Real.log ‖(NativeGenerator.delay tau htau).unitMultiplier c‖| = tau*|c.re| := by
  change |Real.log ‖Complex.exp (-(tau : ℂ)*c)‖| = _
  rw [Complex.norm_exp, Real.log_exp]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, abs_neg, abs_mul, abs_of_nonneg htau]

lemma delay_unit_log_cost_at_right_zero (tau : ℝ) (htau : 0 ≤ tau)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    |Real.log ‖(NativeGenerator.delay tau htau).unitMultiplier ((rho : ℂ)-1/2)‖| =
      tau*((rho : ℂ).re-1/2) := by
  have hc : ((rho : ℂ)-1/2).re = (rho : ℂ).re-1/2 := by norm_num
  rw [delay_unit_log_cost, hc, abs_of_pos (sub_pos.mpr hright)]

lemma inverseEuler_unit_log_cost (Q : ℕ) (hQ : 0 < Q) (c : ℂ) :
    |Real.log ‖(NativeGenerator.inverseFiniteEuler Q hQ).unitMultiplier c‖| =
      |Real.log ‖finiteEulerMultiplier Q c‖| := by
  change |Real.log ‖(finiteEulerMultiplier Q c)⁻¹‖| = _
  rw [norm_inv, Real.log_inv, abs_neg]

lemma finiteEuler_unit_log_value (Q : ℕ) (hQ : 0 < Q)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    Real.log ‖(NativeGenerator.finiteEuler Q hQ).unitMultiplier ((rho : ℂ)-1/2)‖ =
      ∑ p ∈ Q.primeFactors, Real.log ‖1-Complex.exp (-(rho : ℂ)*(Real.log p : ℂ))‖ := by
  have hn := finiteEulerMultiplier_ne_zero_at_right_zero Q rho hright
  unfold finiteEulerMultiplier at hn
  simp only [sub_add_cancel] at hn
  change Real.log ‖finiteEulerMultiplier Q ((rho : ℂ)-1/2)‖ = _
  unfold finiteEulerMultiplier
  simp only [sub_add_cancel, norm_prod]
  exact Real.log_prod (fun p hp => norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mp hn p hp))

lemma abs_log_norm_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    |Real.log ‖1-z‖| ≤ -Real.log (1-‖z‖) := by
  have hp : 0 < 1-‖z‖ := by linarith
  have hlo : 1-‖z‖ ≤ ‖1-z‖ := by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) z
  have hup : ‖1-z‖ ≤ 1/(1-‖z‖) := by
    have hbase : ‖1-z‖ ≤ 1+‖z‖ := by simpa only [norm_one] using norm_sub_le (1 : ℂ) z
    refine hbase.trans ?_
    apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg ‖z‖]
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa only [neg_neg] using Real.log_le_log hp hlo
  · simpa only [one_div, Real.log_inv] using Real.log_le_log (hp.trans_le hlo) hup

lemma neg_log_one_sub_le_cost {t q : ℝ} (ht : 0 ≤ t) (htq : t ≤ q) (hq : q < 1) :
    -Real.log (1-t) ≤ (1-q)⁻¹*t := by
  have hp : 0 < 1-t := by linarith
  have hqp : 0 < 1-q := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hlog
  have hinv : (1-t)⁻¹ ≤ (1-q)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hqp (by linarith : 1-q ≤ 1-t)
  calc
    -Real.log (1-t) ≤ (1-t)⁻¹-1 := hlog
    _ = t*(1-t)⁻¹ := by field_simp; ring
    _ ≤ t*(1-q)⁻¹ := mul_le_mul_of_nonneg_left hinv ht
    _ = (1-q)⁻¹*t := mul_comm _ _

/-- Explicit paper bound with `C_sigma=(1-2^(-sigma))^-1`. The exponential
summand is exactly `p^(-sigma)` for each positive prime p. -/
lemma finiteEuler_unit_log_cost_le (Q : ℕ) (hQ : 0 < Q)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    |Real.log ‖(NativeGenerator.finiteEuler Q hQ).unitMultiplier ((rho : ℂ)-1/2)‖| ≤
      (1-Real.exp (-(rho : ℂ).re*Real.log 2))⁻¹ *
        ∑ p ∈ Q.primeFactors, Real.exp (-(rho : ℂ).re*Real.log p) := by
  let q := Real.exp (-(rho : ℂ).re*Real.log 2)
  have hsigma : 0 < (rho : ℂ).re := lt_trans (by norm_num) hright
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hq : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos hsigma hlog2]
  have hterm (p : ℕ) (hp : p ∈ Q.primeFactors) :
      |Real.log ‖1-Complex.exp (-(rho : ℂ)*(Real.log p : ℂ))‖| ≤
        (1-q)⁻¹*Real.exp (-(rho : ℂ).re*Real.log p) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hlog : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
    have htq : Real.exp (-(rho : ℂ).re*Real.log p) ≤ q := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hlog hsigma.le]
    have hnorm : ‖Complex.exp (-(rho : ℂ)*(Real.log p : ℂ))‖ =
        Real.exp (-(rho : ℂ).re*Real.log p) := by
      rw [Complex.norm_exp]
      congr 1
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    have hnq : ‖Complex.exp (-(rho : ℂ)*(Real.log p : ℂ))‖ ≤ q := by
      rw [hnorm]
      exact htq
    simpa only [hnorm] using
      (abs_log_norm_one_sub_le (lt_of_le_of_lt hnq hq)).trans
        (neg_log_one_sub_le_cost (norm_nonneg _) hnq hq)
  rw [finiteEuler_unit_log_value Q hQ rho hright]
  change |∑ p ∈ Q.primeFactors, Real.log ‖1-Complex.exp (-(rho : ℂ)*(Real.log p : ℂ))‖| ≤
    (1-q)⁻¹*∑ p ∈ Q.primeFactors, Real.exp (-(rho : ℂ).re*Real.log p)
  calc
    _ ≤ ∑ p ∈ Q.primeFactors, |Real.log ‖1-Complex.exp (-(rho : ℂ)*(Real.log p : ℂ))‖| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Q.primeFactors, (1-q)⁻¹*Real.exp (-(rho : ℂ).re*Real.log p) :=
      Finset.sum_le_sum (fun p hp => hterm p hp)
    _ = (1-q)⁻¹*∑ p ∈ Q.primeFactors, Real.exp (-(rho : ℂ).re*Real.log p) := by
      rw [Finset.mul_sum]

lemma prime_decay_exp_eq_rpow (p : ℕ) (hp : p.Prime) (sigma : ℝ) :
    Real.exp (-sigma*Real.log p) = (p : ℝ)^(-sigma) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p)]
  congr 1
  ring

lemma finiteEuler_unit_log_cost_le_rpow (Q : ℕ) (hQ : 0 < Q)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    |Real.log ‖(NativeGenerator.finiteEuler Q hQ).unitMultiplier ((rho : ℂ)-1/2)‖| ≤
      (1-(2 : ℝ)^(-(rho : ℂ).re))⁻¹ *
        ∑ p ∈ Q.primeFactors, (p : ℝ)^(-(rho : ℂ).re) := by
  have hc : Real.exp (-(rho : ℂ).re*Real.log (2 : ℝ)) =
      (2 : ℝ)^(-(rho : ℂ).re) := by
    simpa using prime_decay_exp_eq_rpow 2 Nat.prime_two (rho : ℂ).re
  have hs : (∑ p ∈ Q.primeFactors, Real.exp (-(rho : ℂ).re*Real.log p)) =
      ∑ p ∈ Q.primeFactors, (p : ℝ)^(-(rho : ℂ).re) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact prime_decay_exp_eq_rpow p (Nat.prime_of_mem_primeFactors hp) _
  simpa only [hc, hs] using finiteEuler_unit_log_cost_le Q hQ rho hright

lemma inverseEuler_unit_log_cost_le_rpow (Q : ℕ) (hQ : 0 < Q)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    |Real.log ‖(NativeGenerator.inverseFiniteEuler Q hQ).unitMultiplier ((rho : ℂ)-1/2)‖| ≤
      (1-(2 : ℝ)^(-(rho : ℂ).re))⁻¹ *
        ∑ p ∈ Q.primeFactors, (p : ℝ)^(-(rho : ℂ).re) := by
  rw [inverseEuler_unit_log_cost]
  exact finiteEuler_unit_log_cost_le_rpow Q hQ rho hright

lemma rational_unit_log_value (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    Real.log ‖(NativeGenerator.rational a b ha hb).unitMultiplier ((rho : ℂ)-1/2)‖ =
      Real.log ‖(rho : ℂ)-1/2+(a : ℂ)‖-Real.log ‖(rho : ℂ)-1/2+(b : ℂ)‖ := by
  change Real.log ‖((rho : ℂ)-1/2+(a : ℂ))/((rho : ℂ)-1/2+(b : ℂ))‖ = _
  rw [norm_div, Real.log_div
    (norm_ne_zero_iff.mpr (right_zero_add_positive_ne_zero rho hright ha))
    (norm_ne_zero_iff.mpr (right_zero_add_positive_ne_zero rho hright hb))]

lemma inverseRational_unit_log_value (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    Real.log ‖(NativeGenerator.inverseRational a b ha hb).unitMultiplier ((rho : ℂ)-1/2)‖ =
      Real.log ‖(rho : ℂ)-1/2+(b : ℂ)‖-Real.log ‖(rho : ℂ)-1/2+(a : ℂ)‖ :=
  rational_unit_log_value b a hb ha rho hright

lemma residualPower_unit_log_cost (Y r : ℕ) (rho : Zeta23.zetaZeroConfig.carrier) :
    |Real.log ‖(NativeGenerator.residualPower Y r).unitMultiplier ((rho : ℂ)-1/2)‖| = 0 := by
  change |Real.log ‖(NativeGenerator.residualPower Y r).multiplier ((rho : ℂ)-1/2)‖| = 0
  rw [NativeGenerator.residual_value_one, norm_one, Real.log_one, abs_zero]

lemma completion_unit_norm (c : ℂ) :
    ‖NativeGenerator.completion.unitMultiplier c‖ =
      ‖c-1/2‖/(‖c+1/2‖*‖c+3/2‖) := by
  change ‖Zeta23.CCM.nativeCompletionRationalMultiplier c‖ = _
  rw [Zeta23.CCM.nativeCompletionRationalMultiplier, norm_div, norm_mul]

lemma factorial_jet_log_cost (k : ℕ) {a : ℂ} (ha : a ≠ 0) :
    Real.log ‖(k.factorial : ℂ)*a‖-Real.log ‖a‖ = Real.log (k.factorial : ℝ) := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [norm_mul, Complex.norm_natCast, Real.log_mul hfac (norm_ne_zero_iff.mpr ha)]
  ring

lemma factorial_jet_log_cost_le (k : ℕ) :
    Real.log (k.factorial : ℝ) ≤ (k : ℝ)*Real.log ((k : ℝ)+2) := by
  have hb : (k.factorial : ℝ) ≤ ((k : ℝ)+2)^k := by
    exact_mod_cast (Nat.factorial_le_pow k).trans
      (Nat.pow_le_pow_left (by omega : k ≤ k+2) k)
  have hpos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  simpa only [Real.log_pow] using Real.log_le_log hpos hb

/-- Exact product of the actual generator multipliers. Completion count and
source derivative order are separate parameters. -/
lemma wordMultiplier_eq_unit_zeta (w : NativeWord) (z : ℂ) :
    wordMultiplier w z =
      wordUnitFactor w z * riemannZeta (z+1/2) ^ wordCompletionCount w := by
  induction w with
  | nil => simp [wordMultiplier, wordUnitFactor, wordCompletionCount]
  | cons g w ih =>
    simp only [wordMultiplier, wordUnitFactor, wordCompletionCount]
    rw [g.multiplier_eq_unit_zeta, ih, pow_add]
    ring

/-- Apply the concrete generators in list order, retaining the separately
identified affine history transform at each step. -/
def wordAffineTransform : NativeWord → (ℕ → ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ
  | [], _, f => f
  | g :: w, B, f => wordAffineTransform w (fun i => B (i+1))
      (fun z => g.multiplier z*f z+B 0 z)

def wordAlgebraCorrection (w : NativeWord) (B : ℕ → ℂ → ℂ) : ℂ → ℂ :=
  wordAffineTransform w B 0

/-- The correction is constructed from all actual history Laplace integrals.
Convergence and continuation remain explicit obligations of a physical consumer. -/
def wordCorrection {center : ℂ} (w : NativeWord) (history : NativeWordHistory center) : ℂ → ℂ :=
  wordAlgebraCorrection w (fun i => (history i).continuation)

lemma nativeGenerator_multiplier_analytic (g : NativeGenerator)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    AnalyticAt ℂ g.multiplier ((rho : ℂ)-1/2) := by
  have heq : g.multiplier = fun z =>
      g.unitMultiplier z*riemannZeta (z+1/2)^g.completionCount :=
    funext g.multiplier_eq_unit_zeta
  rw [heq]
  exact (g.unit_analytic rho hright).mul ((shiftedZeta_analyticAt_right_zero rho).pow _)

lemma wordAffineTransform_analytic (w : NativeWord) (B : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re)
    (hf : AnalyticAt ℂ f ((rho : ℂ)-1/2))
    (hB : ∀ i, AnalyticAt ℂ (B i) ((rho : ℂ)-1/2)) :
    AnalyticAt ℂ (wordAffineTransform w B f) ((rho : ℂ)-1/2) := by
  induction w generalizing B f with
  | nil => exact hf
  | cons g w ih =>
    apply ih
    · exact ((nativeGenerator_multiplier_analytic g rho hright).mul hf).add (hB 0)
    · intro i
      exact hB (i+1)

lemma wordCorrection_analytic (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) (history : NativeWordHistory ((rho : ℂ)-1/2)) :
    AnalyticAt ℂ (wordCorrection w history) ((rho : ℂ)-1/2) :=
  wordAffineTransform_analytic w (fun i => (history i).continuation) 0 rho hright
    analyticAt_const (fun i => (history i).analyticAt)

/-- This identity concerns the concrete generator list and every displayed
addition; it is an algebraic helper, not a physical transform assertion. -/
lemma wordAffineTransform_sub (w : NativeWord) (B : ℕ → ℂ → ℂ)
    (f h : ℂ → ℂ) (z : ℂ) :
    wordAffineTransform w B f z-wordAffineTransform w B h z =
      wordMultiplier w z*(f z-h z) := by
  induction w generalizing B f h with
  | nil => simp [wordAffineTransform, wordMultiplier]
  | cons g w ih =>
    simp only [wordAffineTransform, wordMultiplier]
    rw [ih]
    ring

lemma wordAffineTransform_corrected (w : NativeWord) (B : ℕ → ℂ → ℂ)
    (f : ℂ → ℂ) (z : ℂ) :
    wordAffineTransform w B f z-wordAlgebraCorrection w B z =
      wordUnitFactor w z * riemannZeta (z+1/2) ^ wordCompletionCount w * f z := by
  simpa only [wordAlgebraCorrection, Pi.zero_apply, sub_zero, wordMultiplier_eq_unit_zeta]
    using wordAffineTransform_sub w B f 0 z

/-- Actual top derivative of an analytic monomial factor, with its factorial. -/
lemma analyticMonomial_topDerivative {U : ℂ → ℂ} {c : ℂ} (k : ℕ)
    (hU : AnalyticAt ℂ U c) :
    iteratedDeriv k (fun z => (z-c)^k*U z) c = (k.factorial : ℂ)*U c := by
  have hp : AnalyticAt ℂ (fun z : ℂ => (z-c)^k) c := by fun_prop
  have hd (n : ℕ) : iteratedDeriv n (fun z : ℂ => (z-c)^k) c =
      if n = k then (k.factorial : ℂ) else 0 := by
    simpa using congrFun (iteratedDeriv_comp_sub_const n (fun z : ℂ => z^k) c) c
      |>.trans (by simpa using (iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := n) (m := k)))
  have heq : (fun z => (z-c)^k*U z) = fun z => U z*(z-c)^k := by
    funext z
    ring
  rw [heq, iteratedDeriv_fun_mul hU.contDiffAt hp.contDiffAt, Finset.sum_eq_single 0]
  · simp [hd]
    ring
  · intro i hi hne
    have hi_le := Finset.mem_range.mp hi
    rw [hd, if_neg (by omega : k-i ≠ k), mul_zero]
  · simp

lemma multiplierOrder_unit_value {c : ℂ} (M : Zeta23.OPICA.MultiplierOrderData c) :
    M.unit c = iteratedDeriv M.order M.multiplier c/(M.order.factorial : ℂ) := by
  have hd := Filter.EventuallyEq.iteratedDeriv_eq M.order M.multiplier_eq
  rw [analyticMonomial_topDerivative M.order M.unit_analytic] at hd
  have hfac : (M.order.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M.order
  apply (eq_div_iff hfac).mpr
  simpa only [mul_comm] using hd.symm

/-- The unit is chosen from the actual shifted zeta function and its proved
multiplicity, rather than supplied as a factorization hypothesis. -/
def nativeShiftedZetaOrderData (rho : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.OPICA.MultiplierOrderData ((rho : ℂ)-1/2) :=
  let hfact := (shiftedZeta_analyticAt_right_zero rho).analyticOrderAt_eq_natCast.mp
    (shiftedZeta_actual_order rho)
  { multiplier := fun z => riemannZeta (z+1/2)
    order := zeroMult (rho : ℂ)
    unit := Classical.choose hfact
    unit_analytic := (Classical.choose_spec hfact).1
    unit_ne_zero := (Classical.choose_spec hfact).2.1
    multiplier_eq := (Classical.choose_spec hfact).2.2 }

lemma nativeShiftedZetaOrderData_unit_value (rho : Zeta23.zetaZeroConfig.carrier) :
    (nativeShiftedZetaOrderData rho).unit ((rho : ℂ)-1/2) =
      iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rho : ℂ)/
        ((zeroMult (rho : ℂ)).factorial : ℂ) := by
  have hv := multiplierOrder_unit_value (nativeShiftedZetaOrderData rho)
  change (nativeShiftedZetaOrderData rho).unit ((rho : ℂ)-1/2) =
    iteratedDeriv (zeroMult (rho : ℂ)) (fun z => riemannZeta (z+1/2)) ((rho : ℂ)-1/2)/
      ((zeroMult (rho : ℂ)).factorial : ℂ) at hv
  simpa only [iteratedDeriv_comp_add_const, sub_add_cancel] using hv

/-- Order data for the actual finite multiplier product, constructed from each
concrete generator's proved unit and the actual zeta multiplicity. -/
def wordMultiplierOrderData (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    Zeta23.OPICA.MultiplierOrderData ((rho : ℂ)-1/2) where
  multiplier := wordMultiplier w
  order := wordCompletionCount w * zeroMult (rho : ℂ)
  unit := fun z => wordUnitFactor w z *
    (nativeShiftedZetaOrderData rho).unit z ^ wordCompletionCount w
  unit_analytic := (wordUnitFactor_analytic w rho hright).mul
    ((nativeShiftedZetaOrderData rho).unit_analytic.pow _)
  unit_ne_zero := mul_ne_zero (wordUnitFactor_ne_zero w rho hright)
    (pow_ne_zero _ (nativeShiftedZetaOrderData rho).unit_ne_zero)
  multiplier_eq := by
    filter_upwards [(nativeShiftedZetaOrderData rho).multiplier_eq] with z hz
    change riemannZeta (z+1/2) =
      (z-((rho : ℂ)-1/2)) ^ zeroMult (rho : ℂ) *
        (nativeShiftedZetaOrderData rho).unit z at hz
    have hp : ((z-((rho : ℂ)-1/2)) ^ zeroMult (rho : ℂ)) ^ wordCompletionCount w =
        (z-((rho : ℂ)-1/2)) ^ (wordCompletionCount w * zeroMult (rho : ℂ)) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [wordMultiplier_eq_unit_zeta, hz, mul_pow, hp]
    ring

lemma wordMultiplierOrderData_unit_value (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    (wordMultiplierOrderData w rho hright).unit ((rho : ℂ)-1/2) =
      wordUnitFactor w ((rho : ℂ)-1/2) *
        (iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rho : ℂ)/
          ((zeroMult (rho : ℂ)).factorial : ℂ)) ^ wordCompletionCount w := by
  change wordUnitFactor w ((rho : ℂ)-1/2) *
    (nativeShiftedZetaOrderData rho).unit ((rho : ℂ)-1/2) ^ wordCompletionCount w = _
  rw [nativeShiftedZetaOrderData_unit_value]

lemma wordMultiplierOrderData_log_cost (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    |Real.log ‖(wordMultiplierOrderData w rho hright).unit ((rho : ℂ)-1/2)‖| ≤
      wordUnitLogCost w ((rho : ℂ)-1/2) +
        (wordCompletionCount w : ℝ)*
          |Real.log ‖(nativeShiftedZetaOrderData rho).unit ((rho : ℂ)-1/2)‖| := by
  change |Real.log ‖wordUnitFactor w ((rho : ℂ)-1/2) *
    (nativeShiftedZetaOrderData rho).unit ((rho : ℂ)-1/2) ^ wordCompletionCount w‖| ≤ _
  rw [norm_mul, norm_pow, Real.log_mul
    (norm_ne_zero_iff.mpr (wordUnitFactor_ne_zero w rho hright))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (nativeShiftedZetaOrderData rho).unit_ne_zero)),
    Real.log_pow]
  refine (abs_add_le _ _).trans (add_le_add (wordUnitFactor_abs_log_norm_le w rho hright) ?_)
  simp only [abs_mul, abs_of_nonneg
    (show (0 : ℝ) ≤ (wordCompletionCount w : ℝ) from Nat.cast_nonneg _), le_refl]

/-- The pole datum's actual punctured identity supplies meromorphy; no assertion
about an unrelated source is included. -/
lemma simplePoleData_meromorphicAt {Source : Type*} (s : Zeta23.OPICA.SimplePoleData Source) :
    MeromorphicAt s.field s.center := by
  have h : MeromorphicAt (fun z => s.residue/(z-s.center)+s.remainder z) s.center :=
    ((MeromorphicAt.const s.residue s.center).div
      (analyticAt_id.sub analyticAt_const).meromorphicAt).add s.remainder_analytic.meromorphicAt
  exact h.congr s.field_eq.symm

/-- Integer powers retain the zero-completion residue case in the same formula
as positive-completion regular representatives. -/
lemma simplePole_multiplier_germ_factorization {Source : Type*}
    (s : Zeta23.OPICA.SimplePoleData Source) (M : Zeta23.OPICA.MultiplierOrderData s.center) :
    (fun z => M.multiplier z*s.field z) =ᶠ[𝓝[≠] s.center]
      fun z => (z-s.center)^((M.order : ℤ)-1)*
        (M.unit z*(s.residue+(z-s.center)*s.remainder z)) := by
  filter_upwards [s.field_eq, M.multiplier_eq.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hf hM hz
  have hx : z-s.center ≠ 0 := sub_ne_zero.mpr hz
  rw [hf, hM, zpow_sub₀ hx, zpow_natCast, zpow_one]
  field_simp

lemma simplePole_multiplier_meromorphic_order {Source : Type*}
    (s : Zeta23.OPICA.SimplePoleData Source) (M : Zeta23.OPICA.MultiplierOrderData s.center) :
    meromorphicOrderAt (fun z => M.multiplier z*s.field z) s.center =
      ((M.order : ℤ)-1 : ℤ) := by
  have hf := (Zeta23.OPICA.multiplier_analytic M).meromorphicAt.mul
    (simplePoleData_meromorphicAt s)
  apply (meromorphicOrderAt_eq_int_iff hf).mpr
  refine ⟨fun z => M.unit z*(s.residue+(z-s.center)*s.remainder z),
    M.unit_analytic.mul (analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul s.remainder_analytic)), ?_, ?_⟩
  · simpa using mul_ne_zero M.unit_ne_zero s.residue_ne_zero
  · simpa only [smul_eq_mul, Pi.mul_apply, Filter.EventuallyEq]
      using simplePole_multiplier_germ_factorization s M



/-- Re-index the proved actual pole at its proved literal center. This is not
a caller-supplied pole; its remainder is taken from nativePrimePoleData. -/
def nativeWordPrimePole (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) : Zeta23.OPICA.SimplePoleData (ℝ → ℝ) where
  source := Zeta23.CCM.nativeOriginalSource
  center := (rho:ℂ)-1/2
  field := nativePrimeTransformGerm
  residue := -(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)
  residue_ne_zero := by
    simpa only [nativePrimePoleData_residue rho hright] using
      (nativePrimePoleData rho hright).residue_ne_zero
  remainder := (nativePrimePoleData rho hright).remainder
  remainder_analytic := by
    simpa only [nativePrimePoleData_center rho hright] using
      (nativePrimePoleData rho hright).remainder_analytic
  field_eq := by
    simpa only [nativePrimePoleData_field rho hright,nativePrimePoleData_center rho hright,
      nativePrimePoleData_residue rho hright] using (nativePrimePoleData rho hright).field_eq

def nativeWordTransformedField (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) : ℂ → ℂ :=
  wordAffineTransform w (fun i => (history i).continuation) nativePrimeTransformGerm

def nativeWordCorrectedField (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) : ℂ → ℂ :=
  fun z => nativeWordTransformedField w rho history z-wordCorrection w history z

lemma nativeWordCorrectedField_eq_product (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (history : NativeWordHistory ((rho:ℂ)-1/2)) (z : ℂ) :
    nativeWordCorrectedField w rho history z=wordMultiplier w z*nativePrimeTransformGerm z := by
  simpa only [nativeWordCorrectedField,nativeWordTransformedField,wordCorrection,
    wordAlgebraCorrection,Pi.zero_apply,sub_zero] using
    wordAffineTransform_sub w (fun i => (history i).continuation) nativePrimeTransformGerm 0 z

def nativeWordLeadingCoefficient (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  -(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)*
    wordUnitFactor w ((rho:ℂ)-1/2)*
      (iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)/
        ((zeroMult (rho:ℂ)).factorial:ℂ))^wordCompletionCount w

def nativeWordGermFactor (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) : ℂ → ℂ :=
  fun z => (wordMultiplierOrderData w rho hright).unit z*
    ((nativeWordPrimePole rho hright).residue+
      (z-((rho:ℂ)-1/2))*(nativeWordPrimePole rho hright).remainder z)

lemma nativeWordGermFactor_analytic (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (nativeWordGermFactor w rho hright) ((rho:ℂ)-1/2) :=
  (wordMultiplierOrderData w rho hright).unit_analytic.mul
    (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul
      (nativeWordPrimePole rho hright).remainder_analytic))

lemma nativeWordGermFactor_value (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    nativeWordGermFactor w rho hright ((rho:ℂ)-1/2)=nativeWordLeadingCoefficient w rho := by
  simp only [nativeWordGermFactor,sub_self,zero_mul,add_zero,
    wordMultiplierOrderData_unit_value,nativeWordPrimePole,nativeWordLeadingCoefficient]
  ring

lemma nativeWordLeadingCoefficient_ne_zero (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    nativeWordLeadingCoefficient w rho≠0 := by
  rw [←nativeWordGermFactor_value w rho hright]
  simpa only [nativeWordGermFactor,sub_self,zero_mul,add_zero] using
    mul_ne_zero (wordMultiplierOrderData w rho hright).unit_ne_zero
      (nativeWordPrimePole rho hright).residue_ne_zero

lemma nativeWordCorrectedField_germ_factorization (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    nativeWordCorrectedField w rho history =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
      fun z => (z-((rho:ℂ)-1/2))^
        (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)*
          nativeWordGermFactor w rho hright z := by
  have h := simplePole_multiplier_germ_factorization (nativeWordPrimePole rho hright)
    (wordMultiplierOrderData w rho hright)
  filter_upwards [h] with z hz
  rw [nativeWordCorrectedField_eq_product]
  exact hz

lemma nativeWordCorrectedField_meromorphic_order (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    meromorphicOrderAt (nativeWordCorrectedField w rho history) ((rho:ℂ)-1/2)=
      (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1:ℤ) := by
  have he : nativeWordCorrectedField w rho history=
      fun z => wordMultiplier w z*nativePrimeTransformGerm z :=
    funext (nativeWordCorrectedField_eq_product w rho history)
  rw [he]
  exact simplePole_multiplier_meromorphic_order (nativeWordPrimePole rho hright)
    (wordMultiplierOrderData w rho hright)

def nativeWordRegularRepresentative (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) : ℂ → ℂ :=
  (nativeWordPrimePole rho hright).regularRepresentative (wordMultiplierOrderData w rho hright)

lemma nativeWordRegularRepresentative_agrees (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) (hp : 0<wordCompletionCount w) :
    nativeWordCorrectedField w rho history =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
      nativeWordRegularRepresentative w rho hright := by
  have hm : 0<wordCompletionCount w*zeroMult (rho:ℂ) :=
    Nat.mul_pos hp (lt_of_lt_of_le Nat.zero_lt_one (Zeta23.zetaZeroConfig.one_le_mult _ rho.property))
  have h := Zeta23.OPICA.completion_agrees_punctured (nativeWordPrimePole rho hright)
    (wordMultiplierOrderData w rho hright) hm
  filter_upwards [h] with z hz
  rw [nativeWordCorrectedField_eq_product]
  exact hz

lemma nativeWordRegularRepresentative_leading_derivative (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=
        ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℂ)*nativeWordLeadingCoefficient w rho := by
  have h := Zeta23.OPICA.completion_leading_jet (nativeWordPrimePole rho hright)
    (wordMultiplierOrderData w rho hright)
  change iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
    (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=
      ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℂ)*
        ((wordMultiplierOrderData w rho hright).unit ((rho:ℂ)-1/2))*
          (nativeWordPrimePole rho hright).residue at h
  rw [←nativeWordGermFactor_value w rho hright]
  simpa only [nativeWordGermFactor,sub_self,zero_mul,add_zero,mul_assoc] using h

lemma nativeWordRegularRepresentative_lower_derivatives (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (j : ℕ) (hj : j<wordCompletionCount w*zeroMult (rho:ℂ)-1) :
    iteratedDeriv j (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=0 :=
  Zeta23.OPICA.completion_lower_derivatives (nativeWordPrimePole rho hright)
    (wordMultiplierOrderData w rho hright) j hj




lemma NativeGenerator.multiplier_meromorphic (g : NativeGenerator) : Meromorphic g.multiplier := by
  intro z
  have hZ : MeromorphicAt (fun w : ℂ => riemannZeta (w+1/2)) z :=
    (actualZeta_meromorphic (z+1/2)).comp_analyticAt (g := fun w : ℂ => w+1/2) (x := z) (by fun_prop)
  cases g with
  | sourceDerivative d => exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (w^2-1/4)^d) z).meromorphicAt
  | delay tau ht => exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-(tau:ℂ)*w)) z).meromorphicAt
  | finiteEuler Q hQ => exact (finiteEulerMultiplier_analyticAt Q z).meromorphicAt
  | inverseFiniteEuler Q hQ => exact (finiteEulerMultiplier_analyticAt Q z).meromorphicAt.inv
  | rational a b ha hb =>
    exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w+(a:ℂ)) z).meromorphicAt.div
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w+(b:ℂ)) z).meromorphicAt
  | inverseRational a b ha hb =>
    exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w+(b:ℂ)) z).meromorphicAt.div
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w+(a:ℂ)) z).meromorphicAt
  | residualPower Y r =>
    exact ((MeromorphicAt.const 1 z).sub
      (hZ.mul (truncatedMoebiusMultiplier_analyticAt Y z).meromorphicAt)).pow r
  | completion =>
    change MeromorphicAt (fun w : ℂ => Zeta23.CCM.nativeCompletionRationalMultiplier w*riemannZeta (w+1/2)) z
    apply MeromorphicAt.mul ?_ hZ
    unfold Zeta23.CCM.nativeCompletionRationalMultiplier
    apply MeromorphicAt.div
    · exact (by fun_prop : AnalyticAt ℂ _ z).meromorphicAt
    · exact (by fun_prop : AnalyticAt ℂ _ z).meromorphicAt

lemma wordAffineTransform_meromorphicAt (w : NativeWord) (B : ℕ → ℂ → ℂ)
    (f : ℂ → ℂ) (z : ℂ) (hf : MeromorphicAt f z)
    (hB : ∀ i, i<w.length → MeromorphicAt (B i) z) :
    MeromorphicAt (wordAffineTransform w B f) z := by
  induction w generalizing B f with
  | nil => exact hf
  | cons g w ih =>
    apply ih
    · exact ((g.multiplier_meromorphic z).mul hf).add (hB 0 (by simp))
    · intro i hi
      exact hB (i+1) (by simpa using Nat.succ_lt_succ hi)

lemma nativeWordTransformedField_meromorphicOn (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (history : NativeWordHistory ((rho:ℂ)-1/2))
    (D : NativeWordHistoryContinuationDomain w history) :
    MeromorphicOn (nativeWordTransformedField w rho history) D.domain := by
  intro z hz
  apply wordAffineTransform_meromorphicAt
  · exact nativePrimeTransformGerm_meromorphic z
  · intro i hi
    exact (D.active_analytic i hi z hz).meromorphicAt

/-- The local word germ needs only the independently identified local germs of
its actual histories. A common global continuation domain is an additional,
separate conclusion, not a restriction on the native local preservation law. -/
lemma nativeWordTransformedField_meromorphicAt (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    MeromorphicAt (nativeWordTransformedField w rho history) ((rho:ℂ)-1/2) := by
  apply wordAffineTransform_meromorphicAt
  · exact nativePrimeTransformGerm_meromorphic _
  · intro i _
    exact (history i).analyticAt.meromorphicAt




lemma nativeWordCorrectedField_normalized_leading_limit (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    Tendsto (fun z => (z-((rho:ℂ)-1/2))^
      (-(((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1))*
        nativeWordCorrectedField w rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rho)) := by
  have heq : (fun z => (z-((rho:ℂ)-1/2))^
      (-(((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1))*
        nativeWordCorrectedField w rho history z) =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
          nativeWordGermFactor w rho hright := by
    filter_upwards [nativeWordCorrectedField_germ_factorization w rho hright history,
      self_mem_nhdsWithin] with z hz hne
    rw [hz,zpow_neg,←mul_assoc,inv_mul_cancel₀ (zpow_ne_zero _ (sub_ne_zero.mpr hne)),one_mul]
  apply Tendsto.congr' heq.symm
  rw [←nativeWordGermFactor_value w rho hright]
  exact (nativeWordGermFactor_analytic w rho hright).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem nativeWord_order_and_leading (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    MeromorphicAt (nativeWordTransformedField w rho history) ((rho:ℂ)-1/2) ∧
    meromorphicOrderAt (nativeWordCorrectedField w rho history) ((rho:ℂ)-1/2)=
      (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1:ℤ) ∧
    (nativeWordCorrectedField w rho history =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
      fun z => (z-((rho:ℂ)-1/2))^
        (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)*nativeWordGermFactor w rho hright z) ∧
    AnalyticAt ℂ (nativeWordGermFactor w rho hright) ((rho:ℂ)-1/2) ∧
    nativeWordGermFactor w rho hright ((rho:ℂ)-1/2)=nativeWordLeadingCoefficient w rho ∧
    nativeWordLeadingCoefficient w rho≠0 ∧
    Tendsto (fun z => (z-((rho:ℂ)-1/2))^
      (-(((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1))*
        nativeWordCorrectedField w rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rho)) ∧
    (wordCompletionCount w=0 → Tendsto
      (fun z => (z-((rho:ℂ)-1/2))*nativeWordCorrectedField w rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rho))) := by
  refine ⟨nativeWordTransformedField_meromorphicAt w rho history,
    nativeWordCorrectedField_meromorphic_order w rho hright history,
    nativeWordCorrectedField_germ_factorization w rho hright history,
    nativeWordGermFactor_analytic w rho hright,nativeWordGermFactor_value w rho hright,
    nativeWordLeadingCoefficient_ne_zero w rho hright,
    nativeWordCorrectedField_normalized_leading_limit w rho hright history,?_⟩
  intro hp
  simpa only [hp,zero_mul,Nat.cast_zero,zero_sub,neg_neg,zpow_one] using
    nativeWordCorrectedField_normalized_leading_limit w rho hright history

theorem nativeWord_first_nonzero_derivative (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) (hp : 0<wordCompletionCount w) :
    (nativeWordCorrectedField w rho history =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
      nativeWordRegularRepresentative w rho hright) ∧
    AnalyticAt ℂ (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2) ∧
    (∀ j : ℕ, j<wordCompletionCount w*zeroMult (rho:ℂ)-1 →
      iteratedDeriv j (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=0) ∧
    iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=
        ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℂ)*nativeWordLeadingCoefficient w rho ∧
    iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)≠0 := by
  refine ⟨nativeWordRegularRepresentative_agrees w rho hright history hp,
    Zeta23.OPICA.completion_regularRepresentative_analytic (nativeWordPrimePole rho hright)
      (wordMultiplierOrderData w rho hright),
    nativeWordRegularRepresentative_lower_derivatives w rho hright,
    nativeWordRegularRepresentative_leading_derivative w rho hright,?_⟩
  rw [nativeWordRegularRepresentative_leading_derivative]
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
    (nativeWordLeadingCoefficient_ne_zero w rho hright)

def NativeGenerator.leadingLogCost : NativeGenerator → ℂ → ℝ
  | .sourceDerivative d, c => (d:ℝ)*|Real.log ‖c^2-1/4‖|
  | .delay tau _, c => tau*|c.re|
  | .finiteEuler Q _, c => (1-(2:ℝ)^(-(c.re+1/2)))⁻¹*
      ∑ p ∈ Q.primeFactors, (p:ℝ)^(-(c.re+1/2))
  | .inverseFiniteEuler Q _, c => (1-(2:ℝ)^(-(c.re+1/2)))⁻¹*
      ∑ p ∈ Q.primeFactors, (p:ℝ)^(-(c.re+1/2))
  | .rational a b _ _, c => |Real.log ‖c+(a:ℂ)‖-Real.log ‖c+(b:ℂ)‖|
  | .inverseRational a b _ _, c => |Real.log ‖c+(b:ℂ)‖-Real.log ‖c+(a:ℂ)‖|
  | .residualPower _ _, _ => 0
  | .completion, c => |Real.log (‖c-1/2‖/(‖c+1/2‖*‖c+3/2‖))|

lemma NativeGenerator.unit_log_cost_le (g : NativeGenerator)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    |Real.log ‖g.unitMultiplier ((rho:ℂ)-1/2)‖|≤g.leadingLogCost ((rho:ℂ)-1/2) := by
  have hs : ((rho:ℂ)-1/2).re+1/2=(rho:ℂ).re := by simp
  cases g with
  | sourceDerivative d => exact (sourceDerivative_unit_log_cost d _).le
  | delay tau ht => exact (delay_unit_log_cost tau ht _).le
  | finiteEuler Q hQ => simpa only [leadingLogCost,hs] using finiteEuler_unit_log_cost_le_rpow Q hQ rho hright
  | inverseFiniteEuler Q hQ => simpa only [leadingLogCost,hs] using inverseEuler_unit_log_cost_le_rpow Q hQ rho hright
  | rational a b ha hb => exact (congrArg abs (rational_unit_log_value a b ha hb rho hright)).le
  | inverseRational a b ha hb => exact (congrArg abs (inverseRational_unit_log_value a b ha hb rho hright)).le
  | residualPower Y r => exact (residualPower_unit_log_cost Y r rho).le
  | completion => exact (congrArg (fun t : ℝ => |Real.log t|) (completion_unit_norm _)).le

def wordExplicitLogCost (w : NativeWord) (c : ℂ) : ℝ :=
  (w.map fun g => g.leadingLogCost c).sum

lemma wordUnitLogCost_le_explicit (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    wordUnitLogCost w ((rho:ℂ)-1/2)≤wordExplicitLogCost w ((rho:ℂ)-1/2) := by
  induction w with
  | nil => simp [wordUnitLogCost,wordExplicitLogCost]
  | cons g w ih => exact add_le_add (g.unit_log_cost_le rho hright) ih

lemma nativeWordLeadingCoefficient_log_bound (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    |Real.log ‖nativeWordLeadingCoefficient w rho‖|≤
      |Real.log ‖-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)‖|+
        wordExplicitLogCost w ((rho:ℂ)-1/2)+(wordCompletionCount w:ℝ)*
          |Real.log ‖(nativeShiftedZetaOrderData rho).unit ((rho:ℂ)-1/2)‖| := by
  have hbound := (wordMultiplierOrderData_log_cost w rho hright).trans
    (add_le_add (wordUnitLogCost_le_explicit w rho hright) le_rfl)
  rw [←nativeWordGermFactor_value w rho hright,nativeWordGermFactor,
    sub_self,zero_mul,add_zero,norm_mul,Real.log_mul
      (norm_ne_zero_iff.mpr (wordMultiplierOrderData w rho hright).unit_ne_zero)
      (norm_ne_zero_iff.mpr (nativeWordPrimePole rho hright).residue_ne_zero)]
  have ha := (abs_add_le
    (Real.log ‖(wordMultiplierOrderData w rho hright).unit ((rho:ℂ)-1/2)‖)
      (Real.log ‖(nativeWordPrimePole rho hright).residue‖)).trans
        (add_le_add hbound le_rfl)
  simpa only [nativeWordPrimePole,add_assoc,add_comm,add_left_comm] using ha

theorem nativeWord_factor_costs (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    (∀ g : NativeGenerator, |Real.log ‖g.unitMultiplier ((rho:ℂ)-1/2)‖|≤
      g.leadingLogCost ((rho:ℂ)-1/2)) ∧
    |Real.log ‖nativeWordLeadingCoefficient w rho‖|≤
      |Real.log ‖-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)‖|+
        wordExplicitLogCost w ((rho:ℂ)-1/2)+(wordCompletionCount w:ℝ)*
          |Real.log ‖iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)/
            ((zeroMult (rho:ℂ)).factorial:ℂ)‖| ∧
    (0<wordCompletionCount w → Real.log ‖iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)‖-
        Real.log ‖nativeWordLeadingCoefficient w rho‖=
          Real.log ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℝ)) ∧
    Real.log ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℝ)≤
      (wordCompletionCount w*zeroMult (rho:ℂ)-1:ℕ)*
        Real.log ((wordCompletionCount w*zeroMult (rho:ℂ)-1:ℕ)+2:ℝ) := by
  refine ⟨fun g => g.unit_log_cost_le rho hright,?_,?_,factorial_jet_log_cost_le _⟩
  · simpa only [nativeShiftedZetaOrderData_unit_value] using
      nativeWordLeadingCoefficient_log_bound w rho hright
  · intro _hp
    rw [nativeWordRegularRepresentative_leading_derivative]
    exact factorial_jet_log_cost _ (nativeWordLeadingCoefficient_ne_zero w rho hright)



def wordCausalState {center : ℂ} : NativeWord → NativeWordHistory center →
    NativeCausalState → NativeCausalState
  | [], _, state => state
  | g::w, history, state => wordCausalState w (fun i => history (i+1))
      ((g.act state).addAction (history 0).state)

lemma wordCausalState_physical_laplace {center : ℂ} (w : NativeWord)
    (history : NativeWordHistory center) (state : NativeCausalState) (f : ℂ → ℂ)
    (hseed : ∃ S : ℝ, ∀ z : ℂ, S<z.re → f z=state.laplace z) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (wordCausalState w history state).laplace z=
        wordAffineTransform w (fun i => (history i).continuation) f z := by
  induction w generalizing history state f with
  | nil =>
    obtain ⟨S,hS⟩ := hseed
    exact ⟨S,fun z hz => (hS z hz).symm⟩
  | cons g w ih =>
    apply ih
    obtain ⟨S,hS⟩ := hseed
    obtain ⟨T,hT⟩ := (nativeGenerator_transform g state).1
    refine ⟨max S (max T (history 0).safeThreshold),fun z hz => ?_⟩
    rw [NativeCausalState.laplace_addAction,(hT z
      ((le_max_left T _).trans_lt ((le_max_right S _).trans_lt hz))).2.2,
      ←hS z ((le_max_left S _).trans_lt hz),
      ←(history 0).initial_identity z
        ((le_max_right T _).trans_lt ((le_max_right S _).trans_lt hz))]

lemma nativeWord_prime_seed_laplace (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) {z : ℂ} (hz : 1/2<z.re) :
    (primeFamilyCausalState 0).laplace z=nativePrimeTransformGerm z := by
  simp only [primeFamilyCausalState,NativeCausalState.laplace,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,pow_zero,mul_one,one_mul,add_zero]
  change (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(primeFieldFamily 0 t:ℂ))=nativePrimeTransformGerm z
  rw [sourceFamily_zero_eq_original.2.1]
  exact (nativePrimePoleData_physical_laplace rho hright hz).trans
    (congrFun (nativePrimePoleData_field rho hright) z)

def nativeWordCausalState (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) : NativeCausalState :=
  wordCausalState w history (primeFamilyCausalState 0)

theorem nativeWord_corrected_transform (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    (∃ S : ℝ, wordHistorySafeThreshold w history≤S ∧ 1/2≤S ∧ ∀ z : ℂ, S<z.re →
      (∀ term∈nativeWordCausalState w rho history,
        Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (nativeWordCausalState w rho history).laplace z=nativeWordTransformedField w rho history z) ∧
    MeromorphicAt (nativeWordTransformedField w rho history) ((rho:ℂ)-1/2) ∧
    (∀ z : ℂ, nativeWordCorrectedField w rho history z=
      wordUnitFactor w z*riemannZeta (z+1/2)^wordCompletionCount w*nativePrimeTransformGerm z) ∧
    wordUnitFactor w ((rho:ℂ)-1/2)≠0 ∧
    (nativeWordPrimePole rho hright).source=Zeta23.CCM.nativeOriginalSource ∧
    primeFieldFamily 0=Zeta23.CCM.nativeOriginalPrimeField ∧
    (∀ d : ℕ, ∀ test : NativeCompactTest,
      ((NativeGenerator.sourceDerivative d).act (primeFamilyCausalState 0)).applyTest test=
        (primeFamilyCausalState d).applyTest test) := by
  obtain ⟨S,hS⟩ := wordCausalState_physical_laplace w history (primeFamilyCausalState 0)
    nativePrimeTransformGerm ⟨1/2,fun z hz => (nativeWord_prime_seed_laplace rho hright hz).symm⟩
  obtain ⟨T,hT⟩ := (nativeWordCausalState w rho history).exists_regular_exponent_bound
  refine ⟨⟨max S (max (wordHistorySafeThreshold w history) (max (1/2) T)),?_,?_,?_⟩,
    nativeWordTransformedField_meromorphicAt w rho history,?_,wordUnitFactor_ne_zero w rho hright,
    rfl,sourceFamily_zero_eq_original.2.1,primeFamilyCausalState_sourceDerivative_applyTest⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro z hz
    refine ⟨fun term ht => term.regular.laplace_integrable
      ((hT term ht).trans_lt ((le_max_right _ _).trans_lt
        ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hz)))),
      hS z ((le_max_left _ _).trans_lt hz)⟩
  · intro z
    rw [nativeWordCorrectedField_eq_product,wordMultiplier_eq_unit_zeta]


end Zeta23.OPICAFollowup
