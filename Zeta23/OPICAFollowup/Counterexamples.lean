import Zeta23.OPICAFollowup.NormFirstTransfer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact auxiliary countercontrols. None asserts an actual off-line zeta zero. -/

noncomputable section
namespace Zeta23.OPICAFollowup
open Filter Topology Set MeasureTheory
open Zeta23.OPICA
open scoped Matrix BigOperators

/-- Constant unit-interval field, identified with its scalar `L²` value. -/
def exponentialBalanced (T : HorizonSchedule) (θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (θ*T.time n)

def exponentialFull (T : HorizonSchedule) (θ : ℝ) (n : ℕ) : ℝ :=
  exponentialBalanced T θ n + 1

lemma exponential_positive_rate (T : HorizonSchedule) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (positiveRate T (fun n => Real.exp (a*T.time n))) atTop (𝓝 (a/2)) := by
  have htime : Tendsto (fun n => 2*T.time n) atTop atTop :=
    T.cofinal.const_mul_atTop (by norm_num)
  have hc : Tendsto (fun n => Real.log 2/(2*T.time n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htime
  have hdiff : Tendsto
      (fun n => positiveRate T (fun k => Real.exp (a*T.time k)) n-a/2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ?_) (fun n => ?_) hc
    all_goals
      have hp : 0 < 2*T.time n := by nlinarith [T.positive n]
      have hexp : 1 ≤ Real.exp (a*T.time n) := by
        simpa using Real.exp_le_exp.mpr (mul_nonneg ha (T.positive n).le)
      have hlo : a*T.time n ≤ Real.log (1+Real.exp (a*T.time n)) := by
        simpa using Real.log_le_log (Real.exp_pos (a*T.time n))
          (show Real.exp (a*T.time n) ≤ 1+Real.exp (a*T.time n) by linarith)
      have hhi : Real.log (1+Real.exp (a*T.time n)) ≤ Real.log 2+a*T.time n := by
        have hh := Real.log_le_log (by positivity : 0 < 1+Real.exp (a*T.time n))
          (show 1+Real.exp (a*T.time n) ≤ 2*Real.exp (a*T.time n) by linarith)
        simpa [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.exp_ne_zero _)] using hh
      dsimp [positiveRate]
      rw [max_eq_left (Real.exp_nonneg _)]
      have hhalf : a/2 = (a*T.time n)/(2*T.time n) := by
        field_simp [(T.positive n).ne']
      rw [hhalf, ← sub_div]
    · exact div_nonneg (sub_nonneg.mpr hlo) hp.le
    · exact div_le_div_of_nonneg_right (by linarith) hp.le
  have hh := hdiff.add_const (a/2)
  simpa using hh

lemma exponential_balanced_energy (T : HorizonSchedule) (θ : ℝ) (n : ℕ) :
    hilbertEnergy (exponentialBalanced T θ n) = Real.exp ((2*θ)*T.time n) := by
  simp only [hilbertEnergy, exponentialBalanced, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [show (2*θ)*T.time n = θ*T.time n+θ*T.time n by ring, Real.exp_add, pow_two]

lemma exponential_raw_energy_difference (T : HorizonSchedule) (θ : ℝ) (n : ℕ) :
    hilbertEnergy (exponentialFull T θ n)-hilbertEnergy (exponentialBalanced T θ n) =
      2*exponentialBalanced T θ n+1 := by
  simp only [hilbertEnergy, exponentialFull, Real.norm_eq_abs, sq_abs]
  ring

/-- The complete AT1 strictness control: the two constant fields have energy
rate `θ`, while the raw energy difference has rate `θ/2 > 0`. -/
theorem norm_first_strictly_weaker_control (T : HorizonSchedule) {θ : ℝ} (hθ : 0 < θ) :
    (∀ n, exponentialFull T θ n = 1+exponentialBalanced T θ n) ∧
    Tendsto (positiveRate T (fun n => hilbertEnergy (exponentialBalanced T θ n)))
      atTop (𝓝 θ) ∧
    Tendsto (positiveRate T (fun n => hilbertEnergy (exponentialFull T θ n)))
      atTop (𝓝 θ) ∧
    (∀ n, hilbertEnergy (exponentialFull T θ n)-hilbertEnergy (exponentialBalanced T θ n) =
      2*exponentialBalanced T θ n+1) ∧
    Tendsto (magnitudeRate T (fun n =>
      hilbertEnergy (exponentialFull T θ n)-hilbertEnergy (exponentialBalanced T θ n)))
      atTop (𝓝 (θ/2)) ∧
    ¬ SubexpAlong T (fun n =>
      hilbertEnergy (exponentialFull T θ n)-hilbertEnergy (exponentialBalanced T θ n)) := by
  have hbal : Tendsto (positiveRate T (fun n => hilbertEnergy (exponentialBalanced T θ n)))
      atTop (𝓝 θ) := by
    simpa only [exponential_balanced_energy, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)]
      using exponential_positive_rate T (show 0 ≤ 2*θ by linarith)
  have hfull : Tendsto (positiveRate T (fun n => hilbertEnergy (exponentialFull T θ n)))
      atTop (𝓝 θ) := by
    have hh := norm_first_rate_transfer T (exponentialFull T θ) (fun _ => (1:ℝ))
      (exponentialBalanced T θ) (fun n => hilbertEnergy (exponentialBalanced T θ n))
      (fun _ => 0) (fun n => by simp [exponentialFull, add_comm])
      (fun n => by simp) (subexpAlong_const T 1) (subexpAlong_const T 0)
    exact (hh.2.1 θ).mpr hbal
  have hraw : Tendsto (magnitudeRate T (fun n =>
      hilbertEnergy (exponentialFull T θ n)-hilbertEnergy (exponentialBalanced T θ n)))
      atTop (𝓝 (θ/2)) := by
    have htime : Tendsto (fun n => 2*T.time n) atTop atTop :=
      T.cofinal.const_mul_atTop (by norm_num)
    have hc : Tendsto (fun n => Real.log 2/(2*T.time n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop htime
    have heq : magnitudeRate T (fun n =>
        hilbertEnergy (exponentialFull T θ n)-hilbertEnergy (exponentialBalanced T θ n)) =
        fun n => Real.log 2/(2*T.time n)+
          positiveRate T (fun k => Real.exp (θ*T.time k)) n := by
      funext n
      simp only [magnitudeRate]
      rw [exponential_raw_energy_difference]
      have hb : 0 < exponentialBalanced T θ n := Real.exp_pos _
      simp only [positiveRate, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 2*exponentialBalanced T θ n+1),
        max_eq_left (Real.exp_nonneg _)]
      rw [show 1+(2*exponentialBalanced T θ n+1) = 2*(1+exponentialBalanced T θ n) by ring,
        Real.log_mul (by norm_num) (by positivity), add_div]
      rfl
    rw [heq]
    simpa using hc.add (exponential_positive_rate T hθ.le)
  refine ⟨fun n => by simp [exponentialFull, add_comm], hbal, hfull,
    exponential_raw_energy_difference T θ, hraw, ?_⟩
  intro hsub
  have hh := tendsto_nhds_unique hraw hsub
  linarith

def collisionPole (h : ℝ) (i : Fin 2) : ℝ := if i=0 then 1-h else 1+h

def collisionExponential (h : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  Real.exp (-collisionPole h i*t)

/-- The actual half-line exponential Gram integral, rather than a supplied matrix. -/
def collisionGram (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∫ t : ℝ in Ioi 0, collisionExponential h i t*collisionExponential h j t

def collisionTarget (h : ℝ) : Fin 2 → ℝ := ![h/(2*(1-h)), -h/(2*(1+h))]

def collisionCost (h : ℝ) : ℝ := collisionTarget h ⬝ᵥ ((collisionGram h)⁻¹ *ᵥ collisionTarget h)

def collisionInner (h : ℝ) (z : ℂ) : ℂ :=
  ((z-1)^2-(h:ℂ)^2)/((z+1)^2-(h:ℂ)^2)

lemma exponential_pair_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, Real.exp (-a*t)*Real.exp (-b*t)) = 1/(a+b) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, Real.exp (-(a+b)*t) := by
      congr 1
      funext t
      rw [← Real.exp_add]
      congr 1
      ring
    _ = 1/(a+b) := by
      rw [integral_exp_mul_Ioi (by linarith : -(a+b)<0)]
      simp only [mul_zero, Real.exp_zero]
      field_simp [show a+b ≠ 0 by linarith]

lemma collisionGram_eq {h : ℝ} (hm : -1 < h) (hp : h < 1) :
    collisionGram h = !![1/(2*(1-h)), (1:ℝ)/2; 1/2, 1/(2*(1+h))] := by
  have ha : 0 < 1-h := by linarith
  have hb : 0 < 1+h := by linarith
  have hpole : ∀ i, 0 < collisionPole h i := by
    intro i
    fin_cases i <;> simp [collisionPole] <;> linarith
  have hg : ∀ i j, collisionGram h i j = 1/(collisionPole h i+collisionPole h j) := by
    intro i j
    exact exponential_pair_integral (hpole i) (hpole j)
  ext i j
  rw [hg]
  fin_cases i <;> fin_cases j <;>
    norm_num [collisionPole] <;> field_simp <;> ring

lemma collisionGram_det {h : ℝ} (hm : -1 < h) (hp : h < 1) :
    (collisionGram h).det = h^2/(4*(1-h^2)) := by
  rw [collisionGram_eq hm hp, Matrix.det_fin_two]
  have h1 : 1-h ≠ 0 := by linarith
  have h2 : 1+h ≠ 0 := by linarith
  have h3 : 1-h^2 ≠ 0 := by nlinarith
  norm_num
  field_simp
  ring

lemma collisionCost_eq {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    collisionCost h = (2-h^2)/(1-h^2) := by
  have hm : -1 < h := by linarith
  have hminus : 1-h ≠ 0 := by linarith
  have hplus : 1+h ≠ 0 := by linarith
  have hsq : 1-h^2 ≠ 0 := by nlinarith
  rw [collisionCost, Matrix.inv_def, collisionGram_det hm h1, collisionGram_eq hm h1,
    Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp [collisionTarget, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.smul_apply]
  field_simp [h0.ne', hminus, hplus, hsq]
  ring

lemma collisionInner_denominator_ne_zero {h : ℝ} (h0 : 0 < h) (h1 : h < 1)
    {z : ℂ} (hz : 0 ≤ z.re) : (z+1)^2-(h:ℂ)^2 ≠ 0 := by
  have hm : z+1-(h:ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hp : z+1+(h:ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have heq : (z+1)^2-(h:ℂ)^2 = (z+1-(h:ℂ))*(z+1+(h:ℂ)) := by ring
  rw [heq]
  exact mul_ne_zero hm hp

lemma collisionInner_boundary_norm {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (τ : ℝ) :
    ‖collisionInner h (Complex.I*τ)‖ = 1 := by
  have hden := collisionInner_denominator_ne_zero h0 h1
    (z := Complex.I*τ) (by simp)
  have hconj : (Complex.I*(τ:ℂ)-1)^2-(h:ℂ)^2 =
      star ((Complex.I*(τ:ℂ)+1)^2-(h:ℂ)^2) := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [collisionInner, hconj, norm_div, norm_star, div_self (norm_ne_zero_iff.mpr hden)]

lemma collisionInner_hasDerivAt {h : ℝ} {z : ℂ}
    (hz : (z+1)^2-(h:ℂ)^2 ≠ 0) :
    HasDerivAt (collisionInner h)
      ((2*(z-1)*((z+1)^2-(h:ℂ)^2) - ((z-1)^2-(h:ℂ)^2)*(2*(z+1))) /
        (((z+1)^2-(h:ℂ)^2)^2)) z := by
  convert (((((hasDerivAt_id z).sub_const 1).pow 2).sub_const ((h:ℂ)^2)).div
      ((((hasDerivAt_id z).add_const 1).pow 2).sub_const ((h:ℂ)^2)) hz) using 1 <;>
    first | rfl | norm_num [collisionInner]

lemma collisionInner_target {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (i : Fin 2) :
    collisionInner h (collisionPole h i) = 0 ∧
      -deriv (collisionInner h) (collisionPole h i) = (collisionTarget h i : ℂ) := by
  have hp : 0 ≤ collisionPole h i := by
    fin_cases i <;> simp [collisionPole] <;> linarith
  have hden := collisionInner_denominator_ne_zero h0 h1
    (z := (collisionPole h i : ℂ)) (by simpa using hp)
  have hd := collisionInner_hasDerivAt hden
  rw [hd.deriv]
  have hm : (1:ℂ)-(h:ℂ) ≠ 0 := by exact_mod_cast (show (1:ℝ)-h ≠ 0 by linarith)
  have hplus : (1:ℂ)+(h:ℂ) ≠ 0 := by exact_mod_cast (show (1:ℝ)+h ≠ 0 by linarith)
  have hdenm : ((1:ℂ)-(h:ℂ)+1)^2-(h:ℂ)^2 = 4*(1-(h:ℂ)) := by ring
  have hdenp : ((1:ℂ)+(h:ℂ)+1)^2-(h:ℂ)^2 = 4*(1+(h:ℂ)) := by ring
  fin_cases i <;> norm_num [collisionInner, collisionPole, collisionTarget] <;>
    simp only [hdenm, hdenp] <;> field_simp <;> ring

/-- The actual coupled cost stays finite at a collision, despite the singular
limit of the Gram matrix. The integral and derivative source are identified. -/
theorem coupled_gram_collision_control :
    (∀ h : ℝ, 0 < h → h < 1 →
      (∀ τ : ℝ, ‖collisionInner h (Complex.I*τ)‖ = 1) ∧
      (∀ i : Fin 2, collisionInner h (collisionPole h i) = 0 ∧
        -deriv (collisionInner h) (collisionPole h i) = (collisionTarget h i : ℂ)) ∧
      collisionGram h = !![1/(2*(1-h)), (1:ℝ)/2; 1/2, 1/(2*(1+h))] ∧
      (collisionGram h).det = h^2/(4*(1-h^2)) ∧
      0 < (collisionGram h).det ∧
      collisionCost h = (2-h^2)/(1-h^2)) ∧
    Tendsto collisionCost (𝓝[>] (0:ℝ)) (𝓝 2) ∧
    Tendsto (fun h => (collisionGram h).det) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    (collisionGram 0).det = 0 := by
  have hlocal : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), 0 < h ∧ h < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with h hp h1
    exact ⟨hp,h1⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h h0 h1
    have hm : -1 < h := by linarith
    refine ⟨collisionInner_boundary_norm h0 h1, collisionInner_target h0 h1,
      collisionGram_eq hm h1, collisionGram_det hm h1, ?_, collisionCost_eq h0 h1⟩
    rw [collisionGram_det hm h1]
    exact div_pos (sq_pos_of_pos h0) (by nlinarith)
  · have hc : ContinuousAt (fun h : ℝ => (2-h^2)/(1-h^2)) 0 := by fun_prop (disch := norm_num)
    have ht : Tendsto (fun h : ℝ => (2-h^2)/(1-h^2)) (𝓝[>] 0) (𝓝 2) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [hlocal] with h hh
    exact (collisionCost_eq hh.1 hh.2).symm
  · have hc : ContinuousAt (fun h : ℝ => h^2/(4*(1-h^2))) 0 := by fun_prop (disch := norm_num)
    have ht : Tendsto (fun h : ℝ => h^2/(4*(1-h^2))) (𝓝[>] 0) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [hlocal] with h hh
    exact (collisionGram_det (by linarith [hh.1]) hh.2).symm
  · rw [collisionGram_eq (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1), Matrix.det_fin_two]
    norm_num

/-! Supporting inverse-conditioning facts. The two required countercontrol roots
above are preserved exactly; the endpoint uses a punctured right limit. -/

lemma collisionGram_inverse_zero_zero {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    ((collisionGram h)⁻¹) 0 0 = 2*(1-h)/h^2 := by
  have hm : -1 < h := by linarith
  have hminus : 1-h ≠ 0 := by linarith
  have hplus : 1+h ≠ 0 := by linarith
  have hsq : 1-h^2 ≠ 0 := by nlinarith
  rw [Matrix.inv_def, collisionGram_det hm h1, collisionGram_eq hm h1,
    Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply]
  norm_num
  field_simp [h0.ne', hminus, hplus, hsq]
  ring

/-- The actual inverse entry diverges although the coupled quadratic cost stays finite. -/
lemma collisionGram_inverse_zero_zero_tendsto :
    Tendsto (fun h : ℝ => ((collisionGram h)⁻¹) 0 0) (𝓝[>] (0:ℝ)) atTop := by
  apply tendsto_atTop_mono' (𝓝[>] (0:ℝ)) _ tendsto_inv_nhdsGT_zero
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with h h0 hhalf
  rw [collisionGram_inverse_zero_zero h0 (by linarith), inv_eq_one_div]
  apply (div_le_div_iff₀ h0 (sq_pos_of_pos h0)).mpr
  have hmul := mul_nonneg h0.le (show (0:ℝ) ≤ 1-2*h by linarith)
  nlinarith

end Zeta23.OPICAFollowup
