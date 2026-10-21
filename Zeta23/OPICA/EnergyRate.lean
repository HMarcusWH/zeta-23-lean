import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! Elementary logarithmic estimates on an explicitly fixed horizon schedule. -/
noncomputable section
namespace Zeta23.OPICA
open Filter Topology

structure HorizonSchedule where
  time : ℕ → ℝ
  positive : ∀ n, 0 < time n
  cofinal : Tendsto time atTop atTop

def magnitudeRate {E : Type*} [Norm E] (T : HorizonSchedule) (u : ℕ → E) (n : ℕ) : ℝ :=
  Real.log (1 + ‖u n‖) / (2 * T.time n)

def positiveRate (T : HorizonSchedule) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (1 + max (u n) 0) / (2 * T.time n)

def SubexpAlong {E : Type*} [Norm E] (T : HorizonSchedule) (u : ℕ → E) : Prop :=
  Tendsto (magnitudeRate T u) atTop (𝓝 0)

private theorem log_comparison_aux {x y d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hd : 0 ≤ d) (hxy : x ≤ y + d) :
    Real.log (1 + x) - Real.log (1 + y) ≤ Real.log (1 + d) := by
  have hp : (0 : ℝ) < 1 + y := by positivity
  have hq : (0 : ℝ) < 1 + d := by positivity
  have h : 1 + x ≤ (1 + y) * (1 + d) := by nlinarith [mul_nonneg hy hd]
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 1 + x) h
  rw [Real.log_mul hp.ne' hq.ne'] at hl
  linarith

theorem log_one_add_posPart_sub_le (a b : ℝ) :
    |Real.log (1 + max a 0) - Real.log (1 + max b 0)| ≤
      Real.log (1 + |a - b|) := by
  have hab : max a 0 ≤ max b 0 + |a - b| := by
    apply max_le
    · have := le_abs_self (a - b); linarith [le_max_left b 0]
    · positivity
  have hba : max b 0 ≤ max a 0 + |a - b| := by
    apply max_le
    · have := neg_abs_le (a - b); linarith [le_max_left a 0]
    · positivity
  exact abs_le.mpr ⟨by
    have := log_comparison_aux (le_max_right b 0) (le_max_right a 0)
      (abs_nonneg (a - b)) hba
    linarith, log_comparison_aux (le_max_right a 0) (le_max_right b 0)
      (abs_nonneg (a - b)) hab⟩

theorem log_one_add_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    |Real.log (1 + ‖a‖) - Real.log (1 + ‖b‖)| ≤ Real.log (1 + ‖a - b‖) := by
  have hab : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    calc ‖a‖ = ‖(a-b)+b‖ := by rw [sub_add_cancel]
         _ ≤ ‖a-b‖+‖b‖ := norm_add_le _ _
         _ = ‖b‖+‖a-b‖ := add_comm _ _
  have hba : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
    calc ‖b‖ = ‖(b-a)+a‖ := by rw [sub_add_cancel]
         _ ≤ ‖b-a‖+‖a‖ := norm_add_le _ _
         _ = ‖a‖+‖a-b‖ := by rw [norm_sub_rev]; exact add_comm _ _
  exact abs_le.mpr ⟨by
    have := log_comparison_aux (norm_nonneg b) (norm_nonneg a) (norm_nonneg (a-b)) hba
    linarith, log_comparison_aux (norm_nonneg a) (norm_nonneg b)
      (norm_nonneg (a-b)) hab⟩

theorem magnitudeRate_nonneg {E : Type*} [Norm E] (T : HorizonSchedule) (u : ℕ → E)
    (hu : ∀ n, 0 ≤ ‖u n‖) (n : ℕ) : 0 ≤ magnitudeRate T u n := by
  exact div_nonneg (Real.log_nonneg (by linarith [hu n])) (by nlinarith [T.positive n])

private theorem rate_abs_sub_le {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (u v : ℕ → E) (n : ℕ) :
    |magnitudeRate T u n - magnitudeRate T v n| ≤
      magnitudeRate T (u - v) n := by
  have hp : 0 < 2 * T.time n := by nlinarith [T.positive n]
  simpa [magnitudeRate, ← sub_div, abs_div, abs_of_pos hp, abs_of_pos (T.positive n)] using
    div_le_div_of_nonneg_right (log_one_add_norm_sub_le (u n) (v n)) hp.le

theorem rate_congr_of_subexp_error {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (u v : ℕ → E) (h : SubexpAlong T (u - v)) :
    Tendsto (fun n => magnitudeRate T u n - magnitudeRate T v n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) h
  simpa only [Real.norm_eq_abs] using rate_abs_sub_le T u v n

theorem posRate_congr_of_subexp_error (T : HorizonSchedule) (u v : ℕ → ℝ)
    (h : SubexpAlong T (u - v)) :
    Tendsto (fun n => positiveRate T u n - positiveRate T v n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) h
  have hp : 0 < 2 * T.time n := by nlinarith [T.positive n]
  simpa [positiveRate, magnitudeRate, ← sub_div, abs_div, abs_of_pos hp, abs_of_pos (T.positive n), Real.norm_eq_abs]
    using div_le_div_of_nonneg_right (log_one_add_posPart_sub_le (u n) (v n)) hp.le

theorem rate_limit_congr_of_subexp_error {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (u v : ℕ → E) (h : SubexpAlong T (u - v)) {r : ℝ}
    (hv : Tendsto (magnitudeRate T v) atTop (𝓝 r)) :
    Tendsto (magnitudeRate T u) atTop (𝓝 r) := by
  have := (rate_congr_of_subexp_error T u v h).add hv
  simpa using this

private theorem log_one_add_norm_add_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    Real.log (1 + ‖a + b‖) ≤ Real.log (1 + ‖a‖) + Real.log (1 + ‖b‖) := by
  have h : 1 + ‖a + b‖ ≤ (1 + ‖a‖) * (1 + ‖b‖) := by
    nlinarith [norm_add_le a b, norm_nonneg a, norm_nonneg b, mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  simpa [Real.log_mul (by positivity : (1 + ‖a‖) ≠ 0) (by positivity : (1 + ‖b‖) ≠ 0)] using
    Real.log_le_log (by positivity : (0 : ℝ) < 1 + ‖a + b‖) h

theorem subexpAlong_add {E : Type*} [SeminormedAddCommGroup E] (T : HorizonSchedule)
    {u v : ℕ → E} (hu : SubexpAlong T u) (hv : SubexpAlong T v) :
    SubexpAlong T (u + v) := by
  apply squeeze_zero (fun n => magnitudeRate_nonneg T (u+v) (fun _ => norm_nonneg _) n)
    (fun n => ?_) (by simpa using hu.add hv)
  have hp : 0 ≤ 2 * T.time n := by nlinarith [T.positive n]
  simpa [magnitudeRate, add_div] using
    div_le_div_of_nonneg_right (log_one_add_norm_add_le (u n) (v n)) hp

theorem subexpAlong_mul {𝕜 : Type*} [NormedRing 𝕜] (T : HorizonSchedule)
    {u v : ℕ → 𝕜} (hu : SubexpAlong T u) (hv : SubexpAlong T v) :
    SubexpAlong T (u * v) := by
  apply squeeze_zero (fun n => magnitudeRate_nonneg T (u*v) (fun _ => norm_nonneg _) n)
    (fun n => ?_) (by simpa using hu.add hv)
  have hl : Real.log (1 + ‖u n * v n‖) ≤
      Real.log (1 + ‖u n‖) + Real.log (1 + ‖v n‖) := by
    have h : 1 + ‖u n * v n‖ ≤ (1 + ‖u n‖) * (1 + ‖v n‖) := by
      nlinarith [norm_mul_le (u n) (v n), norm_nonneg (u n), norm_nonneg (v n)]
    simpa [Real.log_mul (by positivity : (1 + ‖u n‖) ≠ 0)
      (by positivity : (1 + ‖v n‖) ≠ 0)] using
        Real.log_le_log (by positivity : (0 : ℝ) < 1 + ‖u n * v n‖) h
  simpa [magnitudeRate, add_div] using div_le_div_of_nonneg_right hl (by nlinarith [T.positive n] : 0 ≤ 2*T.time n)

theorem subexpAlong_const {E : Type*} [Norm E] (T : HorizonSchedule) (c : E) :
    SubexpAlong T (fun _ => c) := by
  have hd : Tendsto (fun n => 2 * T.time n) atTop atTop :=
    T.cofinal.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.div_atTop hd

theorem subexpAlong_const_smul {𝕜 E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (T : HorizonSchedule) (c : 𝕜)
    {u : ℕ → E} (hu : SubexpAlong T u) : SubexpAlong T (c • u) := by
  have hc : SubexpAlong T (fun _ : ℕ => ‖c‖) := subexpAlong_const T ‖c‖
  have heq : magnitudeRate T (fun n => ‖u n‖) = magnitudeRate T u := by
    funext n; simp [magnitudeRate]
  have hn : SubexpAlong T (fun n => ‖u n‖) := by unfold SubexpAlong; rw [heq]; exact hu
  have heq' : magnitudeRate T (c • u) =
      magnitudeRate T ((fun _ : ℕ => ‖c‖)*(fun n => ‖u n‖)) := by
    funext n; simp [magnitudeRate, norm_smul]
  unfold SubexpAlong
  rw [heq']
  exact subexpAlong_mul T hc hn

private theorem magnitudeRate_mul_le {𝕜 : Type*} [NormedRing 𝕜] (T : HorizonSchedule)
    (a u : ℕ → 𝕜) (n : ℕ) :
    magnitudeRate T (a * u) n ≤ magnitudeRate T a n + magnitudeRate T u n := by
  have h : 1 + ‖a n * u n‖ ≤ (1+‖a n‖)*(1+‖u n‖) := by
    nlinarith [norm_mul_le (a n) (u n), norm_nonneg (a n), norm_nonneg (u n)]
  have hl := Real.log_le_log (by positivity : (0:ℝ)<1+‖a n*u n‖) h
  rw [Real.log_mul (by positivity : (1+‖a n‖)≠0) (by positivity : (1+‖u n‖)≠0)] at hl
  simpa [magnitudeRate, add_div] using div_le_div_of_nonneg_right hl (by nlinarith [T.positive n] : 0≤2*T.time n)

/-- Both the multiplier and its actual inverse must have subexponential cost. -/
def TemperedAlong {𝕜 : Type*} [NormedDivisionRing 𝕜] (T : HorizonSchedule) (a : ℕ → 𝕜) : Prop :=
  (∀ n, a n ≠ 0) ∧ SubexpAlong T a ∧ SubexpAlong T (fun n => (a n)⁻¹)

theorem temperedAlong_of_max_inverse_cost {𝕜 : Type*} [NormedDivisionRing 𝕜]
    (T : HorizonSchedule) (a : ℕ → 𝕜) (ha : ∀ n, a n ≠ 0)
    (hc : Tendsto (fun n => Real.log (max ‖a n‖ ‖(a n)⁻¹‖)/(2*T.time n)) atTop (𝓝 0)) :
    TemperedAlong T a := by
  have htime : Tendsto (fun n => 2*T.time n) atTop atTop :=
    T.cofinal.const_mul_atTop (by norm_num)
  have hconst : Tendsto (fun n => Real.log 2/(2*T.time n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htime
  have hC : ∀ n, 1 ≤ max ‖a n‖ ‖(a n)⁻¹‖ := by
    intro n
    have hm : ‖a n‖*‖(a n)⁻¹‖ = 1 := by rw [← norm_mul, mul_inv_cancel₀ (ha n), norm_one]
    by_cases h : 1 ≤ ‖a n‖
    · exact h.trans (le_max_left _ _)
    · have hinv : 1 ≤ ‖(a n)⁻¹‖ := by
        nlinarith [norm_nonneg (a n), norm_nonneg ((a n)⁻¹)]
      exact hinv.trans (le_max_right _ _)
  have bound : ∀ (f : ℕ → 𝕜), (∀ n, ‖f n‖ ≤ max ‖a n‖ ‖(a n)⁻¹‖) → SubexpAlong T f := by
    intro f hf
    apply squeeze_zero (fun n => magnitudeRate_nonneg T f (fun _ => norm_nonneg _) n)
      (fun n => ?_) (by simpa using hconst.add hc)
    have hp : 0 < max ‖a n‖ ‖(a n)⁻¹‖ := lt_of_lt_of_le zero_lt_one (hC n)
    have hl := Real.log_le_log (by positivity : (0:ℝ)<1+‖f n‖)
      (show 1+‖f n‖ ≤ 2*max ‖a n‖ ‖(a n)⁻¹‖ by linarith [hf n, hC n])
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne'] at hl
    simpa [magnitudeRate, add_div] using div_le_div_of_nonneg_right hl
      (by nlinarith [T.positive n] : 0≤2*T.time n)
  exact ⟨ha, bound a (fun _ => le_max_left _ _), bound (fun n => (a n)⁻¹) (fun _ => le_max_right _ _)⟩

theorem rate_congr_of_tempered_scale {𝕜 : Type*} [NormedDivisionRing 𝕜]
    (T : HorizonSchedule) (a u : ℕ → 𝕜) (ha : TemperedAlong T a) :
    Tendsto (fun n => magnitudeRate T (a*u) n - magnitudeRate T u n) atTop (𝓝 0) := by
  have hlim := ha.2.1.add ha.2.2
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hlim)
  rw [Real.norm_eq_abs, abs_le]
  have hu := magnitudeRate_mul_le T (fun n => (a n)⁻¹) (a*u) n
  have hcancel : (fun n => (a n)⁻¹) * (a*u) = u := by
    funext n; simp [ha.1 n]
  rw [hcancel] at hu
  have hau := magnitudeRate_mul_le T a u n
  have hpos := magnitudeRate_nonneg T a (fun _ => norm_nonneg _) n
  have hinv := magnitudeRate_nonneg T (fun n => (a n)⁻¹) (fun _ => norm_nonneg _) n
  constructor <;> linarith

theorem posRate_congr_of_positive_tempered_scale (T : HorizonSchedule) (a u : ℕ → ℝ)
    (ha : TemperedAlong T a) (hpos : ∀ n, 0 < a n) :
    Tendsto (fun n => positiveRate T (a*u) n - positiveRate T u n) atTop (𝓝 0) := by
  let v : ℕ → ℝ := fun n => max (u n) 0
  have hv : ∀ n, |v n| = v n := fun n => abs_of_nonneg (le_max_right _ _)
  have hav : ∀ n, |a n*v n| = a n*v n := fun n => abs_of_nonneg (mul_nonneg (hpos n).le (le_max_right _ _))
  have hm : ∀ n, max (a n*u n) 0 = a n*v n := by
    intro n
    dsimp [v]
    by_cases h : 0 ≤ u n
    · rw [max_eq_left h, max_eq_left (mul_nonneg (hpos n).le h)]
    · rw [max_eq_right (le_of_not_ge h), max_eq_right (mul_nonpos_of_nonneg_of_nonpos (hpos n).le (le_of_not_ge h)), mul_zero]
  have hpa : ∀ n, |a n| = a n := fun n => abs_of_pos (hpos n)
  simpa [magnitudeRate, positiveRate, Real.norm_eq_abs, hv, hav, hm, hpa, v]
    using rate_congr_of_tempered_scale T a v ha

theorem eventually_positive_of_positive_rate (T : HorizonSchedule) (u : ℕ → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (h : Tendsto (positiveRate T u) atTop (𝓝 θ)) :
    ∀ᶠ n in atTop, 0 < u n := by
  have hp : ∀ᶠ n in atTop, 0 < positiveRate T u n :=
    (tendsto_order.mp h).1 0 hθ
  filter_upwards [hp] with n hn
  by_contra hu
  have hnon : u n ≤ 0 := le_of_not_gt hu
  simp [positiveRate, max_eq_right hnon] at hn

/-- Equality of the extended nonnegative limsup and liminf, including infinite rates. -/
theorem rate_limsup_liminf_congr {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (u v : ℕ → E) (h : SubexpAlong T (u-v)) :
    Filter.limsup (fun n => ENNReal.ofReal (magnitudeRate T u n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (magnitudeRate T v n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (magnitudeRate T u n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (magnitudeRate T v n)) atTop := by
  let U := fun n => ENNReal.ofReal (magnitudeRate T u n)
  let V := fun n => ENNReal.ofReal (magnitudeRate T v n)
  let D := fun n => ENNReal.ofReal (|magnitudeRate T u n - magnitudeRate T v n|)
  have hd : Tendsto D atTop (𝓝 0) := by
    have := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (rate_congr_of_subexp_error T u v h).abs
    simpa only [D, Function.comp_def, abs_zero, ENNReal.ofReal_zero] using this
  have hu : ∀ n, U n ≤ (V+D) n := by
    intro n
    dsimp [U,V,D]
    rw [← ENNReal.ofReal_add (magnitudeRate_nonneg T v (fun _ => norm_nonneg _) n) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [le_abs_self (magnitudeRate T u n - magnitudeRate T v n)]
  have hv : ∀ n, V n ≤ (U+D) n := by
    intro n
    dsimp [U,V,D]
    rw [← ENNReal.ofReal_add (magnitudeRate_nonneg T u (fun _ => norm_nonneg _) n) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [neg_abs_le (magnitudeRate T u n - magnitudeRate T v n)]
  constructor
  · apply le_antisymm
    · exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hu)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero hd V)
    · exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hv)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero hd U)
  · apply le_antisymm
    · exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hu)).trans_eq
        (ENNReal.liminf_add_of_right_tendsto_zero hd V)
    · exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hv)).trans_eq
        (ENNReal.liminf_add_of_right_tendsto_zero hd U)

/-- The positive-part observation has the same extended-rate invariance,
including an infinite limsup or liminf. -/
theorem posRate_limsup_liminf_congr (T : HorizonSchedule) (u v : ℕ → ℝ)
    (h : SubexpAlong T (u-v)) :
    Filter.limsup (fun n => ENNReal.ofReal (positiveRate T u n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (positiveRate T v n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (positiveRate T u n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (positiveRate T v n)) atTop := by
  have hnon (w : ℕ → ℝ) (n : ℕ) : 0 ≤ positiveRate T w n := by
    exact div_nonneg (Real.log_nonneg (by linarith [le_max_right (w n) 0]))
      (by nlinarith [T.positive n])
  let U := fun n => ENNReal.ofReal (positiveRate T u n)
  let V := fun n => ENNReal.ofReal (positiveRate T v n)
  let D := fun n => ENNReal.ofReal (|positiveRate T u n - positiveRate T v n|)
  have hd : Tendsto D atTop (𝓝 0) := by
    have := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (posRate_congr_of_subexp_error T u v h).abs
    simpa only [D, Function.comp_def, abs_zero, ENNReal.ofReal_zero] using this
  have hu : ∀ n, U n ≤ (V+D) n := by
    intro n
    dsimp [U,V,D]
    rw [← ENNReal.ofReal_add (hnon v n) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [le_abs_self (positiveRate T u n - positiveRate T v n)]
  have hv : ∀ n, V n ≤ (U+D) n := by
    intro n
    dsimp [U,V,D]
    rw [← ENNReal.ofReal_add (hnon u n) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [neg_abs_le (positiveRate T u n - positiveRate T v n)]
  constructor
  · apply le_antisymm
    · exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hu)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero hd V)
    · exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hv)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero hd U)
  · apply le_antisymm
    · exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hu)).trans_eq
        (ENNReal.liminf_add_of_right_tendsto_zero hd V)
    · exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hv)).trans_eq
        (ENNReal.liminf_add_of_right_tendsto_zero hd U)

end Zeta23.OPICA
