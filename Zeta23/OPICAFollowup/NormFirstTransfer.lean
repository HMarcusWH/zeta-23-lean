import Zeta23.OPICA.EnergyRate
import Zeta23.OPICA.DivisorMask
import Mathlib.Analysis.SpecialFunctions.Arsinh

namespace Zeta23.OPICAFollowup

open Filter Topology
open Zeta23.OPICA

/-- Squared norm of a field represented in its ambient normed space. For an
`L²` field this is exactly its Hilbert energy. -/
def hilbertEnergy {E : Type*} [Norm E] (x : E) : ℝ := ‖x‖ ^ 2

lemma norm_first_scalar_bound {b s : ℝ} (_hb : 0 ≤ b) (hs : 0 ≤ s) :
    1 + (b+s)^2 ≤ (1+s)^2 * (1+b^2) := by
  have hbs : b ≤ 1+b^2 := by nlinarith [sq_nonneg (b-1/2)]
  have hprod := mul_nonneg hs (sub_nonneg.mpr hbs)
  have hprod2 := mul_nonneg (sq_nonneg s) (sq_nonneg b)
  nlinarith

lemma norm_first_log_upper {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (hF : F = S + B) :
    Real.log (1+‖F‖^2) ≤ Real.log (1+‖B‖^2) + 2*Real.log (1+‖S‖) := by
  have hnorm : ‖F‖ ≤ ‖B‖ + ‖S‖ := by rw [hF, add_comm]; exact norm_add_le _ _
  have hsq : ‖F‖^2 ≤ (‖B‖+‖S‖)^2 := by nlinarith [norm_nonneg F, norm_nonneg B, norm_nonneg S]
  have hbound : 1+‖F‖^2 ≤ (1+‖S‖)^2*(1+‖B‖^2) := by
    nlinarith [norm_first_scalar_bound (norm_nonneg B) (norm_nonneg S)]
  have h := Real.log_le_log (by positivity : 0 < 1+‖F‖^2) hbound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
  norm_num at h
  linarith

lemma norm_first_log_norms {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (hF : F = S + B) :
    |Real.log (1+‖F‖^2) - Real.log (1+‖B‖^2)| ≤ 2*Real.log (1+‖S‖) := by
  apply abs_le.mpr
  have h := norm_first_log_upper F S B hF
  have hrev : B = -S + F := by rw [hF]; abel
  have h' := norm_first_log_upper B (-S) F hrev
  rw [norm_neg] at h'
  constructor <;> linarith

lemma norm_first_log_positive_part {e q l : ℝ} (he : 0 ≤ e) (hq : q = e-l) :
    |Real.log (1+e)-Real.log (1+max q 0)| ≤ Real.log (1+|l|) := by
  have hq0 := le_max_right q 0
  have hql := le_max_left q 0
  have hl0 := abs_nonneg l
  have hl := le_abs_self l
  have hl' := neg_le_abs l
  have hfirst : 1+e ≤ (1+max q 0)*(1+|l|) := by
    have hh := mul_nonneg hq0 hl0
    nlinarith
  have hmax : max q 0 ≤ e+|l| := max_le (by linarith) (by positivity)
  have hsecond : 1+max q 0 ≤ (1+e)*(1+|l|) := by
    have hh := mul_nonneg he hl0
    nlinarith
  have hp : 0 < 1+max q 0 := by linarith
  have h1 := Real.log_le_log (by positivity : 0 < 1+e) hfirst
  have h2 := Real.log_le_log hp hsecond
  rw [Real.log_mul (by linarith) (by positivity)] at h1
  rw [Real.log_mul (by positivity) (by positivity)] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem norm_first_log_comparison {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S + B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) := by
  have hn := norm_first_log_norms F S B hF
  have hp := norm_first_log_positive_part (sq_nonneg ‖B‖) hq
  calc
    _ = |(Real.log (1+‖F‖^2)-Real.log (1+‖B‖^2)) +
          (Real.log (1+‖B‖^2)-Real.log (1+max q 0))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hn hp)

theorem energy_allocation_bound {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    ‖F‖^2 ≤ 2*‖S‖^2+2*max q 0+2*|l| := by
  have h := norm_add_le S B
  rw [← hF] at h
  have hq' := le_max_left q 0
  have hl := le_abs_self l
  nlinarith [norm_nonneg F, norm_nonneg S, norm_nonneg B, sq_nonneg (‖S‖-‖B‖)]

/-! The norm comparison uses no inner product: it therefore applies in
particular to either real or complex Hilbert spaces, including `L²` fields. -/

/-- Norm-first transfer on the parent's positive cofinal horizon schedule.
The assumptions price the Type I norm and the low-mask error separately. -/
theorem norm_first_rate_difference {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (F S B : ℕ → E) (q l : ℕ → ℝ)
    (hF : ∀ n, F n = S n + B n) (hq : ∀ n, q n = hilbertEnergy (B n) - l n)
    (hS : SubexpAlong T S) (hl : SubexpAlong T l) :
    Tendsto (fun n => positiveRate T (fun k => hilbertEnergy (F k)) n -
      positiveRate T q n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => 2 * magnitudeRate T S n + magnitudeRate T l n)
      atTop (𝓝 0) := by
    simpa using (hS.const_mul 2).add hl
  apply squeeze_zero_norm (fun n => ?_) hlim
  have hp : 0 < 2*T.time n := by nlinarith [T.positive n]
  have h := div_le_div_of_nonneg_right
    (norm_first_log_comparison (F n) (S n) (B n) (q n) (l n) (hF n) (hq n)) hp.le
  simpa [positiveRate, magnitudeRate, hilbertEnergy, Real.norm_eq_abs,
    max_eq_left (sq_nonneg ‖F n‖), ← sub_div, abs_div, abs_of_pos hp,
    abs_of_pos (T.positive n), add_div,
    mul_div_assoc] using h

/-- Any two nonnegative observations whose real rate difference tends to zero
have the same extended limsup and liminf, even when either is infinite. -/
theorem nonnegative_rate_extended_congr (u v : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (h : Tendsto (fun n => u n-v n) atTop (𝓝 0)) :
    Filter.limsup (fun n => ENNReal.ofReal (u n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (v n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (u n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (v n)) atTop := by
  let U := fun n => ENNReal.ofReal (u n)
  let V := fun n => ENNReal.ofReal (v n)
  let D := fun n => ENNReal.ofReal (|u n-v n|)
  have hd : Tendsto D atTop (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h.abs
    simpa only [D, Function.comp_def, abs_zero, ENNReal.ofReal_zero] using hh
  have hUV : ∀ n, U n ≤ (V+D) n := by
    intro n
    dsimp [U,V,D]
    rw [← ENNReal.ofReal_add (hv n) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [le_abs_self (u n-v n)]
  have hVU : ∀ n, V n ≤ (U+D) n := by
    intro n
    dsimp [U,V,D]
    rw [← ENNReal.ofReal_add (hu n) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    linarith [neg_abs_le (u n-v n)]
  constructor
  · apply le_antisymm
    · exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hUV)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero hd V)
    · exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hVU)).trans_eq
        (ENNReal.limsup_add_of_right_tendsto_zero hd U)
  · apply le_antisymm
    · exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hUV)).trans_eq
        (ENNReal.liminf_add_of_right_tendsto_zero hd V)
    · exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hVU)).trans_eq
        (ENNReal.liminf_add_of_right_tendsto_zero hd U)

theorem positiveRate_nonneg (T : HorizonSchedule) (u : ℕ → ℝ) (n : ℕ) :
    0 ≤ positiveRate T u n := by
  exact div_nonneg (Real.log_nonneg (by linarith [le_max_right (u n) 0]))
    (by nlinarith [T.positive n])

/-- AT1, including finite limits and the extended nonnegative limsup/liminf.
It requires no subexponential bound on the difference of squared energies. -/
theorem norm_first_rate_transfer {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (F S B : ℕ → E) (q l : ℕ → ℝ)
    (hF : ∀ n, F n = S n + B n) (hq : ∀ n, q n = hilbertEnergy (B n)-l n)
    (hS : SubexpAlong T S) (hl : SubexpAlong T l) :
    Tendsto (fun n => positiveRate T (fun k => hilbertEnergy (F k)) n -
      positiveRate T q n) atTop (𝓝 0) ∧
    (∀ r : ℝ, Tendsto (positiveRate T (fun k => hilbertEnergy (F k))) atTop (𝓝 r) ↔
      Tendsto (positiveRate T q) atTop (𝓝 r)) ∧
    (Filter.limsup (fun n => ENNReal.ofReal (positiveRate T (fun k => hilbertEnergy (F k)) n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (positiveRate T q n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (positiveRate T (fun k => hilbertEnergy (F k)) n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (positiveRate T q n)) atTop) := by
  have hd := norm_first_rate_difference T F S B q l hF hq hS hl
  refine ⟨hd, ?_, nonnegative_rate_extended_congr _ _
    (positiveRate_nonneg T _) (positiveRate_nonneg T _) hd⟩
  intro r
  constructor
  · intro hr
    have hh := hr.sub hd
    simpa using hh
  · intro hr
    have hh := hd.add hr
    simpa using hh

/-- The AT2 logarithmic allocation estimate, before passing to a limit. -/
theorem energy_allocation_log_bound {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = hilbertEnergy B-l) :
    Real.log (1+hilbertEnergy F) ≤
      Real.log (1+max (hilbertEnergy S) (max q 0)) + Real.log (1+|l|) + Real.log 8 := by
  have he := energy_allocation_bound F S B q l hF hq
  let M := max (hilbertEnergy S) (max q 0)
  have hM : 0 ≤ M := (sq_nonneg ‖S‖).trans (le_max_left _ _)
  have hSM : hilbertEnergy S ≤ M := le_max_left _ _
  have hqM : max q 0 ≤ M := le_max_right _ _
  have hl0 := abs_nonneg l
  have hcross := mul_nonneg hM hl0
  have hb : 1+hilbertEnergy F ≤ (1+M)*(1+|l|)*8 := by
    dsimp [hilbertEnergy] at he hSM ⊢
    nlinarith
  have hlog := Real.log_le_log
    (by dsimp [hilbertEnergy]; positivity : 0 < 1+hilbertEnergy F) hb
  rw [Real.log_mul (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by positivity)] at hlog
  exact hlog

/-- AT2: a positive full energy rate and subexponential low-mask error force
the maximum of the Type I energy and positive balanced observation to retain
at least that rate. The maximizing branch may vary with the horizon. -/
theorem energy_allocation_rate_lower {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (F S B : ℕ → E) (q l : ℕ → ℝ)
    (hF : ∀ n, F n = S n+B n) (hq : ∀ n, q n = hilbertEnergy (B n)-l n)
    (hl : SubexpAlong T l) {θ : ℝ} (_hθ : 0 < θ)
    (hfull : Tendsto (positiveRate T (fun n => hilbertEnergy (F n))) atTop (𝓝 θ)) :
    (∀ b : ℝ, b < θ → ∀ᶠ n in atTop,
      b ≤ positiveRate T (fun k => max (hilbertEnergy (S k)) (max (q k) 0)) n) ∧
    ENNReal.ofReal θ ≤ Filter.liminf
      (fun n => ENNReal.ofReal
        (positiveRate T (fun k => max (hilbertEnergy (S k)) (max (q k) 0)) n)) atTop := by
  let M := fun n => max (hilbertEnergy (S n)) (max (q n) 0)
  let lower := fun n => positiveRate T (fun k => hilbertEnergy (F k)) n -
    magnitudeRate T l n - Real.log 8/(2*T.time n)
  have htime : Tendsto (fun n => 2*T.time n) atTop atTop :=
    T.cofinal.const_mul_atTop (by norm_num)
  have hc : Tendsto (fun n => Real.log 8/(2*T.time n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htime
  have hlow : Tendsto lower atTop (𝓝 θ) := by
    simpa [lower] using (hfull.sub hl).sub hc
  have hle : ∀ n, lower n ≤ positiveRate T M n := by
    intro n
    have hp : 0 < 2*T.time n := by nlinarith [T.positive n]
    have hM : 0 ≤ M n := (sq_nonneg ‖S n‖).trans (le_max_left _ _)
    have hb := div_le_div_of_nonneg_right
      (energy_allocation_log_bound (F n) (S n) (B n) (q n) (l n) (hF n) (hq n)) hp.le
    dsimp [lower, positiveRate, magnitudeRate, M, hilbertEnergy] at hb ⊢
    have hMM : 0 ≤ max (‖S n‖^2) (max (q n) 0) := (sq_nonneg ‖S n‖).trans (le_max_left _ _)
    rw [max_eq_left (sq_nonneg ‖F n‖), max_eq_left hMM]
    simp only [add_div] at hb
    linarith
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.mp hlow).1 b hb] with n hn
    exact hn.le.trans (hle n)
  · have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlow
    have hcomp : ∀ᶠ n in atTop, ENNReal.ofReal (lower n) ≤
        ENNReal.ofReal (positiveRate T M n) :=
      Filter.Eventually.of_forall (fun n => ENNReal.ofReal_le_ofReal (hle n))
    exact he.liminf_eq.symm.trans_le (Filter.liminf_le_liminf hcomp)

/-! Optional Candidate 1 from the Post-Green amendment v1.1. These supporting
lemmas do not change any mandatory root or its expected signature. -/

/-- The optimal multiplicative norm-first constant at distance `d`. -/
noncomputable def sharpNormAlpha (d : ℝ) : ℝ := (d + Real.sqrt (d^2 + 4)) / 2

lemma sharpNormAlpha_pos {d : ℝ} (hd : 0 ≤ d) : 0 < sharpNormAlpha d := by
  have hs := Real.sqrt_pos.2 (by positivity : 0 < d^2 + 4)
  unfold sharpNormAlpha
  positivity

lemma sharpNormAlpha_one_le {d : ℝ} (hd : 0 ≤ d) : 1 ≤ sharpNormAlpha d := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ d^2 + 4)
  have hp := Real.sqrt_nonneg (d^2 + 4)
  unfold sharpNormAlpha
  nlinarith [sq_nonneg d]

lemma sharpNormAlpha_le_one_add {d : ℝ} (hd : 0 ≤ d) : sharpNormAlpha d ≤ 1+d := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ d^2 + 4)
  have hp := Real.sqrt_nonneg (d^2 + 4)
  unfold sharpNormAlpha
  nlinarith

lemma sharpNormAlpha_quadratic (d : ℝ) :
    (sharpNormAlpha d)^2 - d * sharpNormAlpha d = 1 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ d^2 + 4)
  unfold sharpNormAlpha
  nlinarith

lemma sharpNormAlpha_sub_inv {d : ℝ} (hd : 0 ≤ d) :
    sharpNormAlpha d - (sharpNormAlpha d)⁻¹ = d := by
  have ha := sharpNormAlpha_pos hd
  have hq := sharpNormAlpha_quadratic d
  field_simp [ha.ne']
  nlinarith

@[simp] lemma sharpNormAlpha_zero : sharpNormAlpha 0 = 1 := by
  norm_num [sharpNormAlpha]

lemma sharpNormAlpha_log_eq_arsinh (d : ℝ) :
    Real.log (sharpNormAlpha d) = Real.arsinh (d/2) := by
  have h₁ := Real.sq_sqrt (by positivity : 0 ≤ 1+(d/2)^2)
  have h₂ := Real.sq_sqrt (by positivity : 0 ≤ d^2+4)
  have h₁p := Real.sqrt_nonneg (1+(d/2)^2)
  have h₂p := Real.sqrt_nonneg (d^2+4)
  have hs : Real.sqrt (1+(d/2)^2) = Real.sqrt (d^2+4)/2 := by nlinarith
  unfold Real.arsinh sharpNormAlpha
  rw [hs]
  congr 1
  ring

/-- The exact nonnegative remainder exhibits the sharp scalar constant. -/
lemma sharp_norm_first_scalar_identity {d : ℝ} (hd : 0 ≤ d) (b : ℝ) :
    (sharpNormAlpha d)^2 * (1+b^2) - (1+(b+d)^2) =
      sharpNormAlpha d*d*(b-(sharpNormAlpha d)⁻¹)^2 := by
  generalize heq : sharpNormAlpha d = a
  have ha : 0 < a := by simpa only [heq] using sharpNormAlpha_pos hd
  have hdiff : a-a⁻¹ = d := by simpa only [heq] using sharpNormAlpha_sub_inv hd
  rw [← hdiff]
  field_simp [ha.ne']
  ring

lemma sharp_norm_first_scalar_bound {d : ℝ} (hd : 0 ≤ d) (b : ℝ) :
    1+(b+d)^2 ≤ (sharpNormAlpha d)^2*(1+b^2) := by
  have hi := sharp_norm_first_scalar_identity hd b
  have hn := mul_nonneg (mul_nonneg (sharpNormAlpha_pos hd).le hd)
    (sq_nonneg (b-(sharpNormAlpha d)⁻¹))
  linarith

lemma sharp_norm_first_log_upper {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    Real.log (1+‖u‖^2) ≤ Real.log (1+‖v‖^2) +
      2*Real.log (sharpNormAlpha ‖u-v‖) := by
  have hnorm : ‖u‖ ≤ ‖v‖+‖u-v‖ := by
    calc
      ‖u‖ = ‖(u-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ ‖u-v‖+‖v‖ := norm_add_le _ _
      _ = ‖v‖+‖u-v‖ := add_comm _ _
  have hsq : ‖u‖^2 ≤ (‖v‖+‖u-v‖)^2 := by
    nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u-v)]
  have hb := sharp_norm_first_scalar_bound (norm_nonneg (u-v)) ‖v‖
  have hbound : 1+‖u‖^2 ≤ (sharpNormAlpha ‖u-v‖)^2*(1+‖v‖^2) := by linarith
  have ha := sharpNormAlpha_pos (norm_nonneg (u-v))
  have hlog := Real.log_le_log (by positivity : 0 < 1+‖u‖^2) hbound
  rw [Real.log_mul (by positivity : (sharpNormAlpha ‖u-v‖)^2 ≠ 0) (by positivity),
    Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- Sharp norm-first comparison in a seminormed group; null vectors need not vanish. -/
lemma sharp_norm_first_log_norms {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    |Real.log (1+‖u‖^2)-Real.log (1+‖v‖^2)| ≤
      2*Real.log (sharpNormAlpha ‖u-v‖) := by
  have hu := sharp_norm_first_log_upper u v
  have hv := sharp_norm_first_log_upper v u
  rw [norm_sub_rev v u] at hv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma sharp_norm_first_arsinh_bound {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    |Real.log (1+‖u‖^2)-Real.log (1+‖v‖^2)| ≤
      2*Real.arsinh (‖u-v‖/2) ∧
      2*Real.arsinh (‖u-v‖/2) ≤ 2*Real.log (1+‖u-v‖) := by
  constructor
  · simpa only [sharpNormAlpha_log_eq_arsinh] using sharp_norm_first_log_norms u v
  · rw [← sharpNormAlpha_log_eq_arsinh]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (sharpNormAlpha_pos (norm_nonneg (u-v)))
        (sharpNormAlpha_le_one_add (norm_nonneg (u-v)))) (by norm_num)

/-- Every nonnegative distance attains the constant on the real scalar model. -/
lemma sharp_norm_first_scalar_attained {d : ℝ} (hd : 0 ≤ d) :
    ‖sharpNormAlpha d-(sharpNormAlpha d)⁻¹‖ = d ∧
    |Real.log (1+‖sharpNormAlpha d‖^2)-Real.log (1+‖(sharpNormAlpha d)⁻¹‖^2)| =
      2*Real.log (sharpNormAlpha d) := by
  have ha := sharpNormAlpha_pos hd
  have ha₁ := sharpNormAlpha_one_le hd
  have hai := inv_pos.2 ha
  constructor
  · rw [sharpNormAlpha_sub_inv hd, Real.norm_eq_abs, abs_of_nonneg hd]
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hai]
    have hp : 1+(sharpNormAlpha d)^2 =
        (sharpNormAlpha d)^2*(1+((sharpNormAlpha d)⁻¹)^2) := by
      field_simp [ha.ne']
      ring
    have heq : Real.log (1+(sharpNormAlpha d)^2) -
        Real.log (1+((sharpNormAlpha d)⁻¹)^2) = 2*Real.log (sharpNormAlpha d) := by
      rw [hp, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    rw [heq, abs_of_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg ha₁))]

/-- Optional sharp positive-part transfer. Native identifications remain consumers. -/
lemma sharp_norm_first_log_comparison {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.arsinh (‖S‖/2)+Real.log (1+|l|) := by
  have hn := (sharp_norm_first_arsinh_bound F B).1
  have hdist : ‖F-B‖ = ‖S‖ := by rw [hF, add_sub_cancel_right]
  rw [hdist] at hn
  have hp := norm_first_log_positive_part (sq_nonneg ‖B‖) hq
  calc
    _ = |(Real.log (1+‖F‖^2)-Real.log (1+‖B‖^2)) +
          (Real.log (1+‖B‖^2)-Real.log (1+max q 0))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hn hp)

end Zeta23.OPICAFollowup

