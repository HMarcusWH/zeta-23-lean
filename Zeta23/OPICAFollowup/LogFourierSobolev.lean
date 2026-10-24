import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
Logarithmic Fourier-Sobolev calculus (R2-S1b, F1, F2, F3).

- `logUnitary` is the true log unitary (U h)(t) = e^(t/2) h(e^t) for x = e^t.
- `LogFormDomain h h'` is the actual form domain on (0, ∞): h is the primitive of a measurable,
  locally integrable h', and h, x h' are in L²(0, ∞). `logForm h'` is ∫_0^∞ x² |h'|².
- `logFourier` uses the frequency convention e^(-iξt), with no 2π in the phase, so Plancherel
  carries the factor 1/(2π). It is converted exactly to the pinned Mathlib transform
  𝓕 f(ξ/(2π)).

The boundary terms of the form identity vanish because x|h(x)|² has limits at 0 and ∞, and
those limits must be 0 for |h|² to be integrable. Weak derivatives are primitive
representations, proved with Mathlib's fundamental theorem of calculus for absolutely continuous
functions. The L¹ ∩ L² Plancherel identity is derived from Mathlib's L² Fourier transform through
tempered distributions. The H¹(ℝ) realization `LogH1` carries the continuous H⁻¹-H¹ pairing
∫ w (φ' - φ/2) of the actual force -(∂ + 1/2) w, with constant ‖w‖₂. No force term is
transformed separately.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ContDiff Real

namespace Zeta23.OPICAFollowup

section RealEnergy

/-- The primitive branch v(y) = u(a) + ∫_a^y u'. -/
lemma local_energy_primitive {u' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable u' volume a b) :
    ∫ x in a..b, ((c + ∫ t in a..x, u' t) ^ 2 + 2 * x * (c + ∫ t in a..x, u' t) * u' x) =
      b * (c + ∫ t in a..b, u' t) ^ 2 - a * (c + ∫ t in a..a, u' t) ^ 2 := by
  set v : ℝ → ℝ := fun y => c + ∫ t in a..y, u' t with hv
  have hac_int : AbsolutelyContinuousOnInterval (fun y => ∫ t in a..y, u' t) a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral
      (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab)
  have hac_c : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    (contDiffOn_const).absolutelyContinuousOnInterval
  have hac_v : AbsolutelyContinuousOnInterval v a b := hac_c.add hac_int
  have hac_id : AbsolutelyContinuousOnInterval (fun y : ℝ => y) a b :=
    (contDiffOn_id).absolutelyContinuousOnInterval
  have hac_g : AbsolutelyContinuousOnInterval ((fun y : ℝ => y) * (v * v)) a b :=
    hac_id.mul (hac_v.mul hac_v)
  have hftc := hac_g.integral_deriv_eq_sub
  have hderiv : ∀ᵐ x, x ∈ Set.uIoc a b → deriv ((fun y : ℝ => y) * (v * v)) x =
      v x ^ 2 + 2 * x * v x * u' x := by
    filter_upwards [hint.ae_hasDerivAt_integral] with x hx hxI
    have hxU : x ∈ uIcc a b := uIoc_subset_uIcc hxI
    have hd : HasDerivAt v (u' x) x := by
      have := (hx hxU a (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab)).const_add c
      simpa [hv] using this
    have hg : HasDerivAt ((fun y : ℝ => y) * (v * v)) (1 * (v x * v x) + x * (u' x * v x + v x * u' x)) x :=
      (hasDerivAt_id x).mul (hd.mul hd)
    rw [hg.deriv]; ring
  rw [intervalIntegral.integral_congr_ae hderiv] at hftc
  simp only [Pi.mul_apply] at hftc
  rw [hftc]
  simp only [hv]; ring

/-- Local energy identity on [a, b] ⊂ (0, ∞) for u represented as a primitive of u'. -/
lemma local_energy {u u' : ℝ → ℝ} (hrep : ∀ a b, 0 < a → 0 < b → u b - u a = ∫ x in a..b, u' x)
    (hint : ∀ a b, 0 < a → 0 < b → IntervalIntegrable u' volume a b) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∫ x in a..b, (u x ^ 2 + 2 * x * u x * u' x) = b * u b ^ 2 - a * u a ^ 2 := by
  have hb := lt_of_lt_of_le ha hab
  have hU : ∀ y, 0 < y → u y = u a + ∫ t in a..y, u' t := fun y hy => by linarith [hrep a y ha hy]
  have h := local_energy_primitive (c := u a) hab (hint a b ha hb)
  rw [intervalIntegral.integral_same, add_zero, ← hU b hb] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [uIcc_of_le hab] at hx
  rw [← hU x (lt_of_lt_of_le ha hx.1)]

/-- Global energy identity: ∫_0^∞ x u u' = -(1/2) ∫_0^∞ u², the boundary terms x u(x)² vanishing
at 0 and ∞ because u² is integrable. -/
theorem energy_identity_real {u u' : ℝ → ℝ}
    (hrep : ∀ a b, 0 < a → 0 < b → u b - u a = ∫ x in a..b, u' x)
    (hint : ∀ a b, 0 < a → 0 < b → IntervalIntegrable u' volume a b)
    (hmu : AEStronglyMeasurable u (volume.restrict (Ioi 0)))
    (hmu' : AEStronglyMeasurable u' (volume.restrict (Ioi 0)))
    (hu2 : IntegrableOn (fun x => u x ^ 2) (Ioi 0))
    (hxu2 : IntegrableOn (fun x => x ^ 2 * u' x ^ 2) (Ioi 0)) :
    IntegrableOn (fun x => x * u x * u' x) (Ioi 0) ∧
      ∫ x in Ioi 0, x * u x * u' x = -(1 / 2) * ∫ x in Ioi 0, u x ^ 2 := by
  have hmx : AEStronglyMeasurable (fun x : ℝ => x * u x * u' x) (volume.restrict (Ioi 0)) :=
    (continuous_id.aestronglyMeasurable.mul hmu).mul hmu'
  have hcross : IntegrableOn (fun x => x * u x * u' x) (Ioi 0) := by
    refine ((hu2.add hxu2).div_const 2).mono' hmx (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, Pi.add_apply]
    have h1 : |x * u x * u' x| = |u x| * |x * u' x| := by rw [abs_mul, abs_mul, abs_mul]; ring
    rw [h1]
    have e1 : |u x| ^ 2 = u x ^ 2 := sq_abs _
    have e2 : |x * u' x| ^ 2 = x ^ 2 * u' x ^ 2 := by rw [sq_abs, mul_pow]
    nlinarith [sq_nonneg (|u x| - |x * u' x|)]
  set f : ℝ → ℝ := fun x => u x ^ 2 + 2 * (x * u x * u' x) with hf
  have hfi : IntegrableOn f (Ioi 0) := hu2.add (hcross.const_mul 2)
  -- boundary at infinity: ∫_(a,∞) f = -a u(a)² for every a > 0
  have hinf : ∀ a, 0 < a → ∫ x in Ioi a, f x = -(a * u a ^ 2) := by
    intro a ha
    have hfa : IntegrableOn f (Ioi a) := hfi.mono_set (Ioi_subset_Ioi ha.le)
    have hlim := intervalIntegral_tendsto_integral_Ioi a hfa tendsto_id
    have hloc : ∀ b, a ≤ b → ∫ x in a..b, f x = b * u b ^ 2 - a * u a ^ 2 := by
      intro b hab
      rw [← local_energy hrep hint ha hab]
      congr 1; funext x; simp only [hf]; ring
    have hlim2 : Tendsto (fun b => b * u b ^ 2) atTop (𝓝 ((∫ x in Ioi a, f x) + a * u a ^ 2)) := by
      refine ((hlim.add_const (a * u a ^ 2))).congr' ?_
      filter_upwards [eventually_ge_atTop a] with b hb
      simp only [id]; rw [hloc b hb]; ring
    set L := (∫ x in Ioi a, f x) + a * u a ^ 2 with hL
    have hL0 : 0 ≤ L := ge_of_tendsto hlim2 (by
      filter_upwards [eventually_ge_atTop 0] with b hb; positivity)
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (fun h => hne (by linarith))
    obtain ⟨B, hB⟩ := eventually_atTop.1 ((tendsto_order.1 hlim2).1 (L / 2) (by linarith))
    set B' := max B 1
    have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
    apply (not_integrableOn_Ioi_inv (a := B'))
    have hu2B : IntegrableOn (fun x => u x ^ 2) (Ioi B') := hu2.mono_set (Ioi_subset_Ioi hB'0.le)
    refine ((hu2B.const_mul (2 / L))).mono' (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : 0 < x := lt_trans hB'0 hx
    have hbx := hB x (le_trans (le_max_left _ _) (le_of_lt hx))
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), inv_eq_one_div, div_le_iff₀ hx0]
    have : L / 2 * (2 / L) = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hbx.le (by positivity : (0 : ℝ) ≤ 2 / L)]
  -- boundary at zero
  have hzero : ∫ x in Ioi 0, f x = 0 := by
    have hsplit : ∀ a, 0 < a → ∫ x in Ioi a, f x = (∫ x in Ioi 0, f x) - ∫ x in Ioc 0 a, f x := by
      intro a ha
      rw [eq_sub_iff_add_eq, add_comm, ← setIntegral_union (Set.disjoint_left.mpr (fun t h1 h2 => by
          simp only [mem_Ioc, mem_Ioi] at h1 h2; linarith)) measurableSet_Ioi
        (hfi.mono_set Ioc_subset_Ioi_self) (hfi.mono_set (Ioi_subset_Ioi ha.le)),
        Ioc_union_Ioi_eq_Ioi ha.le]
    have hsmall : Tendsto (fun a => ∫ x in Ioc 0 a, f x) (𝓝[>] 0) (𝓝 0) := by
      have hres : ∀ a : ℝ, (∫ x in Ioc 0 a, f x ∂(volume.restrict (Ioi 0))) = ∫ x in Ioc 0 a, f x := by
        intro a
        rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.mpr Ioc_subset_Ioi_self]
      simp_rw [← hres]
      refine hfi.tendsto_setIntegral_nhds_zero ?_
      have : Tendsto (fun a : ℝ => volume (Ioc (0 : ℝ) a)) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun a : ℝ => ENNReal.ofReal a) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.ofReal_zero]
          exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        refine h1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with a ha
        rw [Real.volume_Ioc, sub_zero]
      have hmeas : (fun a => (volume.restrict (Ioi 0)) (Ioc 0 a)) = fun a => volume (Ioc (0 : ℝ) a) := by
        funext a
        rw [Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi, sup_idem]
      simpa [Function.comp_def, hmeas] using this
    have hlim0 : Tendsto (fun a => a * u a ^ 2) (𝓝[>] 0) (𝓝 (-(∫ x in Ioi 0, f x))) := by
      have := (hsmall.const_sub (∫ x in Ioi 0, f x)).neg
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a ha
      rw [← hsplit a ha, hinf a ha, neg_neg]
    set L := -(∫ x in Ioi 0, f x) with hL
    have hL0 : 0 ≤ L := ge_of_tendsto hlim0 (by
      filter_upwards [self_mem_nhdsWithin] with a ha
      have : 0 < a := ha
      positivity)
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (fun h => hne (by linarith))
    have hev := (tendsto_order.1 hlim0).1 (L / 2) (by linarith)
    obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
    set δ := ε with hδdef
    have hδ0 : 0 < δ := hε
    have hδ : ∀ a, 0 < a → a < δ → L / 2 < a * u a ^ 2 := fun a ha0 haε =>
      hh (by rw [Real.dist_eq, sub_zero, abs_of_pos ha0]; exact haε) ha0
    have hII : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 (δ / 2) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
      have hu2s : IntegrableOn (fun x => u x ^ 2) (Ioc 0 (δ / 2)) := hu2.mono_set Ioc_subset_Ioi_self
      refine ((hu2s.const_mul (2 / L))).mono' (by fun_prop) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun x hx => ?_))
      have hx0 : 0 < x := hx.1
      have hxδ : x < δ := lt_of_le_of_lt hx.2 (by linarith)
      have hbx := hδ x hx0 hxδ
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), inv_eq_one_div, div_le_iff₀ hx0]
      have : L / 2 * (2 / L) = 1 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hbx.le (by positivity : (0 : ℝ) ≤ 2 / L)]
    rw [intervalIntegrable_inv_iff] at hII
    rcases hII with h | h
    · linarith
    · exact h (by rw [uIcc_of_le (by positivity)]; exact left_mem_Icc.mpr (by positivity))
  refine ⟨hcross, ?_⟩
  have h2 : ∫ x in Ioi 0, f x = (∫ x in Ioi 0, u x ^ 2) + 2 * ∫ x in Ioi 0, x * u x * u' x := by
    simp only [hf]
    rw [integral_add hu2 (hcross.const_mul 2), integral_const_mul]
  rw [hzero] at h2
  linarith

end RealEnergy

section Domain

/-- The actual form domain on (0, ∞): h is a primitive of the locally integrable, measurable h'
on (0, ∞) (local absolute continuity), h ∈ L²(0, ∞) and x h' ∈ L²(0, ∞). -/
structure LogFormDomain (h h' : ℝ → ℂ) : Prop where
  integral_eq : ∀ a b : ℝ, 0 < a → 0 < b → h b - h a = ∫ x in a..b, h' x
  intervalIntegrable : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable h' volume a b
  measurable_deriv : Measurable h'
  memLp : MemLp h 2 (volume.restrict (Ioi 0))
  memLp_mul_deriv : MemLp (fun x : ℝ => (x : ℂ) * h' x) 2 (volume.restrict (Ioi 0))

/-- The log quadratic form ∫_0^∞ x² |h'|². -/
def logForm (h' : ℝ → ℂ) : ℝ := ∫ x in Ioi 0, x ^ 2 * ‖h' x‖ ^ 2

namespace LogFormDomain

variable {h h' : ℝ → ℂ}

lemma continuousOn (hD : LogFormDomain h h') : ContinuousOn h (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have hrep : ∀ y ∈ uIcc (x / 2) (2 * x), h y = h (x / 2) + ∫ t in (x / 2)..y, h' t := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have := hD.integral_eq (x / 2) y (by linarith) (by linarith [hy.1])
    linear_combination this
  have hcont : ContinuousOn (fun y => h (x / 2) + ∫ t in (x / 2)..y, h' t) (uIcc (x / 2) (2 * x)) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le (by linarith)]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
        (hD.intervalIntegrable (x / 2) (2 * x) (by linarith) (by linarith))))
  have hc : ContinuousOn h (uIcc (x / 2) (2 * x)) := hcont.congr (fun y hy => hrep y hy)
  have hmem : uIcc (x / 2) (2 * x) ∈ 𝓝 x := by
    rw [uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith)
  exact (hc.continuousAt hmem).continuousWithinAt

lemma aestronglyMeasurable (hD : LogFormDomain h h') :
    AEStronglyMeasurable h (volume.restrict (Ioi 0)) :=
  hD.continuousOn.aestronglyMeasurable measurableSet_Ioi

lemma integrableOn_norm_sq (hD : LogFormDomain h h') :
    IntegrableOn (fun x => ‖h x‖ ^ 2) (Ioi 0) :=
  (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD.memLp

lemma integrableOn_sq_norm_deriv (hD : LogFormDomain h h') :
    IntegrableOn (fun x => x ^ 2 * ‖h' x‖ ^ 2) (Ioi 0) := by
  have := (memLp_two_iff_integrable_sq_norm (μ := volume.restrict (Ioi 0))
    ((Complex.measurable_ofReal.mul hD.measurable_deriv).aestronglyMeasurable)).mp hD.memLp_mul_deriv
  refine this.congr (Eventually.of_forall (fun x => ?_))
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Real and imaginary parts inherit the representation. -/
lemma re_integral_eq (hD : LogFormDomain h h') (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (h b).re - (h a).re = ∫ x in a..b, (h' x).re := by
  rw [← Complex.sub_re, hD.integral_eq a b ha hb]
  exact (Complex.reCLM.intervalIntegral_comp_comm (hD.intervalIntegrable a b ha hb)).symm

lemma im_integral_eq (hD : LogFormDomain h h') (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (h b).im - (h a).im = ∫ x in a..b, (h' x).im := by
  rw [← Complex.sub_im, hD.integral_eq a b ha hb]
  exact (Complex.imCLM.intervalIntegral_comp_comm (hD.intervalIntegrable a b ha hb)).symm

/-- The complex energy identity ∫_0^∞ x Re(conj h h') = -(1/2) ∫_0^∞ |h|². -/
theorem energy_identity (hD : LogFormDomain h h') :
    IntegrableOn (fun x => x * (starRingEnd ℂ (h x) * h' x).re) (Ioi 0) ∧
      ∫ x in Ioi 0, x * (starRingEnd ℂ (h x) * h' x).re = -(1 / 2) * ∫ x in Ioi 0, ‖h x‖ ^ 2 := by
  have hm := hD.aestronglyMeasurable
  have hm' : AEStronglyMeasurable h' (volume.restrict (Ioi 0)) := hD.measurable_deriv.aestronglyMeasurable
  have hn := hD.integrableOn_norm_sq
  have hn' := hD.integrableOn_sq_norm_deriv
  have hre2 : IntegrableOn (fun x => (h x).re ^ 2) (Ioi 0) := by
    refine hn.mono' ((Complex.continuous_re.comp_aestronglyMeasurable hm).pow 2)
      (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    exact (sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_re_le_norm _)))
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)))
  have him2 : IntegrableOn (fun x => (h x).im ^ 2) (Ioi 0) := by
    refine hn.mono' ((Complex.continuous_im.comp_aestronglyMeasurable hm).pow 2)
      (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    exact (sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_im_le_norm _)))
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)))
  have hre2' : IntegrableOn (fun x => x ^ 2 * (h' x).re ^ 2) (Ioi 0) := by
    refine hn'.mono' ((continuous_id.pow 2).aestronglyMeasurable.mul
      ((Complex.continuous_re.comp_aestronglyMeasurable hm').pow 2)) (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg
      (Complex.abs_re_le_norm _))) ((le_abs_self _).trans (Complex.abs_re_le_norm _))) (sq_nonneg x)
  have him2' : IntegrableOn (fun x => x ^ 2 * (h' x).im ^ 2) (Ioi 0) := by
    refine hn'.mono' ((continuous_id.pow 2).aestronglyMeasurable.mul
      ((Complex.continuous_im.comp_aestronglyMeasurable hm').pow 2)) (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg
      (Complex.abs_im_le_norm _))) ((le_abs_self _).trans (Complex.abs_im_le_norm _))) (sq_nonneg x)
  obtain ⟨hI1, hE1⟩ := energy_identity_real (u := fun x => (h x).re) (u' := fun x => (h' x).re)
    hD.re_integral_eq (fun a b ha hb => ⟨(hD.intervalIntegrable a b ha hb).1.re, (hD.intervalIntegrable a b ha hb).2.re⟩)
    (Complex.continuous_re.comp_aestronglyMeasurable hm)
    (Complex.continuous_re.comp_aestronglyMeasurable hm') hre2 hre2'
  obtain ⟨hI2, hE2⟩ := energy_identity_real (u := fun x => (h x).im) (u' := fun x => (h' x).im)
    hD.im_integral_eq (fun a b ha hb => ⟨(hD.intervalIntegrable a b ha hb).1.im, (hD.intervalIntegrable a b ha hb).2.im⟩)
    (Complex.continuous_im.comp_aestronglyMeasurable hm)
    (Complex.continuous_im.comp_aestronglyMeasurable hm') him2 him2'
  have hfun : (fun x => x * (starRingEnd ℂ (h x) * h' x).re) =
      fun x => x * (h x).re * (h' x).re + x * (h x).im * (h' x).im := by
    funext x; simp [Complex.mul_re]; ring
  have hnorm : (fun x => ‖h x‖ ^ 2) = fun x => (h x).re ^ 2 + (h x).im ^ 2 := by
    funext x; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  refine ⟨by rw [hfun]; exact hI1.add hI2, ?_⟩
  rw [hfun, integral_add hI1 hI2, hE1, hE2, hnorm, integral_add hre2 him2]
  ring

end LogFormDomain

end Domain

section LogUnitary

lemma integral_exp_smul_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ t, Real.exp t • g (Real.exp t) = ∫ x in Ioi 0, g x := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  congr 1; funext t; rw [abs_of_pos (Real.exp_pos t)]

lemma integrable_exp_smul_comp_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    Integrable (fun t => Real.exp t • g (Real.exp t)) ↔ IntegrableOn g (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) (f := Real.exp)
    (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp, integrableOn_univ] at h
  rw [h]
  refine integrable_congr (Eventually.of_forall (fun t => ?_))
  simp only [abs_of_pos (Real.exp_pos t)]

/-- The unitary log change of variables (U h)(t) = e^(t/2) h(e^t). -/
def logUnitary (h : ℝ → ℂ) (t : ℝ) : ℂ := (Real.exp (t / 2) : ℂ) * h (Real.exp t)

/-- The derivative of U h computed from the derivative h' of h. -/
def logUnitaryDeriv (h h' : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (t / 2) : ℂ) * (h (Real.exp t) / 2 + (Real.exp t : ℂ) * h' (Real.exp t))

lemma exp_half_sq (t : ℝ) : Real.exp (t / 2) ^ 2 = Real.exp t := by
  rw [sq, ← Real.exp_add]; ring_nf

lemma norm_logUnitary_sq (h : ℝ → ℂ) (t : ℝ) :
    ‖logUnitary h t‖ ^ 2 = Real.exp t * ‖h (Real.exp t)‖ ^ 2 := by
  rw [logUnitary, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, exp_half_sq]

lemma norm_add_mul_sq (a b : ℂ) (x : ℝ) :
    ‖a / 2 + (x : ℂ) * b‖ ^ 2 = ‖a‖ ^ 2 / 4 + x * (starRingEnd ℂ a * b).re + x ^ 2 * ‖b‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  norm_num
  ring

lemma norm_logUnitaryDeriv_sq (h h' : ℝ → ℂ) (t : ℝ) :
    ‖logUnitaryDeriv h h' t‖ ^ 2 = Real.exp t *
      (‖h (Real.exp t)‖ ^ 2 / 4 + Real.exp t * (starRingEnd ℂ (h (Real.exp t)) * h' (Real.exp t)).re +
        Real.exp t ^ 2 * ‖h' (Real.exp t)‖ ^ 2) := by
  rw [logUnitaryDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, exp_half_sq, norm_add_mul_sq]

namespace LogFormDomain

variable {h h' : ℝ → ℂ}

lemma continuous_logUnitary (hD : LogFormDomain h h') : Continuous (logUnitary h) :=
  (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
    (hD.continuousOn.comp_continuous Real.continuous_exp (fun t => Real.exp_pos t))

lemma measurable_logUnitaryDeriv (hD : LogFormDomain h h') : Measurable (logUnitaryDeriv h h') := by
  have hc : Continuous (fun t => h (Real.exp t)) :=
    hD.continuousOn.comp_continuous Real.continuous_exp (fun t => Real.exp_pos t)
  unfold logUnitaryDeriv
  exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_id.div_const 2))).mul
    ((hc.measurable.div_const 2).add ((Complex.measurable_ofReal.comp Real.measurable_exp).mul
      (hD.measurable_deriv.comp Real.measurable_exp)))

/-- Unitary L² conversion: ‖U h‖_(L²(ℝ)) = ‖h‖_(L²(0,∞)). -/
theorem logUnitary_unitary (hD : LogFormDomain h h') :
    MemLp (logUnitary h) 2 ∧ ∫ t, ‖logUnitary h t‖ ^ 2 = ∫ x in Ioi 0, ‖h x‖ ^ 2 := by
  have hfun : (fun t => ‖logUnitary h t‖ ^ 2) =
      fun t => Real.exp t • (fun x => ‖h x‖ ^ 2) (Real.exp t) := by
    funext t; rw [norm_logUnitary_sq, smul_eq_mul]
  have hint : Integrable (fun t => ‖logUnitary h t‖ ^ 2) := by
    rw [hfun]; exact (integrable_exp_smul_comp_iff _).mpr hD.integrableOn_norm_sq
  refine ⟨(memLp_two_iff_integrable_sq_norm hD.continuous_logUnitary.aestronglyMeasurable).mpr hint, ?_⟩
  rw [hfun]
  exact integral_exp_smul_comp (fun x => ‖h x‖ ^ 2)

/-- The log-unitary form identity ∫_0^∞ x²|h'|² = ∫ |ψ'|² + (1/4) ∫_0^∞ |h|², ψ = U h. -/
theorem logForm_eq (hD : LogFormDomain h h') :
    MemLp (logUnitaryDeriv h h') 2 ∧
      logForm h' = (∫ t, ‖logUnitaryDeriv h h' t‖ ^ 2) + 1 / 4 * ∫ x in Ioi 0, ‖h x‖ ^ 2 := by
  obtain ⟨hcross, henergy⟩ := hD.energy_identity
  have hn := hD.integrableOn_norm_sq
  have hn' := hD.integrableOn_sq_norm_deriv
  set G : ℝ → ℝ := fun x => ‖h x‖ ^ 2 / 4 + x * (starRingEnd ℂ (h x) * h' x).re +
    x ^ 2 * ‖h' x‖ ^ 2 with hG
  have hGi : IntegrableOn G (Ioi 0) := ((hn.div_const 4).add hcross).add hn'
  have hfun : (fun t => ‖logUnitaryDeriv h h' t‖ ^ 2) = fun t => Real.exp t • G (Real.exp t) := by
    funext t; rw [norm_logUnitaryDeriv_sq, smul_eq_mul]
  have hint : Integrable (fun t => ‖logUnitaryDeriv h h' t‖ ^ 2) := by
    rw [hfun]; exact (integrable_exp_smul_comp_iff _).mpr hGi
  refine ⟨(memLp_two_iff_integrable_sq_norm hD.measurable_logUnitaryDeriv.aestronglyMeasurable).mpr
    hint, ?_⟩
  rw [hfun, integral_exp_smul_comp]
  have hsplit : ∫ x in Ioi 0, G x = (∫ x in Ioi 0, ‖h x‖ ^ 2) / 4 +
      (∫ x in Ioi 0, x * (starRingEnd ℂ (h x) * h' x).re) + ∫ x in Ioi 0, x ^ 2 * ‖h' x‖ ^ 2 := by
    have i0 : IntegrableOn (fun x => ‖h x‖ ^ 2 / 4) (Ioi 0) := hn.div_const 4
    have i1 : IntegrableOn (fun x => ‖h x‖ ^ 2 / 4 + x * (starRingEnd ℂ (h x) * h' x).re) (Ioi 0) :=
      i0.add hcross
    simp only [hG]
    rw [integral_add i1 hn', integral_add i0 hcross, integral_div]
  rw [hsplit, henergy, logForm]
  ring

end LogFormDomain

end LogUnitary

section WeakDerivative

lemma image_exp_Ioc (a b : ℝ) : Real.exp '' Ioc a b = Ioc (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.exp_lt_exp.mpr hx.1, Real.exp_le_exp.mpr hx.2⟩
  · intro hy
    have hy0 : 0 < y := lt_trans (Real.exp_pos a) hy.1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy0⟩
    · rw [← Real.exp_lt_exp, Real.exp_log hy0]; exact hy.1
    · rw [← Real.exp_le_exp, Real.exp_log hy0]; exact hy.2

/-- Product rule for a smooth real factor and a real primitive. -/
lemma integral_deriv_mul_primitive {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (deriv u x * (c + ∫ t in a..x, g t) + u x * g x) =
      u b * (c + ∫ t in a..b, g t) - u a * c := by
  set v : ℝ → ℝ := fun y => c + ∫ t in a..y, g t with hv
  have hac_v : AbsolutelyContinuousOnInterval v a b :=
    ((contDiffOn_const).absolutelyContinuousOnInterval).add
      (hg.absolutelyContinuousOnInterval_intervalIntegral
        (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab))
  have hac_u : AbsolutelyContinuousOnInterval u a b := hu.contDiffOn.absolutelyContinuousOnInterval
  have hftc := hac_u.integral_deriv_mul_eq_sub hac_v
  have hderiv : ∀ᵐ x, x ∈ Set.uIoc a b → deriv u x * v x + u x * deriv v x =
      deriv u x * (c + ∫ t in a..x, g t) + u x * g x := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxI
    have hxU : x ∈ uIcc a b := uIoc_subset_uIcc hxI
    have hd : HasDerivAt v (g x) x := by
      have := (hx hxU a (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab)).const_add c
      simpa [hv] using this
    rw [hd.deriv]
  rw [intervalIntegral.integral_congr_ae hderiv] at hftc
  rw [hftc]
  simp only [hv, intervalIntegral.integral_same, add_zero]

namespace LogFormDomain

variable {h h' : ℝ → ℂ}

/-- Substitution x = e^s in the primitive representation of h. -/
lemma comp_exp_sub (hD : LogFormDomain h h') {a t : ℝ} (hat : a ≤ t) :
    IntervalIntegrable (fun s => (Real.exp s : ℂ) * h' (Real.exp s)) volume a t ∧
      h (Real.exp t) - h (Real.exp a) = ∫ s in a..t, (Real.exp s : ℂ) * h' (Real.exp s) := by
  have hder : ∀ x ∈ Ioc a t, HasDerivWithinAt Real.exp (Real.exp x) (Ioc a t) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (Ioc a t) := Real.exp_injective.injOn
  have hI : IntegrableOn h' (Ioc (Real.exp a) (Real.exp t)) :=
    (hD.intervalIntegrable _ _ (Real.exp_pos a) (Real.exp_pos t)).1
  have hI' := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hder hinj h').mp
    (by rw [image_exp_Ioc]; exact hI)
  have hfun : (fun x => |Real.exp x| • h' (Real.exp x)) = fun s => (Real.exp s : ℂ) * h' (Real.exp s) := by
    funext x; rw [abs_of_pos (Real.exp_pos x), Complex.real_smul]
  rw [hfun] at hI'
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hat).mpr hI', ?_⟩
  have himg := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hder hinj h'
  rw [image_exp_Ioc, hfun] at himg
  rw [hD.integral_eq _ _ (Real.exp_pos a) (Real.exp_pos t),
    intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hat), himg,
    intervalIntegral.integral_of_le hat]

lemma logUnitaryDeriv_eq (t : ℝ) : logUnitaryDeriv h h' t =
    ((Real.exp (t / 2) / 2 : ℝ) : ℂ) * h (Real.exp t) +
      (Real.exp (t / 2) : ℂ) * ((Real.exp t : ℂ) * h' (Real.exp t)) := by
  rw [logUnitaryDeriv]; push_cast; ring

lemma deriv_exp_half (x : ℝ) : deriv (fun t => Real.exp (t / 2)) x = Real.exp (x / 2) / 2 := by
  have h : HasDerivAt (fun t => Real.exp (t / 2)) (Real.exp (x / 2) * (1 / 2)) x :=
    ((hasDerivAt_id x).div_const 2).exp
  rw [h.deriv]; ring

/-- The weak derivative statement: ψ = U h is the primitive of ψ' = U' h on every interval. -/
theorem logUnitary_integral_eq (hD : LogFormDomain h h') (a b : ℝ) :
    IntervalIntegrable (logUnitaryDeriv h h') volume a b ∧
      logUnitary h b - logUnitary h a = ∫ t in a..b, logUnitaryDeriv h h' t := by
  -- reduce to a ≤ b
  suffices key : ∀ a b : ℝ, a ≤ b → IntervalIntegrable (logUnitaryDeriv h h') volume a b ∧
      logUnitary h b - logUnitary h a = ∫ t in a..b, logUnitaryDeriv h h' t by
    rcases le_total a b with hab | hba
    · exact key a b hab
    · obtain ⟨hI, hE⟩ := key b a hba
      refine ⟨hI.symm, ?_⟩
      rw [intervalIntegral.integral_symm, ← hE]; ring
  intro a b hab
  set u : ℝ → ℝ := fun t => Real.exp (t / 2) with hu
  have hu1 : ContDiff ℝ 1 u := (Real.contDiff_exp.comp (contDiff_id.div_const 2))
  set g : ℝ → ℂ := fun s => (Real.exp s : ℂ) * h' (Real.exp s) with hg
  obtain ⟨hgi, -⟩ := hD.comp_exp_sub hab
  have hrep : ∀ t ∈ Icc a b, h (Real.exp t) = h (Real.exp a) + ∫ s in a..t, g s := by
    intro t ht
    have := (hD.comp_exp_sub ht.1).2
    linear_combination this
  have hcont : Continuous (fun t => h (Real.exp t)) :=
    hD.continuousOn.comp_continuous Real.continuous_exp (fun t => Real.exp_pos t)
  have hψI : IntervalIntegrable (logUnitaryDeriv h h') volume a b := by
    have h1 : IntervalIntegrable (fun t => ((Real.exp (t / 2) / 2 : ℝ) : ℂ) * h (Real.exp t)) volume a b :=
      ((Complex.continuous_ofReal.comp ((Real.continuous_exp.comp (continuous_id.div_const 2)).div_const
        2)).mul hcont).intervalIntegrable a b
    have h2 : IntervalIntegrable (fun t => (Real.exp (t / 2) : ℂ) * g t) volume a b :=
      hgi.continuousOn_mul ((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_id.div_const 2))).continuousOn)
    exact (h1.add h2).congr (fun t _ => (logUnitaryDeriv_eq t).symm)
  refine ⟨hψI, ?_⟩
  have hgre : IntervalIntegrable (fun s => (g s).re) volume a b := ⟨hgi.1.re, hgi.2.re⟩
  have hgim : IntervalIntegrable (fun s => (g s).im) volume a b := ⟨hgi.1.im, hgi.2.im⟩
  have hR := integral_deriv_mul_primitive hu1 (c := (h (Real.exp a)).re) hab hgre
  have hI := integral_deriv_mul_primitive hu1 (c := (h (Real.exp a)).im) hab hgim
  -- real and imaginary parts of ψ' on [a, b]
  have hre_pt : ∀ t ∈ uIcc a b, (logUnitaryDeriv h h' t).re =
      deriv u t * ((h (Real.exp a)).re + ∫ s in a..t, (g s).re) + u t * (g t).re := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hv : (h (Real.exp t)).re = (h (Real.exp a)).re + ∫ s in a..t, (g s).re := by
      rw [hrep t ht, Complex.add_re]
      congr 1
      exact (Complex.reCLM.intervalIntegral_comp_comm (hgi.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2))).symm
    rw [logUnitaryDeriv_eq, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hv,
      hu, deriv_exp_half]
  have him_pt : ∀ t ∈ uIcc a b, (logUnitaryDeriv h h' t).im =
      deriv u t * ((h (Real.exp a)).im + ∫ s in a..t, (g s).im) + u t * (g t).im := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hv : (h (Real.exp t)).im = (h (Real.exp a)).im + ∫ s in a..t, (g s).im := by
      rw [hrep t ht, Complex.add_im]
      congr 1
      exact (Complex.imCLM.intervalIntegral_comp_comm (hgi.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2))).symm
    rw [logUnitaryDeriv_eq, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hv,
      hu, deriv_exp_half]
  have hvb_re : (h (Real.exp b)).re = (h (Real.exp a)).re + ∫ s in a..b, (g s).re := by
    rw [hrep b ⟨hab, le_rfl⟩, Complex.add_re]
    congr 1
    exact (Complex.reCLM.intervalIntegral_comp_comm hgi).symm
  have hvb_im : (h (Real.exp b)).im = (h (Real.exp a)).im + ∫ s in a..b, (g s).im := by
    rw [hrep b ⟨hab, le_rfl⟩, Complex.add_im]
    congr 1
    exact (Complex.imCLM.intervalIntegral_comp_comm hgi).symm
  have hre_int : (∫ t in a..b, logUnitaryDeriv h h' t).re = ∫ t in a..b, (logUnitaryDeriv h h' t).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hψI
    simpa using this.symm
  have him_int : (∫ t in a..b, logUnitaryDeriv h h' t).im = ∫ t in a..b, (logUnitaryDeriv h h' t).im := by
    have := Complex.imCLM.intervalIntegral_comp_comm hψI
    simpa using this.symm
  apply Complex.ext
  · rw [Complex.sub_re, hre_int, intervalIntegral.integral_congr hre_pt, hR]
    simp only [logUnitary, Complex.re_ofReal_mul, hu]
    rw [hvb_re]
  · rw [Complex.sub_im, him_int, intervalIntegral.integral_congr him_pt, hI]
    simp only [logUnitary, Complex.im_ofReal_mul, hu]
    rw [hvb_im]

end LogFormDomain

end WeakDerivative

section Plancherel

lemma integral_fourier_mul_eq_of_integrable' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, 𝓕 f x * g x = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg

lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

lemma L2_norm_sq_eq_integral (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  have h1 : (‖g‖ ^ 2 : ℂ) = inner ℂ g g := (inner_self_eq_norm_sq_to_K g).symm
  rw [MeasureTheory.L2.inner_def] at h1
  have h2 : (∫ a, inner ℂ (g a) (g a)) = ((∫ a, ‖g a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h2] at h1
  exact_mod_cast h1

/-- Plancherel for the Mathlib Fourier transform on L¹ ∩ L²: the L² Fourier transform agrees with
the integral transform almost everywhere, and ∫ |𝓕 f|² = ∫ |f|². -/
theorem integral_norm_sq_fourier_of_mem {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun ξ => ‖𝓕 f ξ‖ ^ 2) ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf2.toLp f) with hF
  have hFc := continuous_fourier_of_integrable hf1
  have hpair : ∀ φ : 𝓢(ℝ, ℂ), ∫ x, φ x • F x = ∫ x, φ x • 𝓕 f x := by
    intro φ
    have h1 : ∫ x, φ x • F x = (F : 𝓢'(ℝ, ℂ)) φ := (Lp.toTemperedDistribution_apply F φ).symm
    rw [h1, hF, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply]
    have h2 : ∫ x, (𝓕 φ) x • (hf2.toLp f) x = ∫ x, f x * 𝓕 (φ : ℝ → ℂ) x := by
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx, smul_eq_mul, mul_comm, SchwartzMap.fourier_coe]
    rw [h2, ← integral_fourier_mul_eq_of_integrable' hf1 φ.integrable]
    congr 1; funext x; rw [smul_eq_mul, mul_comm]
  have hae : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
    refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp F).locallyIntegrable (by norm_num))
      hFc.locallyIntegrable (fun g hg hgs => ?_)
    have hgc : HasCompactSupport (fun x => (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
    have hgd : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have := hpair (hgc.toSchwartzMap hgd)
    calc ∫ x, g x • F x = ∫ x, (hgc.toSchwartzMap hgd) x • F x := by
          congr 1
      _ = ∫ x, (hgc.toSchwartzMap hgd) x • 𝓕 f x := this
      _ = ∫ x, g x • 𝓕 f x := by
          congr 1
  have hint : Integrable (fun ξ => ‖𝓕 f ξ‖ ^ 2) := by
    have := (memLp_two_iff_integrable_sq_norm (Lp.memLp F).1).mp (Lp.memLp F)
    exact this.congr (hae.mono (fun x hx => by simp only [hx]))
  refine ⟨hint, ?_⟩
  have e1 : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [L2_norm_sq_eq_integral]
    exact integral_congr_ae (hae.mono (fun x hx => by simp only [hx]))
  have e2 : ∫ t, ‖f t‖ ^ 2 = ‖hf2.toLp f‖ ^ 2 := by
    rw [L2_norm_sq_eq_integral]
    exact integral_congr_ae (hf2.coeFn_toLp.mono (fun x hx => by simp only [hx]))
  rw [e1, e2, hF, Lp.norm_fourier_eq]

end Plancherel

section LogFourier

/-- The logarithmic Fourier transform 𝓕_log f(ξ) = ∫ f(t) e^(-iξt) dt (no 2π in the phase;
Plancherel factor 1/(2π)). -/
def logFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ := ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t

/-- Conversion to the pinned Mathlib convention 𝓕 f(w) = ∫ e^(-2πi t w) f(t) dt. -/
theorem logFourier_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) : logFourier f ξ = 𝓕 f (ξ / (2 * π)) := by
  rw [Real.fourier_real_eq, logFourier]
  congr 1; funext t
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  field_simp

/-- Plancherel with factor 1/(2π) for f ∈ L¹ ∩ L². -/
theorem logFourier_plancherel {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    Integrable (fun ξ => ‖logFourier f ξ‖ ^ 2) ∧
      ∫ t, ‖f t‖ ^ 2 = 1 / (2 * π) * ∫ ξ, ‖logFourier f ξ‖ ^ 2 := by
  obtain ⟨hI, hE⟩ := integral_norm_sq_fourier_of_mem hf1 hf2
  have hfun : (fun ξ => ‖logFourier f ξ‖ ^ 2) = fun ξ => (fun η => ‖𝓕 f η‖ ^ 2) (ξ / (2 * π)) := by
    funext ξ; rw [logFourier_eq_fourier]
  refine ⟨by rw [hfun]; exact hI.comp_div (by positivity), ?_⟩
  rw [hfun, Measure.integral_comp_div (fun η => ‖𝓕 f η‖ ^ 2) (2 * π), hE, smul_eq_mul,
    abs_of_pos (by positivity)]
  field_simp

/-- Differentiation: 𝓕_log(f')(ξ) = iξ 𝓕_log f(ξ). -/
theorem logFourier_deriv {f : ℝ → ℂ} (hf : Integrable f) (hd : Differentiable ℝ f)
    (hf' : Integrable (deriv f)) (ξ : ℝ) :
    logFourier (deriv f) ξ = (ξ : ℂ) * I * logFourier f ξ := by
  rw [logFourier_eq_fourier, logFourier_eq_fourier, Real.fourier_deriv hf hd hf']
  simp only [smul_eq_mul]
  push_cast
  field_simp

end LogFourier

section H1Line

lemma local_energy_line_primitive {u' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable u' volume a b) :
    ∫ x in a..b, 2 * ((c + ∫ t in a..x, u' t) * u' x) =
      (c + ∫ t in a..b, u' t) ^ 2 - (c + ∫ t in a..a, u' t) ^ 2 := by
  set v : ℝ → ℝ := fun y => c + ∫ t in a..y, u' t with hv
  have hac_v : AbsolutelyContinuousOnInterval v a b :=
    ((contDiffOn_const).absolutelyContinuousOnInterval).add
      (hint.absolutelyContinuousOnInterval_intervalIntegral
        (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab))
  have hftc := (hac_v.mul hac_v).integral_deriv_eq_sub
  have hderiv : ∀ᵐ x, x ∈ Set.uIoc a b → deriv (v * v) x = 2 * (v x * u' x) := by
    filter_upwards [hint.ae_hasDerivAt_integral] with x hx hxI
    have hxU : x ∈ uIcc a b := uIoc_subset_uIcc hxI
    have hd : HasDerivAt v (u' x) x := by
      have := (hx hxU a (by rw [uIcc_of_le hab]; exact left_mem_Icc.mpr hab)).const_add c
      simpa [hv] using this
    rw [(hd.mul hd).deriv]; ring
  rw [intervalIntegral.integral_congr_ae hderiv] at hftc
  simp only [Pi.mul_apply] at hftc
  rw [hftc]; simp only [hv]; ring

/-- On the whole line, ∫ u u' = 0 when u and u' are square integrable (boundary terms vanish). -/
theorem energy_line_real {u u' : ℝ → ℝ} (hrep : ∀ a b, u b - u a = ∫ x in a..b, u' x)
    (hint : ∀ a b, IntervalIntegrable u' volume a b)
    (hmu : AEStronglyMeasurable u volume) (hmu' : AEStronglyMeasurable u' volume)
    (hu2 : Integrable (fun x => u x ^ 2)) (hu2' : Integrable (fun x => u' x ^ 2)) :
    Integrable (fun x => u x * u' x) ∧ ∫ x, u x * u' x = 0 := by
  have hcross : Integrable (fun x => u x * u' x) := by
    refine ((hu2.add hu2').div_const 2).mono' (hmu.mul hmu') (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    nlinarith [sq_nonneg (|u x| - |u' x|), sq_abs (u x), sq_abs (u' x)]
  have hloc : ∀ a b, a ≤ b → ∫ x in a..b, 2 * (u x * u' x) = u b ^ 2 - u a ^ 2 := by
    intro a b hab
    have hU : ∀ y, u y = u a + ∫ t in a..y, u' t := fun y => by linarith [hrep a y]
    have h := local_energy_line_primitive (c := u a) hab (hint a b)
    rw [intervalIntegral.integral_same, add_zero, ← hU b] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [← hU x]
  have hf : Integrable (fun x => 2 * (u x * u' x)) := hcross.const_mul 2
  have hnot : ∀ (L : ℝ) (s : Set ℝ), 0 < L → volume s = ⊤ → MeasurableSet s →
      (∀ x ∈ s, L / 2 ≤ u x ^ 2) → False := by
    intro L s hL hs hsm hle
    have hc : IntegrableOn (fun _ : ℝ => L / 2) s := by
      refine (hu2.integrableOn).mono' (by fun_prop) ?_
      refine (ae_restrict_iff' hsm).mpr (Eventually.of_forall (fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact hle x hx
    rw [integrableOn_const_iff (by simp)] at hc
    rcases hc with h | h
    · simp at h; linarith
    · rw [hs] at h; exact lt_irrefl _ h
  -- right half-line
  have hR : ∫ x in Ioi 0, 2 * (u x * u' x) = -(u 0 ^ 2) := by
    have hlim := intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
    have hlim2 : Tendsto (fun b => u b ^ 2) atTop (𝓝 ((∫ x in Ioi 0, 2 * (u x * u' x)) + u 0 ^ 2)) := by
      refine (hlim.add_const (u 0 ^ 2)).congr' ?_
      filter_upwards [eventually_ge_atTop 0] with b hb
      simp only [id]; rw [hloc 0 b hb]; ring
    set L := (∫ x in Ioi 0, 2 * (u x * u' x)) + u 0 ^ 2
    have hL0 : 0 ≤ L := ge_of_tendsto hlim2 (Eventually.of_forall (fun b => sq_nonneg _))
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (fun h => hne (by linarith))
    obtain ⟨B, hB⟩ := eventually_atTop.1 ((tendsto_order.1 hlim2).1 (L / 2) (by linarith))
    exact hnot L (Ici B) hLpos Real.volume_Ici measurableSet_Ici (fun x hx => (hB x hx).le)
  -- left half-line
  have hL : ∫ x in Iic 0, 2 * (u x * u' x) = u 0 ^ 2 := by
    have hlim := intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id
    have hlim2 : Tendsto (fun a => u a ^ 2) atBot (𝓝 (u 0 ^ 2 - ∫ x in Iic 0, 2 * (u x * u' x))) := by
      refine (hlim.const_sub (u 0 ^ 2)).congr' ?_
      filter_upwards [eventually_le_atBot 0] with a ha
      simp only [id]; rw [hloc a 0 ha]; ring
    set L := u 0 ^ 2 - ∫ x in Iic 0, 2 * (u x * u' x)
    have hL0 : 0 ≤ L := ge_of_tendsto hlim2 (Eventually.of_forall (fun b => sq_nonneg _))
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (fun h => hne (by linarith))
    obtain ⟨B, hB⟩ := eventually_atBot.1 ((tendsto_order.1 hlim2).1 (L / 2) (by linarith))
    exact hnot L (Iic B) hLpos Real.volume_Iic measurableSet_Iic (fun x hx => (hB x hx).le)
  refine ⟨hcross, ?_⟩
  have htot := intervalIntegral.integral_Iic_add_Ioi (b := 0) hf.integrableOn hf.integrableOn
  rw [hL, hR, integral_const_mul] at htot
  linarith

/-- H¹(ℝ) data: φ is a primitive of the measurable φ' on ℝ, with φ, φ' ∈ L²(ℝ). -/
structure LogH1 (φ φ' : ℝ → ℂ) : Prop where
  integral_eq : ∀ a b : ℝ, φ b - φ a = ∫ t in a..b, φ' t
  intervalIntegrable : ∀ a b : ℝ, IntervalIntegrable φ' volume a b
  measurable_deriv : Measurable φ'
  memLp : MemLp φ 2
  memLp_deriv : MemLp φ' 2

namespace LogH1

variable {φ φ' : ℝ → ℂ}

lemma continuous (hφ : LogH1 φ φ') : Continuous φ := by
  have hrep : φ = fun x => φ 0 + ∫ t in (0 : ℝ)..x, φ' t := by
    funext x; linear_combination hφ.integral_eq 0 x
  rw [hrep]
  exact continuous_const.add (intervalIntegral.continuous_primitive hφ.intervalIntegrable 0)

/-- The cross term vanishes: ∫ Re(conj φ φ') = 0. -/
theorem cross_term (hφ : LogH1 φ φ') :
    Integrable (fun t => (starRingEnd ℂ (φ t) * φ' t).re) ∧
      ∫ t, (starRingEnd ℂ (φ t) * φ' t).re = 0 := by
  have hm : AEStronglyMeasurable φ volume := hφ.continuous.aestronglyMeasurable
  have hm' : AEStronglyMeasurable φ' volume := hφ.measurable_deriv.aestronglyMeasurable
  have hn := (memLp_two_iff_integrable_sq_norm hm).mp hφ.memLp
  have hn' := (memLp_two_iff_integrable_sq_norm hm').mp hφ.memLp_deriv
  have bound_re : ∀ z : ℂ, z.re ^ 2 ≤ ‖z‖ ^ 2 := fun z =>
    sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_re_le_norm _)))
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have bound_im : ∀ z : ℂ, z.im ^ 2 ≤ ‖z‖ ^ 2 := fun z =>
    sq_le_sq' (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_im_le_norm _)))
      ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have i1 : Integrable (fun t => (φ t).re ^ 2) := hn.mono' ((Complex.continuous_re.comp_aestronglyMeasurable
    hm).pow 2) (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound_re _))
  have i2 : Integrable (fun t => (φ t).im ^ 2) := hn.mono' ((Complex.continuous_im.comp_aestronglyMeasurable
    hm).pow 2) (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound_im _))
  have i3 : Integrable (fun t => (φ' t).re ^ 2) := hn'.mono' ((Complex.continuous_re.comp_aestronglyMeasurable
    hm').pow 2) (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound_re _))
  have i4 : Integrable (fun t => (φ' t).im ^ 2) := hn'.mono' ((Complex.continuous_im.comp_aestronglyMeasurable
    hm').pow 2) (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact bound_im _))
  have hre : ∀ a b, (φ b).re - (φ a).re = ∫ t in a..b, (φ' t).re := fun a b => by
    rw [← Complex.sub_re, hφ.integral_eq a b]
    exact (Complex.reCLM.intervalIntegral_comp_comm (hφ.intervalIntegrable a b)).symm
  have him : ∀ a b, (φ b).im - (φ a).im = ∫ t in a..b, (φ' t).im := fun a b => by
    rw [← Complex.sub_im, hφ.integral_eq a b]
    exact (Complex.imCLM.intervalIntegral_comp_comm (hφ.intervalIntegrable a b)).symm
  obtain ⟨hI1, hE1⟩ := energy_line_real hre (fun a b => ⟨(hφ.intervalIntegrable a b).1.re,
    (hφ.intervalIntegrable a b).2.re⟩) (Complex.continuous_re.comp_aestronglyMeasurable hm)
    (Complex.continuous_re.comp_aestronglyMeasurable hm') i1 i3
  obtain ⟨hI2, hE2⟩ := energy_line_real him (fun a b => ⟨(hφ.intervalIntegrable a b).1.im,
    (hφ.intervalIntegrable a b).2.im⟩) (Complex.continuous_im.comp_aestronglyMeasurable hm)
    (Complex.continuous_im.comp_aestronglyMeasurable hm') i2 i4
  have hfun : (fun t => (starRingEnd ℂ (φ t) * φ' t).re) =
      fun t => (φ t).re * (φ' t).re + (φ t).im * (φ' t).im := by
    funext t; simp [Complex.mul_re]
  refine ⟨by rw [hfun]; exact hI1.add hI2, ?_⟩
  rw [hfun, integral_add hI1 hI2, hE1, hE2, add_zero]

/-- ‖φ' - φ/2‖₂² = ‖φ'‖₂² + (1/4) ‖φ‖₂² for φ ∈ H¹(ℝ). -/
theorem norm_sq_shift (hφ : LogH1 φ φ') :
    Integrable (fun t => ‖φ' t - φ t / 2‖ ^ 2) ∧
      ∫ t, ‖φ' t - φ t / 2‖ ^ 2 = (∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2 := by
  have hm : AEStronglyMeasurable φ volume := hφ.continuous.aestronglyMeasurable
  have hm' : AEStronglyMeasurable φ' volume := hφ.measurable_deriv.aestronglyMeasurable
  have hn := (memLp_two_iff_integrable_sq_norm hm).mp hφ.memLp
  have hn' := (memLp_two_iff_integrable_sq_norm hm').mp hφ.memLp_deriv
  obtain ⟨hc, hce⟩ := hφ.cross_term
  have hpt : ∀ t, ‖φ' t - φ t / 2‖ ^ 2 =
      ‖φ' t‖ ^ 2 + 1 / 4 * ‖φ t‖ ^ 2 - (starRingEnd ℂ (φ t) * φ' t).re := by
    intro t
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    norm_num; ring
  have hfun : (fun t => ‖φ' t - φ t / 2‖ ^ 2) =
      fun t => ‖φ' t‖ ^ 2 + 1 / 4 * ‖φ t‖ ^ 2 - (starRingEnd ℂ (φ t) * φ' t).re := funext hpt
  have i1 : Integrable (fun t => ‖φ' t‖ ^ 2 + 1 / 4 * ‖φ t‖ ^ 2) := hn'.add (hn.const_mul _)
  refine ⟨by rw [hfun]; exact i1.sub hc, ?_⟩
  rw [hfun, integral_sub i1 hc, hce, sub_zero, integral_add hn' (hn.const_mul _), integral_const_mul]

/-- The actual-force pairing ⟨-(∂ + 1/2) w, φ⟩ := ∫ w (φ' - φ/2) is a continuous H⁻¹-H¹ pairing:
|⟨-(∂+1/2)w, φ⟩| ≤ ‖w‖₂ · (‖φ'‖₂² + ‖φ‖₂²/4)^(1/2). -/
theorem force_pairing_bound {w : ℝ → ℂ} (hw : MemLp w 2) (hφ : LogH1 φ φ') :
    Integrable (fun t => w t * (φ' t - φ t / 2)) ∧
      ‖∫ t, w t * (φ' t - φ t / 2)‖ ≤
        (∫ t, ‖w t‖ ^ 2) ^ (1 / 2 : ℝ) * ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hm : AEStronglyMeasurable φ volume := hφ.continuous.aestronglyMeasurable
  have hm' : AEStronglyMeasurable φ' volume := hφ.measurable_deriv.aestronglyMeasurable
  have hg : MemLp (fun t => φ' t - φ t / 2) 2 := by
    have := hφ.memLp_deriv.sub (hφ.memLp.const_mul (1 / 2 : ℂ))
    refine this.ae_eq (Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply]; ring
  have hprod : Integrable (fun t => w t * (φ' t - φ t / 2)) := hw.integrable_mul hg
  refine ⟨hprod, ?_⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hw' : MemLp (fun t => ‖w t‖) (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hw.norm
  have hg' : MemLp (fun t => ‖φ' t - φ t / 2‖) (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hg.norm
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Eventually.of_forall (fun t => norm_nonneg (w t)))
    (Eventually.of_forall (fun t => norm_nonneg _)) hw' hg'
  have e2 : ∫ t, ‖φ' t - φ t / 2‖ ^ (2 : ℝ) = (∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2 := by
    rw [← (hφ.norm_sq_shift).2]; congr 1; funext t; exact Real.rpow_two _
  have e1 : ∫ t, ‖w t‖ ^ (2 : ℝ) = ∫ t, ‖w t‖ ^ 2 := by congr 1; funext t; exact Real.rpow_two _
  rw [e1, e2] at hH
  calc ‖∫ t, w t * (φ' t - φ t / 2)‖ ≤ ∫ t, ‖w t * (φ' t - φ t / 2)‖ := norm_integral_le_integral_norm _
    _ = ∫ t, ‖w t‖ * ‖φ' t - φ t / 2‖ := by congr 1; funext t; rw [norm_mul]
    _ ≤ _ := hH

end LogH1

/-- The H¹ norm with the spectral weight a(ξ) = ξ² + 1/4 in log-Fourier variables. -/
theorem logH1_fourier_norm {φ : ℝ → ℂ} (hφ1 : Integrable φ) (hφ2 : MemLp φ 2)
    (hd : Differentiable ℝ φ) (hd1 : Integrable (deriv φ)) (hd2 : MemLp (deriv φ) 2) :
    Integrable (fun ξ => (ξ ^ 2 + 1 / 4) * ‖logFourier φ ξ‖ ^ 2) ∧
      (∫ t, ‖deriv φ t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2 =
        1 / (2 * π) * ∫ ξ, (ξ ^ 2 + 1 / 4) * ‖logFourier φ ξ‖ ^ 2 := by
  obtain ⟨hI, hE⟩ := logFourier_plancherel hφ1 hφ2
  obtain ⟨hI', hE'⟩ := logFourier_plancherel hd1 hd2
  have hder : ∀ ξ, ‖logFourier (deriv φ) ξ‖ ^ 2 = ξ ^ 2 * ‖logFourier φ ξ‖ ^ 2 := by
    intro ξ
    rw [logFourier_deriv hφ1 hd hd1, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hfun : (fun ξ => (ξ ^ 2 + 1 / 4) * ‖logFourier φ ξ‖ ^ 2) =
      fun ξ => ‖logFourier (deriv φ) ξ‖ ^ 2 + 1 / 4 * ‖logFourier φ ξ‖ ^ 2 := by
    funext ξ; rw [hder]; ring
  refine ⟨by rw [hfun]; exact hI'.add (hI.const_mul _), ?_⟩
  rw [hfun, integral_add hI' (hI.const_mul _), integral_const_mul, hE, hE']
  ring

end H1Line

section Roots

/-- R2-S1b / F1 / F2 / F3: for the actual form domain (h a primitive of h' on (0, ∞), h and x h' in
L²(0, ∞)), the log unitary ψ = U h, ψ(t) = e^(t/2) h(e^t), is an L² isometry onto L²(ℝ), ψ is the
primitive of ψ' = U' h on every interval (weak derivative), ψ' ∈ L²(ℝ), ψ ∈ H¹(ℝ), and
∫_0^∞ x²|h'|² = ∫ |ψ'|² + (1/4) ∫_0^∞ |h|². -/
theorem log_unitary_form_identity (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    MemLp (logUnitary h) 2 ∧
    (∫ t, ‖logUnitary h t‖ ^ 2) = ∫ x in Ioi 0, ‖h x‖ ^ 2 ∧
    (∀ a b : ℝ, logUnitary h b - logUnitary h a = ∫ t in a..b, logUnitaryDeriv h h' t) ∧
    MemLp (logUnitaryDeriv h h') 2 ∧
    logForm h' = (∫ t, ‖logUnitaryDeriv h h' t‖ ^ 2) + 1 / 4 * ∫ x in Ioi 0, ‖h x‖ ^ 2 ∧
    LogH1 (logUnitary h) (logUnitaryDeriv h h') := by
  obtain ⟨hU1, hU2⟩ := hD.logUnitary_unitary
  obtain ⟨hD1, hD2⟩ := hD.logForm_eq
  exact ⟨hU1, hU2, fun a b => (hD.logUnitary_integral_eq a b).2, hD1, hD2,
    ⟨fun a b => (hD.logUnitary_integral_eq a b).2, fun a b => (hD.logUnitary_integral_eq a b).1,
      hD.measurable_logUnitaryDeriv, hU1, hD1⟩⟩

/-- R2-S1b / F1 / F2 / F3: the e^(-iξt) convention and its conversion to the pinned Mathlib
transform, Plancherel with factor 1/(2π), differentiation 𝓕_log(f') = iξ 𝓕_log f, the H¹ norm with
the spectral weight a(ξ) = ξ² + 1/4, and the continuous H⁻¹-H¹ pairing of the actual force
-(∂ + 1/2) w with constant ‖w‖₂. -/
theorem log_fourier_plancherel :
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
  ⟨fun _ _ => rfl, logFourier_eq_fourier, fun _ h1 h2 => logFourier_plancherel h1 h2,
    fun _ h1 hd h2 ξ => logFourier_deriv h1 hd h2 ξ,
    fun _ h1 h2 hd hd1 hd2 => (logH1_fourier_norm h1 h2 hd hd1 hd2).2,
    fun _ _ hφ => hφ.norm_sq_shift.2, fun _ _ _ hw hφ => (hφ.force_pairing_bound hw).2⟩

end Roots

end Zeta23.OPICAFollowup
