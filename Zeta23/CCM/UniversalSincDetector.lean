import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The exact original sinc product: source-level prerequisites

The index `n : ℕ` represents the paper index `r = n + 1`.  The widths and
infinite product below are the specified source, not the earlier bump bank.
The product convergence and nonreal nonvanishing theorems do not assert the
existence of its compact smooth probability density or identify a Fourier
transform. Those analytic construction obligations remain separate.
-/

noncomputable section

open Filter Finset
open scoped Topology Asymptotics

namespace Zeta23.CCM.UniversalSinc

/-- The original source scale required by the core output contract. -/
def fixedScale : ℝ := 1 / 4096

theorem fixedScale_pos : 0 < fixedScale := by
  norm_num [fixedScale]

/-- The paper half-width `s / [r(r+1)]`, indexed from zero. -/
def width (s : ℝ) (n : ℕ) : ℝ := s / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem width_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < width s n := by
  unfold width
  positivity

theorem width_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ width s n := by
  unfold width
  positivity

theorem width_eq_difference (s : ℝ) (n : ℕ) :
    width s n = s / ((n : ℝ) + 1) - s / ((n : ℝ) + 2) := by
  unfold width
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem sum_width_range (s : ℝ) (N : ℕ) :
    ∑ n ∈ range N, width s n = s - s / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, width_eq_difference]
    push_cast
    ring

theorem hasSum_width {s : ℝ} (hs : 0 ≤ s) : HasSum (width s) s := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => width_nonneg hs n) s).2
  simp_rw [sum_width_range]
  have ht : Tendsto (fun N : ℕ => s / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul s
  simpa using tendsto_const_nhds.sub ht

theorem hasSum_tail_width {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    HasSum (fun n : ℕ => width s (n + N)) (s / ((N : ℝ) + 1)) := by
  have ht := (hasSum_nat_add_iff' N).mpr (hasSum_width hs)
  simpa [sum_width_range] using ht

/-- Complex sinc with the removable singularity assigned its exact value. -/
def sinc (z : ℂ) : ℂ := dslope Complex.sin 0 z

@[simp] theorem sinc_zero : sinc 0 = 1 := by
  simp [sinc]

theorem sinc_of_ne_zero {z : ℂ} (hz : z ≠ 0) : sinc z = Complex.sin z / z := by
  simp [sinc, dslope_of_ne _ hz, slope, div_eq_mul_inv, mul_comm]

@[simp] theorem sinc_neg (z : ℂ) : sinc (-z) = sinc z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [sinc_of_ne_zero hz, sinc_of_ne_zero (neg_ne_zero.mpr hz)]

theorem analyticAt_sinc_zero : AnalyticAt ℂ sinc 0 := by
  obtain ⟨p, hp⟩ := (Complex.analyticAt_sin (x := 0))
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem analyticAt_sinc (z : ℂ) : AnalyticAt ℂ sinc z := by
  by_cases hz : z = 0
  · subst z
    exact analyticAt_sinc_zero
  · have hEq : (fun w : ℂ => Complex.sin w / w) =ᶠ[𝓝 z] sinc := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact (sinc_of_ne_zero hw).symm
    exact (Complex.analyticAt_sin.div analyticAt_id hz).congr hEq

theorem continuous_sinc : Continuous sinc :=
  continuous_iff_continuousAt.mpr (fun z => (analyticAt_sinc z).continuousAt)

theorem differentiable_sinc : Differentiable ℂ sinc :=
  fun z => (analyticAt_sinc z).differentiableAt

private theorem complex_norm_instances_eq :
    Complex.instNormedAddCommGroup.toNorm = Complex.instNorm := by
  rfl

theorem sinc_sub_one_isBigO : (fun z : ℂ => sinc z - 1) =O[𝓝 0] id := by
  have h := analyticAt_sinc_zero.differentiableAt.isBigO_sub
  rw [complex_norm_instances_eq] at h
  have hf : (fun x : ℂ => sinc x - sinc 0) = (fun x : ℂ => sinc x - 1) := by
    funext x
    rw [sinc_zero]
  have hg : (fun x : ℂ => x - 0) = id := by
    funext x
    exact sub_zero x
  rw [hf, hg] at h
  exact h

/-- Every individual factor is nonzero off the real axis. -/
theorem sinc_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : sinc z ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; apply hz; simp [h]
  rw [sinc_of_ne_zero hz0]
  apply div_ne_zero _ hz0
  intro hsin
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  apply hz
  rw [hk]
  simp

/-- The original infinite sinc product, without a finite truncation. -/
def product (s : ℝ) (z : ℂ) : ℂ := ∏' n : ℕ, sinc ((width s n : ℂ) * z)

theorem summable_norm_width_mul {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Summable (fun n : ℕ => ‖(width s n : ℂ) * z‖) := by
  have hnorm : (fun n : ℕ => ‖(width s n : ℂ) * z‖) =
      (fun n : ℕ => width s n * ‖z‖) := by
    funext n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (width_nonneg hs n)]
  rw [hnorm]
  exact (hasSum_width hs).summable.mul_right ‖z‖

/-- The summable-deviation criterion, rather than convergence alone, controls
the infinite tail. -/
theorem summable_norm_sinc_sub_one {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Summable (fun n : ℕ => ‖sinc ((width s n : ℂ) * z) - 1‖) := by
  exact sinc_sub_one_isBigO.comp_summable_norm (summable_norm_width_mul hs z)

theorem multipliable_sinc {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Multipliable (fun n : ℕ => sinc ((width s n : ℂ) * z)) := by
  simpa using multipliable_one_add_of_summable (summable_norm_sinc_sub_one hs z)

/-- Prefix products converge to the specified infinite product; a finite
prefix is never substituted for it without a convergence statement. -/
theorem tendsto_partial_product {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Tendsto (fun N : ℕ => ∏ n ∈ range N, sinc ((width s n : ℂ) * z))
      atTop (𝓝 (product s z)) :=
  (multipliable_sinc hs z).hasProd.tendsto_prod_nat

private theorem complex_commMonoid_instances_eq :
    (@NormedField.toNormedCommRing ℂ Complex.instNormedField).toCommRing.toCommMonoid =
      Complex.commRing.toCommMonoid := by
  rfl

/-- Normal convergence on any compact complex set. The common tail bound
is derived from the specified widths and local sinc estimate. -/
theorem hasProdUniformlyOn_compact {s : ℝ} (hs : 0 ≤ s) {K : Set ℂ}
    (hK : IsCompact K) :
    HasProdUniformlyOn (fun n : ℕ => fun z : ℂ => sinc ((width s n : ℂ) * z))
      (product s) K := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C, hCpos, hC⟩ := Asymptotics.isBigO_iff'.mp sinc_sub_one_isBigO
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hC
  have hu : Summable (fun n : ℕ => C * (width s n * R)) :=
    ((hasSum_width hs).summable.mul_right R).mul_left C
  have ht : Tendsto (fun n : ℕ => width s n * R) cofinite (𝓝 0) := by
    simpa using (hasSum_width hs).summable.tendsto_cofinite_zero.mul_const R
  have hb : ∀ᶠ n : ℕ in cofinite, ∀ z ∈ K,
      ‖sinc ((width s n : ℂ) * z) - 1‖ ≤ C * (width s n * R) := by
    filter_upwards [ht.eventually (Iio_mem_nhds hδ)] with n hn z hz
    have hnorm : ‖(width s n : ℂ) * z‖ ≤ width s n * R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (width_nonneg hs n)]
      exact mul_le_mul_of_nonneg_left (hR z hz) (width_nonneg hs n)
    have hmem : (width s n : ℂ) * z ∈ Metric.ball 0 δ := by
      simpa using hnorm.trans_lt hn
    exact (hball hmem).trans (mul_le_mul_of_nonneg_left hnorm hCpos.le)
  have hcts : ∀ n : ℕ, ContinuousOn
      (fun z : ℂ => sinc ((width s n : ℂ) * z) - 1) K := by
    intro n
    exact ((continuous_sinc.comp (continuous_const.mul continuous_id)).sub
      continuous_const).continuousOn
  have hp := Summable.hasProdUniformlyOn_one_add hK hu hb hcts
  rw [complex_commMonoid_instances_eq] at hp
  have hfunc : (fun n : ℕ => fun z : ℂ => 1 + (sinc ((width s n : ℂ) * z) - 1)) =
      (fun n : ℕ => fun z : ℂ => sinc ((width s n : ℂ) * z)) := by
    funext n z
    ring
  have hlimit : (fun z : ℂ => ∏' n : ℕ, (1 + (sinc ((width s n : ℂ) * z) - 1))) =
      product s := by
    funext z
    unfold product
    apply tprod_congr
    intro n
    ring
  rw [hfunc, hlimit] at hp
  exact hp

theorem hasProdLocallyUniformlyOn_univ {s : ℝ} (hs : 0 ≤ s) :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => sinc ((width s n : ℂ) * z))
      (product s) Set.univ := by
  exact hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    (fun _ _ hK => hasProdUniformlyOn_compact hs hK)

/-- The actual infinite product is entire, as a locally uniform limit of
the entire finite products. This still does not construct its density. -/
theorem differentiable_product {s : ℝ} (hs : 0 ≤ s) :
    Differentiable ℂ (product s) := by
  have hF : ∀ᶠ N : ℕ in atTop, DifferentiableOn ℂ
      (fun z : ℂ => ∏ n ∈ range N, sinc ((width s n : ℂ) * z)) Set.univ := by
    filter_upwards with N
    apply Differentiable.differentiableOn
    apply Differentiable.fun_finsetProd
    intro n _
    exact differentiable_sinc.comp
      ((differentiable_const (width s n : ℂ)).mul differentiable_id)
  exact differentiableOn_univ.mp
    ((hasProdLocallyUniformlyOn_univ hs).tendstoLocallyUniformlyOn_finsetRange.differentiableOn
      hF isOpen_univ)

theorem analyticAt_product {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    AnalyticAt ℂ (product s) z :=
  (differentiable_product hs).analyticAt z

/-- The exact infinite source product has no nonreal zeros. -/
theorem product_ne_zero_of_im_ne_zero {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) : product s z ≠ 0 := by
  unfold product
  have hfactor : ∀ n : ℕ, sinc ((width s n : ℂ) * z) ≠ 0 := by
    intro n
    apply sinc_ne_zero_of_im_ne_zero
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_ne_zero (ne_of_gt (width_pos hs n)) hz
  simpa using tprod_one_add_ne_zero_of_summable
    (f := fun n : ℕ => sinc ((width s n : ℂ) * z) - 1)
    (by simpa using hfactor) (summable_norm_sinc_sub_one hs.le z)

@[simp] theorem product_zero (s : ℝ) : product s 0 = 1 := by
  simp [product]

@[simp] theorem product_neg (s : ℝ) (z : ℂ) : product s (-z) = product s z := by
  simp [product]

/-- The frozen source inherits the actual infinite-tail nonvanishing proof. -/
theorem fixed_product_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    product fixedScale z ≠ 0 :=
  product_ne_zero_of_im_ne_zero fixedScale_pos hz

theorem sinc_int_mul_pi_eq_zero (m : ℤ) (hm : m ≠ 0) :
    sinc ((m : ℂ) * (Real.pi : ℂ)) = 0 := by
  have hz : (m : ℂ) * (Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hm
    · exact_mod_cast Real.pi_ne_zero
  rw [sinc_of_ne_zero hz]
  have hsin : Complex.sin ((m : ℂ) * (Real.pi : ℂ)) = 0 :=
    Complex.sin_eq_zero_iff.mpr ⟨m, rfl⟩
  rw [hsin, zero_div]

/-- At this real-axis point the first two distinct factors vanish together. -/
def fixedCoincidentArgument : ℂ := 6 * (Real.pi : ℂ) / (fixedScale : ℂ)

theorem fixed_coincident_factor_zeros :
    (0 : ℕ) ≠ 1 ∧
      sinc ((width fixedScale 0 : ℂ) * fixedCoincidentArgument) = 0 ∧
      sinc ((width fixedScale 1 : ℂ) * fixedCoincidentArgument) = 0 := by
  have h0 : (width fixedScale 0 : ℂ) * fixedCoincidentArgument =
      (3 : ℂ) * (Real.pi : ℂ) := by
    norm_num [width, fixedCoincidentArgument, fixedScale] <;> ring
  have h1 : (width fixedScale 1 : ℂ) * fixedCoincidentArgument =
      (Real.pi : ℂ) := by
    norm_num [width, fixedCoincidentArgument, fixedScale] <;> ring
  refine ⟨by decide, ?_, ?_⟩
  · rw [h0]
    simpa using sinc_int_mul_pi_eq_zero 3 (by decide)
  · rw [h1]
    simpa using sinc_int_mul_pi_eq_zero 1 (by decide)

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.hasSum_width
#print axioms Zeta23.CCM.UniversalSinc.summable_norm_sinc_sub_one
#print axioms Zeta23.CCM.UniversalSinc.product_ne_zero_of_im_ne_zero
#print axioms Zeta23.CCM.UniversalSinc.fixed_product_ne_zero_of_im_ne_zero
#print axioms Zeta23.CCM.UniversalSinc.hasProdUniformlyOn_compact
#print axioms Zeta23.CCM.UniversalSinc.analyticAt_product
#print axioms Zeta23.CCM.UniversalSinc.fixed_coincident_factor_zeros
