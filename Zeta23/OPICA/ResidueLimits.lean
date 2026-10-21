import Mathlib.Analysis.Meromorphic.Basic
import Zeta23.OPICA.LocalData
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Complex Filter Metric Set
open scoped Topology

namespace Zeta23.OPICA

def contourResidue (center : ℂ) (radius : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ z in C(center, radius), f z

theorem contourResidue_sub {center : ℂ} {radius : ℝ} {f g : ℂ → ℂ}
    (hf : CircleIntegrable f center radius) (hg : CircleIntegrable g center radius) :
    contourResidue center radius (fun z => f z - g z) =
      contourResidue center radius f - contourResidue center radius g := by
  simp only [contourResidue, circleIntegral.integral_sub hf hg, mul_sub]

theorem contourResidue_norm_le {center : ℂ} {radius bound : ℝ} {f : ℂ → ℂ}
    (hr : 0 ≤ radius) (hf : ∀ z ∈ sphere center radius, ‖f z‖ ≤ bound) :
    ‖contourResidue center radius f‖ ≤ radius * bound := by
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hf

theorem contourResidue_continuous_of_circle_uniform (center : ℂ) (radius : ℝ)
    (hr : 0 < radius) (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (error : ℕ → ℝ)
    (hf : ∀ n, CircleIntegrable (f n) center radius)
    (hg : CircleIntegrable g center radius)
    (hbound : ∀ n z, z ∈ sphere center radius → ‖f n z - g z‖ ≤ error n)
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto (fun n => contourResidue center radius (f n)) atTop
      (𝓝 (contourResidue center radius g)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm
    (a := fun n => radius * error n)
  · intro n
    rw [← contourResidue_sub (hf n) hg]
    exact contourResidue_norm_le hr.le (hbound n)
  · simpa using tendsto_const_nhds.mul herror

/-- An actual simple-pole representative on a closed disk has its stated
residue as contour coordinate. Analyticity is required across the boundary. -/
theorem contourResidue_eq_simplePole (center residue : ℂ) (radius : ℝ)
    (hr : 0 < radius) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall center radius)) :
    contourResidue center radius (fun z => residue / (z - center) + h z) = residue := by
  have hp : CircleIntegrable (fun z : ℂ => residue * (z - center)⁻¹) center radius := by
    apply ContinuousOn.circleIntegrable hr.le
    intro z hz
    have hzc : z - center ≠ 0 := by
      intro heq
      have : z = center := sub_eq_zero.mp heq
      subst z
      have hz' : (0 : ℝ) = radius := by simpa using hz
      exact hr.ne' hz'.symm
    exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀ hzc)).continuousWithinAt
  have hhcont : ContinuousOn h (closedBall center radius) := hh.continuousOn
  have hi : CircleIntegrable h center radius :=
    (hhcont.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hzero : (∮ z in C(center, radius), h z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
      (s := ∅) countable_empty hhcont (fun z hz =>
        (hh z (ball_subset_closedBall hz.1)).differentiableAt)
  simp only [div_eq_mul_inv, contourResidue, circleIntegral.integral_add hp hi,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv center hr.ne',
    hzero, add_zero]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp

def escapingTailTransform (center : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(n : ℂ) * (z - center)) / (z - center)

theorem escaping_tail_keeps_residue (center : ℂ) (n : ℕ) :
    Tendsto (fun z => (z - center) * escapingTailTransform center n z)
      (𝓝[≠] center) (𝓝 1) := by
  have heq : (fun z => (z - center) * escapingTailTransform center n z) =ᶠ[𝓝[≠] center]
      fun z => Complex.exp (-(n : ℂ) * (z - center)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    dsimp [escapingTailTransform]
    have hzc : z - center ≠ 0 := sub_ne_zero.mpr hz
    field_simp
  apply Tendsto.congr' heq.symm
  have hc : ContinuousAt (fun z : ℂ => Complex.exp (-(n : ℂ) * (z - center))) center :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

def escapingTailPhysical (center : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  if (n : ℝ) < t then Complex.exp (center * (t : ℂ)) else 0

theorem escaping_tail_compact_eventually_zero (center : ℂ) (bound : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, t ≤ bound → escapingTailPhysical center n t = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt bound
  filter_upwards [eventually_ge_atTop N] with n hn
  intro t ht
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp [escapingTailPhysical, show ¬(n : ℝ) < t by linarith]

theorem escaping_tail_laplace_formula (center z : ℂ) (hz : center.re < z.re) (n : ℕ) :
    (∫ t : ℝ in Ioi (n : ℝ),
      Complex.exp (-z * (t : ℂ)) * Complex.exp (center * (t : ℂ))) =
      escapingTailTransform center n z := by
  have heq : (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
      Complex.exp (center * (t : ℂ))) =
      fun t : ℝ => Complex.exp ((center - z) * (t : ℂ)) := by
    funext t
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [heq, integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hz)]
  dsimp [escapingTailTransform]
  have harg : (center - z) * (n : ℂ) = -(n : ℂ) * (z - center) := by ring
  rw [harg]
  have hden : center - z = -(z - center) := by ring
  simp only [hden, div_neg, neg_div, neg_neg]

theorem escaping_tail_safe_halfPlane_tendsto (center z : ℂ) (hz : center.re < z.re) :
    Tendsto (fun n => escapingTailTransform center n z) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => Complex.exp (-(n : ℂ) * (z - center))) atTop (𝓝 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have heq : (fun n : ℕ => (-(n : ℂ) * (z - center)).re) =
        fun n : ℕ => (center.re - z.re) * (n : ℝ) := by
      funext n
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.natCast_re, Complex.natCast_im, neg_zero, zero_mul, sub_zero, Complex.sub_re]
      ring
    rw [heq]
    exact tendsto_const_nhds.neg_mul_atTop (sub_neg.mpr hz) tendsto_natCast_atTop_atTop
  simpa [escapingTailTransform] using he.div_const (z - center)

theorem escaping_tail_halfPlane_bound (center z : ℂ) (n : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hz : epsilon ≤ (z - center).re) :
    ‖escapingTailTransform center n z‖ ≤ Real.exp (-(n : ℝ) * epsilon) / epsilon := by
  have hxnorm : epsilon ≤ ‖z - center‖ := hz.trans (Complex.re_le_norm _)
  have hnum : ‖Complex.exp (-(n : ℂ) * (z - center))‖ ≤
      Real.exp (-(n : ℝ) * epsilon) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero, zero_mul, sub_zero]
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  dsimp [escapingTailTransform]
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le hepsilon hxnorm)

/-- Uniform decay on every closed half-plane strictly to the right of the
pole. These sets contain neighborhoods of all safe-half-plane points. -/
theorem escaping_tail_safe_halfPlane_uniform (center : ℂ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (tolerance : ℝ) (htol : 0 < tolerance) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, epsilon ≤ (z - center).re →
      ‖escapingTailTransform center n z‖ < tolerance := by
  have ht : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * epsilon) / epsilon)
      atTop (𝓝 0) := by
    have harg : Tendsto (fun n : ℕ => -(n : ℝ) * epsilon) atTop atBot := by
      have h := tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos hepsilon)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      simpa [mul_comm] using h
    simpa using (Real.tendsto_exp_atBot.comp harg).div_const epsilon
  filter_upwards [ht.eventually (Iio_mem_nhds htol)] with n hn
  intro z hz
  exact (escaping_tail_halfPlane_bound center z n epsilon hepsilon hz).trans_lt hn


/-- The common closed disk makes the contour coordinate the actual residue,
and gives boundary integrability without any further caller premise. -/
theorem simplePole_circleIntegrable (center residue : ℂ) (radius : ℝ)
    (hr : 0 < radius) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall center radius)) :
    CircleIntegrable (fun z => residue / (z-center) + h z) center radius := by
  apply ContinuousOn.circleIntegrable hr.le
  intro z hz
  have hzc : z-center ≠ 0 := by
    intro heq
    have : z = center := sub_eq_zero.mp heq
    subst z
    have hz' : (0 : ℝ) = radius := by simpa using hz
    exact hr.ne' hz'.symm
  exact ((continuousAt_const.div (continuousAt_id.sub continuousAt_const) hzc).continuousWithinAt).add
    ((hh.continuousOn.mono sphere_subset_closedBall) z hz)

/-- Actual simple-pole residues converge under uniform convergence on the
boundary of one common analytic disk. No convergence across a pole is inferred
from convergence confined to a disjoint safe half-plane. -/
theorem simplePole_residues_continuous_of_circle_uniform (center : ℂ) (radius : ℝ)
    (hr : 0 < radius) (residues : ℕ → ℂ) (residue : ℂ)
    (remainders : ℕ → ℂ → ℂ) (remainder : ℂ → ℂ)
    (hrem : ∀ n, AnalyticOnNhd ℂ (remainders n) (closedBall center radius))
    (hlimit : AnalyticOnNhd ℂ remainder (closedBall center radius))
    (error : ℕ → ℝ)
    (hbound : ∀ n z, z ∈ sphere center radius →
      ‖(residues n / (z-center) + remainders n z) -
        (residue / (z-center) + remainder z)‖ ≤ error n)
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto residues atTop (𝓝 residue) := by
  have h := contourResidue_continuous_of_circle_uniform center radius hr
    (fun n z => residues n / (z-center) + remainders n z)
    (fun z => residue / (z-center) + remainder z) error
    (fun n => simplePole_circleIntegrable center (residues n) radius hr _ (hrem n))
    (simplePole_circleIntegrable center residue radius hr _ hlimit) hbound herror
  have hseq : (fun n => contourResidue center radius
      (fun z => residues n / (z-center) + remainders n z)) = residues := by
    funext n
    exact contourResidue_eq_simplePole center (residues n) radius hr _ (hrem n)
  have hres := contourResidue_eq_simplePole center residue radius hr remainder hlimit
  rwa [hseq,hres] at h


/-- Actual fields meromorphic on one isolating closed disk. The center pole
may have any finite order; analyticity is certified across its boundary. -/
structure MeromorphicDiskData (center : ℂ) (radius : ℝ) where
  field : ℂ → ℂ
  meromorphic_center : MeromorphicAt field center
  analytic_punctured_disk : AnalyticOnNhd ℂ field (closedBall center radius \ {center})

/-- The residue is the normalized Cauchy integral of the actual field on the
certified common circle. It is not independent value data in the carrier. -/
def MeromorphicDiskData.residue {center : ℂ} {radius : ℝ}
    (f : MeromorphicDiskData center radius) : ℂ := contourResidue center radius f.field

theorem MeromorphicDiskData.circleIntegrable {center : ℂ} {radius : ℝ}
    (f : MeromorphicDiskData center radius) (hr : 0 < radius) :
    CircleIntegrable f.field center radius := by
  apply ContinuousOn.circleIntegrable hr.le
  apply f.analytic_punctured_disk.continuousOn.mono
  intro z hz
  refine ⟨sphere_subset_closedBall hz, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro heq
  subst z
  have hz' : (0 : ℝ) = radius := by simpa using hz
  exact hr.ne' hz'.symm

/-- Uniform convergence on an actual common isolating meromorphic circle
preserves residues, including higher-order center poles. -/
theorem residue_continuous_of_circle_uniform (center : ℂ) (radius : ℝ)
    (hr : 0 < radius) (f : ℕ → MeromorphicDiskData center radius)
    (g : MeromorphicDiskData center radius) (error : ℕ → ℝ)
    (hbound : ∀ n z, z ∈ sphere center radius → ‖(f n).field z - g.field z‖ ≤ error n)
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto (fun n => (f n).residue) atTop (𝓝 g.residue) :=
  contourResidue_continuous_of_circle_uniform center radius hr
    (fun n => (f n).field) g.field error (fun n => (f n).circleIntegrable hr)
    (g.circleIntegrable hr) hbound herror


theorem MeromorphicDiskData.residue_sub_norm_le {center : ℂ} {radius : ℝ}
    (f g : MeromorphicDiskData center radius) (hr : 0 < radius) (error : ℝ)
    (hbound : ∀ z ∈ sphere center radius, ‖f.field z-g.field z‖ ≤ error) :
    ‖f.residue-g.residue‖ ≤ radius*error := by
  unfold MeromorphicDiskData.residue
  rw [← contourResidue_sub (f.circleIntegrable hr) (g.circleIntegrable hr)]
  exact contourResidue_norm_le hr.le hbound

/-- A genuine arbitrary-order principal part, included as a scope control for
common-disk residue continuity. Order two has residue zero, not a simple pole. -/
def inversePowerMeromorphicDisk (center : ℂ) (radius : ℝ) (order : ℕ) :
    MeromorphicDiskData center radius where
  field z := ((z-center)^order)⁻¹
  meromorphic_center := (((analyticAt_id.sub analyticAt_const).meromorphicAt).pow order).inv
  analytic_punctured_disk := by
    intro z hz
    have hzc : z-center ≠ 0 := sub_ne_zero.mpr (by simpa only [Set.mem_singleton_iff] using hz.2)
    exact ((analyticAt_id.sub analyticAt_const).pow order).inv (pow_ne_zero _ hzc)

theorem inversePowerMeromorphicDisk_residue_two (center : ℂ) (radius : ℝ) :
    (inversePowerMeromorphicDisk center radius 2).residue = 0 := by
  unfold MeromorphicDiskData.residue inversePowerMeromorphicDisk contourResidue
  have heq : (fun z : ℂ => ((z-center)^2)⁻¹) = fun z => (z-center)^(-2 : ℤ) := by
    funext z
    simp
  rw [heq, circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1)]
  simp

end Zeta23.OPICA
