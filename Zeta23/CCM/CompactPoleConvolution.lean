import Zeta23.CCM.UniversalSincSourceFacade
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The compact pole operator in the actual source convolution

Two actual integrations by parts move P from the compact test to the
second factor. The second factor needs only C2 regularity, with no global
integrability or support premise. In particular (Pq)*(Pq)=q*(P²q) for the
unchanged original source; the two source factors are not defined equal.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.CCM

theorem integral_compactPole_left_eq_right {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) :
    (∫ x : ℝ, universalSincDifferential f x * g x) =
      ∫ x : ℝ, f x * universalSincDifferential g x := by
  have hfd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hgd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hfdd : Continuous (deriv (deriv f)) := hf.deriv'.continuous_deriv le_rfl
  have hgdd : Continuous (deriv (deriv g)) := hg.deriv'.continuous_deriv le_rfl
  have hfg : Integrable (fun x : ℝ => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hfgd : Integrable (fun x : ℝ => f x * deriv g x) :=
    (hf.continuous.mul hgd).integrable_of_hasCompactSupport hfc.mul_right
  have hfdg : Integrable (fun x : ℝ => deriv f x * g x) :=
    (hfd.mul hg.continuous).integrable_of_hasCompactSupport hfc.deriv.mul_right
  have hfdgd : Integrable (fun x : ℝ => deriv f x * deriv g x) :=
    (hfd.mul hgd).integrable_of_hasCompactSupport hfc.deriv.mul_right
  have hfddg : Integrable (fun x : ℝ => deriv (deriv f) x * g x) :=
    (hfdd.mul hg.continuous).integrable_of_hasCompactSupport hfc.deriv.deriv.mul_right
  have hfgdd : Integrable (fun x : ℝ => f x * deriv (deriv g) x) :=
    (hf.continuous.mul hgdd).integrable_of_hasCompactSupport hfc.mul_right
  have h1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := deriv g) (u' := deriv f) (v' := deriv (deriv g))
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hg.differentiable_deriv_two x).hasDerivAt) hfgdd hfdgd hfgd
  have h2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := deriv f) (v := g) (u' := deriv (deriv f)) (v' := deriv g)
    (fun x _ => (hf.differentiable_deriv_two x).hasDerivAt)
    (fun x _ => (hg.differentiable (by norm_num) x).hasDerivAt) hfdgd hfddg hfdg
  have hsecond : (∫ x : ℝ, deriv (deriv f) x * g x) =
      ∫ x : ℝ, f x * deriv (deriv g) x := by linear_combination h2 - h1
  have hleft : (fun x => universalSincDifferential f x * g x) =
      fun x => deriv (deriv f) x * g x - (1 / 4 : ℂ) * (f x * g x) := by
    funext x
    unfold universalSincDifferential
    ring
  have hright : (fun x => f x * universalSincDifferential g x) =
      fun x => f x * deriv (deriv g) x - (1 / 4 : ℂ) * (f x * g x) := by
    funext x
    unfold universalSincDifferential
    ring
  rw [hleft, hright, integral_sub hfddg (hfg.const_mul (1 / 4 : ℂ)),
    integral_sub hfgdd (hfg.const_mul (1 / 4 : ℂ)), hsecond]

theorem universalSincDifferential_reflected (g : ℝ → ℂ) (t x : ℝ) :
    universalSincDifferential (fun y => g (t - y)) x =
      universalSincDifferential g (t - x) := by
  have h := congrFun (iteratedDeriv_comp_const_sub 2 g t) x
  have hsecond : deriv (deriv (fun y => g (t - y))) x = deriv (deriv g) (t - x) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, neg_one_sq, one_smul] using h
  simp only [universalSincDifferential, hsecond]

theorem compactPole_convolution_left_eq_right {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    (∫ x : ℝ, universalSincDifferential f x * g (t - x)) =
      ∫ x : ℝ, f x * universalSincDifferential g (t - x) := by
  have h := integral_compactPole_left_eq_right hf hfc
    (hg.comp (contDiff_const.sub contDiff_id) : ContDiff ℝ 2 (fun x => g (t - x)))
  change (∫ x : ℝ, universalSincDifferential f x * g (t - x)) =
    ∫ x : ℝ, f x * universalSincDifferential (fun y => g (t - y)) x at h
  simpa only [universalSincDifferential_reflected] using h

/-- The literal original correlation source is q*j, with j=P²q. -/
theorem universalSincKernel_selfConvolution_eq_source_second {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (∫ x : ℝ, universalSincKernel s x * universalSincKernel s (t - x)) =
      ∫ x : ℝ, UniversalSinc.originalDensityComplex s x * universalSincSecondKernel s (t - x) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (UniversalSinc.originalDensityComplex s) := by
    rw [← UniversalSinc.inverseCandidate_eq_originalDensityComplex hs]
    exact UniversalSinc.contDiff_inverseCandidate hs
  exact compactPole_convolution_left_eq_right
    (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (UniversalSinc.originalDensityComplex_hasCompactSupport hs)
    ((universalSincKernel_contDiff hs).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) t

end Zeta23.CCM

#print axioms Zeta23.CCM.integral_compactPole_left_eq_right
#print axioms Zeta23.CCM.universalSincDifferential_reflected
#print axioms Zeta23.CCM.compactPole_convolution_left_eq_right
#print axioms Zeta23.CCM.universalSincKernel_selfConvolution_eq_source_second
