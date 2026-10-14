import Zeta23.CCM.OriginalSincNativeConvolution
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The literal P=∂²-1/4 commutes with all four prime-history arguments

A translated or reflected original prime history has the same P-image
as the actual fixed X field at that translated/reflected argument.
The two reflection signs cancel in the second derivative.

This is a local differentiable identity; no global weighted L2 premise
or source-specific growth bound is inserted. It provides a rigorous
bridge for the forthcoming four-history inverse-duality estimates.
-/

noncomputable section
open Set MeasureTheory
namespace Zeta23.CCM

private theorem deriv_translate_const
    {f : ℝ → ℂ} (hf : Differentiable ℝ f) (b x : ℝ) :
    HasDerivAt (fun t : ℝ => f (t - b)) (deriv f (x - b)) x := by
  simpa only [Function.comp_def, id_eq, one_smul] using
    ((hf (x - b)).hasDerivAt.scomp x
      ((hasDerivAt_id x).sub_const b))

private theorem deriv_reflect_const
    {f : ℝ → ℂ} (hf : Differentiable ℝ f) (b x : ℝ) :
    HasDerivAt (fun t : ℝ => f (b - t)) (-(deriv f (b - x))) x := by
  have hinner : HasDerivAt (fun t : ℝ => b - t) (-1) x := by
    simpa only using ((hasDerivAt_id x).const_sub b)
  simpa only [Function.comp_def, neg_one_smul] using
    ((hf (b - x)).hasDerivAt.scomp x hinner)

/-- Translation covariance for the exact native differential operator. -/
theorem nativePoleDifferential_translate
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (b x : ℝ) :
    universalSincDifferential (fun t : ℝ => f (t - b)) x =
      universalSincDifferential f (x - b) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (deriv f) :=
    (hf.deriv').differentiable (by norm_num)
  have hFirst : deriv (fun t : ℝ => f (t - b)) =
      fun t : ℝ => deriv f (t - b) := by
    funext t
    exact (deriv_translate_const hfd b t).deriv
  have hSecond : deriv (deriv (fun t : ℝ => f (t - b))) x =
      deriv (deriv f) (x - b) := by
    rw [hFirst]
    exact (deriv_translate_const hfdd b x).deriv
  unfold universalSincDifferential
  rw [hSecond]

/-- Reflection covariance: a second derivative removes both minus signs. -/
theorem nativePoleDifferential_reflect
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (b x : ℝ) :
    universalSincDifferential (fun t : ℝ => f (b - t)) x =
      universalSincDifferential f (b - x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (deriv f) :=
    (hf.deriv').differentiable (by norm_num)
  have hFirst : deriv (fun t : ℝ => f (b - t)) =
      fun t : ℝ => -(deriv f (b - t)) := by
    funext t
    exact (deriv_reflect_const hfd b t).deriv
  have hSecond : deriv (deriv (fun t : ℝ => f (b - t))) x =
      deriv (deriv f) (b - x) := by
    rw [hFirst]
    have hh : HasDerivAt
        (fun t : ℝ => -(deriv f (b - t)))
        (deriv (deriv f) (b - x)) x := by
      simpa only [neg_neg] using (deriv_reflect_const hfdd b x).neg
    exact hh.deriv
  unfold universalSincDifferential
  rw [hSecond]

/-- The fixed native one-sided F_k/X pairing survives ALL four
literal original source translations, including two reflections. -/
theorem originalDetector_fourPrimeHistory_poleImages (a x : ℝ) :
    let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
    let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
    let F := nativeOriginalKernelPrimeField
    universalSincDifferential (fun t : ℝ => F (t - c)) x =
      (nativeOriginalPrimeField (x - c) : ℂ) ∧
    universalSincDifferential (fun t : ℝ => F (c - t)) x =
      (nativeOriginalPrimeField (c - x) : ℂ) ∧
    universalSincDifferential (fun t : ℝ => F (L - t - c)) x =
      (nativeOriginalPrimeField (L - x - c) : ℂ) ∧
    universalSincDifferential (fun t : ℝ => F (t + c - L)) x =
      (nativeOriginalPrimeField (x + c - L) : ℂ) := by
  dsimp only
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
  have hF : ContDiff ℝ 2 nativeOriginalKernelPrimeField :=
    nativeOriginalKernelPrimeField_contDiff.of_le le_top
  have hPole := nativeOriginalKernelPrimeField_poleImage
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (nativePoleDifferential_translate hF c x).trans
      (congrFun hPole (x - c))
  · exact (nativePoleDifferential_reflect hF c x).trans
      (congrFun hPole (c - x))
  · have harg : (fun t : ℝ => nativeOriginalKernelPrimeField (L - t - c)) =
        fun t : ℝ => nativeOriginalKernelPrimeField ((L - c) - t) := by
      funext t
      congr 1
      ring
    rw [harg]
    have hb : (L - c) - x = L - x - c := by ring
    simpa only [hb] using
      (nativePoleDifferential_reflect hF (L - c) x).trans
        (congrFun hPole ((L - c) - x))
  · have harg : (fun t : ℝ => nativeOriginalKernelPrimeField (t + c - L)) =
        fun t : ℝ => nativeOriginalKernelPrimeField (t - (L - c)) := by
      funext t
      congr 1
      ring
    rw [harg]
    have hb : x - (L - c) = x + c - L := by ring
    simpa only [hb] using
      (nativePoleDifferential_translate hF (L - c) x).trans
        (congrFun hPole (x - (L - c)))

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleDifferential_translate
#print axioms Zeta23.CCM.nativePoleDifferential_reflect
#print axioms Zeta23.CCM.originalDetector_fourPrimeHistory_poleImages
