import Zeta23.RHReference.Perron.LiteralPerronRemainder
import Zeta23.Analytic.RectangleLogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Abel

/-!
The finite rectangle identity for the literal Perron integrand. The pure
double-pole term is the derivative of a reciprocal and its four edge
increments cancel. The historical simple-pole residue theorem then
applies to the exact subtracted integrand.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Topology Interval

namespace Zeta23.RHReference

private def reciprocalPrimitive (a p s : ℂ) : ℂ :=
  -a * (s - p)⁻¹

private theorem hasDerivAt_reciprocalPrimitive (a p : ℂ) {s : ℂ} (hs : s ≠ p) :
    HasDerivAt (reciprocalPrimitive a p) (a / (s - p)^2) s := by
  have hp := (((hasDerivAt_id s).sub_const p).inv (sub_ne_zero.mpr hs)).const_mul (-a)
  change HasDerivAt (fun z : ℂ => -a * (z - p)⁻¹) (a / (s - p)^2) s
  simpa [div_eq_mul_inv, mul_assoc] using hp

private theorem differentiableAt_doublePole (a p : ℂ) {s : ℂ} (hs : s ≠ p) :
    DifferentiableAt ℂ (fun s : ℂ => a / (s - p)^2) s :=
  (differentiableAt_const a).div ((differentiableAt_id.sub_const p).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hs))

/-- The reciprocal derivative has zero contour integral whenever its pole
is off the border. The location of its pole relative to the interior does
not matter. -/
theorem rectangleIntegral_doublePole_zero {z w p : ℂ} (a : ℂ)
    (hp : p ∉ RectangleBorder z w) :
    RectangleIntegral' (fun s => a / (s - p)^2) z w = 0 := by
  let D : ℂ → ℂ := fun s => a / (s - p)^2
  let G := reciprocalPrimitive a p
  have hF : ContinuousOn D (RectangleBorder z w) :=
    fun s hs => (differentiableAt_doublePole a p (fun he => hp (he ▸ hs))).continuousAt.continuousWithinAt
  have hI := hF.rectangleBorder_integrable
  have hH (y : ℝ)
      (hPath : MapsTo (fun t : ℝ => (t : ℂ) + y * I) [[z.re, w.re]] (RectangleBorder z w))
      (hInt : IntervalIntegrable (fun t : ℝ => D (t + y * I)) volume z.re w.re) :
      HIntegral D z.re w.re y = G (w.re + y * I) - G (z.re + y * I) := by
    unfold HIntegral
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => G (t + y * I))
      (fun t ht => ?_) hInt
    have hne : (t : ℂ) + y * I ≠ p := fun h => hp (h ▸ hPath ht)
    have hD := hasDerivAt_reciprocalPrimitive a p hne
    have hP := (hasDerivAt_id (t : ℂ)).add_const ((y : ℂ) * I)
    simpa [G, D, mul_one, Function.comp_def] using (hD.comp (t : ℂ) hP).comp_ofReal
  have hV (y : ℝ)
      (hPath : MapsTo (fun t : ℝ => (y : ℂ) + t * I) [[z.im, w.im]] (RectangleBorder z w))
      (hInt : IntervalIntegrable (fun t : ℝ => D (y + t * I)) volume z.im w.im) :
      VIntegral D y z.im w.im = G (y + w.im * I) - G (y + z.im * I) := by
    change I * (∫ t : ℝ in z.im..w.im, D (y + t * I)) = _
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => G (y + t * I))
      (fun t ht => ?_) (hInt.const_mul I)
    have hne : (y : ℂ) + t * I ≠ p := fun h => hp (h ▸ hPath ht)
    have hD := hasDerivAt_reciprocalPrimitive a p hne
    have hP := ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (y : ℂ)
    simpa [G, D, mul_comm, Function.comp_def] using (hD.comp (t : ℂ) hP).comp_ofReal
  change (1 / (2 * Real.pi * I) : ℂ) • RectangleIntegral D z w = _
  unfold RectangleIntegral
  rw [hH z.im (mapsTo_rectangleBorder_left_im z w) hI.1,
      hH w.im (mapsTo_rectangleBorder_right_im z w) hI.2.1,
      hV w.re (mapsTo_rectangleBorder_right_re z w) hI.2.2.1,
      hV z.re (mapsTo_rectangleBorder_left_re z w) hI.2.2.2]
  have hcancel :
      G (w.re + z.im * I) - G (z.re + z.im * I) -
        (G (w.re + w.im * I) - G (z.re + w.im * I)) +
        (G (w.re + w.im * I) - G (w.re + z.im * I)) -
        (G (z.re + w.im * I) - G (z.re + z.im * I)) = 0 := by abel
  rw [hcancel, smul_zero]

/-- The exact native centering is the normalized finite rectangle integral. -/
theorem literalPerron_rectangle_eq_residue {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hOne : Rectangle z w ∈ 𝓝 (1 : ℂ))
    (hf : HolomorphicOn (literalPerronIntegrand x) (Rectangle z w \ {1})) :
    RectangleIntegral' (literalPerronIntegrand x) z w = literalPerronResidue x := by
  let D := literalPerronDoubleTerm x
  let F := literalPerronIntegrand x
  have hD : HolomorphicOn D (Rectangle z w \ {1}) := by
    intro s hs
    exact (differentiableAt_doublePole (x : ℂ) 1 (show s ≠ 1 from hs.2)).differentiableWithinAt
  have hFD : HolomorphicOn (F - D) (Rectangle z w \ {1}) := hf.sub hD
  have hResidue :
      RectangleIntegral' (F - D) z w = literalPerronResidue x := by
    have h := Zeta23.Analytic.residueTheorem_finset (f := F - D) hre him
      ({1} : Finset ℂ) (fun _ => literalPerronResidue x)
      (fun p hp => by simpa [show p = 1 from Finset.mem_singleton.mp hp] using hOne)
      (by simpa using hFD)
      (fun p hp => by
        simpa [show p = 1 from Finset.mem_singleton.mp hp, F, D, Pi.sub_def] using
          literalPerron_sub_double_residue_bigO hx)
    simpa using h
  have hDouble : RectangleIntegral' D z w = 0 :=
    rectangleIntegral_doublePole_zero (x : ℂ) (not_mem_rectangleBorder_of_rectangle_mem_nhds hOne)
  have hSplit : RectangleIntegral' F z w =
      RectangleIntegral' (F - D) z w + RectangleIntegral' D z w := by
    conv_lhs => rw [show F = (F - D) + D by abel]
    unfold RectangleIntegral'
    rw [(hFD.rectangleBorderIntegrable' hOne).add (hD.rectangleBorderIntegrable' hOne), smul_add]
  calc
    RectangleIntegral' F z w =
        RectangleIntegral' (F - D) z w + RectangleIntegral' D z w := hSplit
    _ = _ := by rw [hResidue, hDouble, add_zero]

/-- A single exact zero-free half-plane suffices for the finite rectangle
identity. The contour rectangle lies strictly to the right of its threshold. -/
theorem literalPerron_rectangle_eq_residue_of_fixed_strip {x β : ℝ} (hx : 0 < x)
    (hβ : 0 ≤ β)
    (hzero : ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0) {z w : ℂ}
    (hleft : β < z.re) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hOne : Rectangle z w ∈ 𝓝 (1 : ℂ)) :
    RectangleIntegral' (literalPerronIntegrand x) z w = literalPerronResidue x := by
  apply literalPerron_rectangle_eq_residue hx hre him hOne
  intro s hs
  have hreal := hs.1.1
  rw [uIcc_of_le hre] at hreal
  have hright : β < s.re := hleft.trans_le hreal.1
  have hs1 : s ≠ 1 := hs.2
  have hs0 : s ≠ 0 := by
    intro hs0
    rw [hs0, Complex.zero_re] at hright
    exact (not_lt_of_ge hβ) hright
  have hζ : AnalyticAt ℂ riemannZeta s :=
    differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton s hs1
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s := by
    simp_rw [Complex.cpow_def, if_neg hx0]
    exact analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id)
  have hlog := hζ.deriv.neg.div hζ (hzero s hright hs1)
  have hdenom : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) s :=
    analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
  exact ((hlog.mul hpow).div hdenom (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).differentiableAt.differentiableWithinAt

#print axioms Zeta23.RHReference.rectangleIntegral_doublePole_zero
#print axioms Zeta23.RHReference.literalPerron_rectangle_eq_residue
#print axioms Zeta23.RHReference.literalPerron_rectangle_eq_residue_of_fixed_strip

end Zeta23.RHReference
