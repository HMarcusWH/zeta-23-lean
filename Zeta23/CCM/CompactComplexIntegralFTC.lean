/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The primitive argument is adapted from Mathlib's AbsolutelyContinuous.lean.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Complex absolutely continuous primitives and their exact integral identity

The primitive argument extends the real-valued Mathlib proof to complex
values, using the norm of the Bochner integral. It supplies the missing
complex-valued FTC interface for general compact L2 pole sources.
-/

noncomputable section

open MeasureTheory Set Filter Function AbsolutelyContinuousOnInterval
open scoped Topology

namespace Zeta23.CCM

theorem complex_intervalPrimitive_absolutelyContinuous {f : ℝ → ℂ} {a b c : ℝ}
    (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) => ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hsmall : Tendsto (fun i => ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
      (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have hreal := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hsmall
  refine squeeze_zero' ?_ ?_ hreal
  · filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  simp only [comp_apply, s]
  have hwithin : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b := eventually_inf_principal.mpr (by simp)
  filter_upwards [hwithin] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
      (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
      (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi))]
    simpa only [uIoc_comm] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f)
        (a := (I i).2) (b := (I i).1) (μ := volume))
  · intro i hi
    unfold IntegrableOn
    have hsubset := uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact IntegrableOn.mono_set h.def'.norm hsubset |>.integrable

/-- Complex FTC from actual absolute continuity and actual a.e. derivatives.
No merely continuous Cantor-type primitive can satisfy these premises. -/
theorem complex_integral_eq_sub_of_ac_ae {f f' : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : IntervalIntegrable f' volume a b)
    (hderiv : ∀ᵐ x : ℝ, x ∈ uIcc a b → HasDerivAt f (f' x) x) :
    (∫ x in a..b, f' x) = f b - f a := by
  let g := fun x : ℝ => f x - ∫ t in a..x, f' t
  have hg : AbsolutelyContinuousOnInterval g a b :=
    hf.sub (complex_intervalPrimitive_absolutelyContinuous hf' (by simp))
  have hz : ∀ᵐ x : ℝ, x ∈ uIcc a b → HasDerivAt g 0 x := by
    filter_upwards [hderiv, IntervalIntegrable.ae_hasDerivAt_integral hf'] with x hx hix hmem
    convert! (hx hmem).sub (hix hmem a (by simp)) using 1
    simp
  obtain ⟨C, hC⟩ := hg.const_of_ae_hasDerivAt_zero hz
  have hleft := hC a (by simp)
  have hright := hC b (by simp)
  dsimp [g] at hleft hright
  simp only [intervalIntegral.integral_same, sub_zero] at hleft
  linear_combination hleft - hright

end Zeta23.CCM

#print axioms Zeta23.CCM.complex_intervalPrimitive_absolutelyContinuous
#print axioms Zeta23.CCM.complex_integral_eq_sub_of_ac_ae
