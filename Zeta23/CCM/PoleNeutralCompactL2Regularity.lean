import Zeta23.CCM.PoleNeutralCompactInverse
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The literal compact pole inverse for a general compact L2 source

No continuity of the source is assumed. The same finite primitives have
continuous representatives, compact support and clamped value/explicit-first-
derivative traces. Both differential equations hold almost everywhere, and
all three actual jet representatives belong to L2. These are supporting
regularity results; the sharp norm bound and weak/Sobolev interface require
their own proofs.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

private theorem poleExponential_continuous (r : ℝ) : Continuous (nativePoleExponential r) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem nativePoleWeightedSource_locallyIntegrable {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (r : ℝ) :
    LocallyIntegrable (fun x : ℝ => nativePoleExponential r x * f x) volume :=
  (hf.locallyIntegrable (by norm_num)).continuous_mul (poleExponential_continuous r)

theorem nativePolePrimitive_continuous_of_memLp (s r : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : Continuous (nativePolePrimitive s r f) := by
  apply intervalIntegral.continuous_primitive (fun a b => ?_) (-s)
  exact ((nativePoleWeightedSource_locallyIntegrable hf r).integrableOn_isCompact
    isCompact_uIcc).intervalIntegrable

theorem nativePoleCompactInverse_continuous_of_memLp (s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : Continuous (nativePoleCompactInverse s f) :=
  ((poleExponential_continuous (1 / 2)).mul (nativePolePrimitive_continuous_of_memLp s (-1 / 2) hf)).sub
    ((poleExponential_continuous (-1 / 2)).mul (nativePolePrimitive_continuous_of_memLp s (1 / 2) hf))

theorem nativePoleCompactInverseDerivative_continuous_of_memLp (s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) : Continuous (nativePoleCompactInverseDerivative s f) :=
  continuous_const.mul
    (((poleExponential_continuous (1 / 2)).mul
      (nativePolePrimitive_continuous_of_memLp s (-1 / 2) hf)).add
      ((poleExponential_continuous (-1 / 2)).mul
        (nativePolePrimitive_continuous_of_memLp s (1 / 2) hf)))

private theorem poleExponential_half_product (x : ℝ) :
    nativePoleExponential (1 / 2) x * nativePoleExponential (-1 / 2) x = 1 := by
  unfold nativePoleExponential
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have heq : (1 / 2 : ℝ) * x + (-1 / 2 : ℝ) * x = 0 := by ring
  rw [heq, Real.exp_zero, Complex.ofReal_one]

theorem nativePoleCompactInverse_ae_hasDerivAt (s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    ∀ᵐ x : ℝ, HasDerivAt (nativePoleCompactInverse s f)
      (nativePoleCompactInverseDerivative s f x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (nativePoleWeightedSource_locallyIntegrable hf (-1 / 2)),
    LocallyIntegrable.ae_hasDerivAt_integral
      (nativePoleWeightedSource_locallyIntegrable hf (1 / 2))] with x hA hB
  have h := ((hasDerivAt_nativePoleExponential (1 / 2) x).mul (hA (-s))).sub
    ((hasDerivAt_nativePoleExponential (-1 / 2) x).mul (hB (-s)))
  convert! h using 1 <;> first
    | rfl
    | (simp only [nativePoleCompactInverse, nativePoleCompactInverseDerivative,
        nativePolePrimitive, Pi.mul_apply, Pi.sub_apply]
       push_cast
       ring)

theorem nativePoleCompactInverseDerivative_ae_hasDerivAt (s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    ∀ᵐ x : ℝ, HasDerivAt (nativePoleCompactInverseDerivative s f)
      ((1 / 4 : ℂ) * nativePoleCompactInverse s f x + f x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (nativePoleWeightedSource_locallyIntegrable hf (-1 / 2)),
    LocallyIntegrable.ae_hasDerivAt_integral
      (nativePoleWeightedSource_locallyIntegrable hf (1 / 2))] with x hA hB
  have h := (((hasDerivAt_nativePoleExponential (1 / 2) x).mul (hA (-s))).add
    ((hasDerivAt_nativePoleExponential (-1 / 2) x).mul (hB (-s)))).const_mul (1 / 2 : ℂ)
  convert! h using 1 <;> first
    | rfl
    | (simp only [nativePoleCompactInverse, nativePoleCompactInverseDerivative,
        nativePolePrimitive, Pi.mul_apply, Pi.add_apply]
       have he := poleExponential_half_product x
       push_cast
       linear_combination -f x * he)

private theorem continuous_supported_endpoint_values {s : ℝ} {h : ℝ → ℂ}
    (hh : Continuous h) (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → h x = 0) :
    h (-s) = 0 ∧ h s = 0 := by
  have hclosed : IsClosed {x : ℝ | h x = 0} := isClosed_eq hh continuous_const
  constructor
  · have hleft : Iio (-s) ⊆ {x : ℝ | h x = 0} := by
      intro x hx
      exact hsupport x (fun hmem => (not_le_of_gt hx) hmem.1)
    exact (hclosed.closure_subset_iff.mpr hleft)
      (by simpa only [closure_Iio, mem_Iic] using (le_rfl : -s ≤ -s))
  · have hright : Ioi s ⊆ {x : ℝ | h x = 0} := by
      intro x hx
      exact hsupport x (fun hmem => (not_le_of_gt hx) hmem.2)
    exact (hclosed.closure_subset_iff.mpr hright)
      (by simpa only [closure_Ioi, mem_Ici] using (le_rfl : s ≤ s))

/-- Endpoint values of the actual continuous potential and its explicit
first-jet representative; no pointwise second derivative of the L2 source
is asserted. -/
theorem nativePoleCompactInverse_memLp_clamped_values {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    nativePoleCompactInverse s f (-s) = 0 ∧ nativePoleCompactInverse s f s = 0 ∧
      nativePoleCompactInverseDerivative s f (-s) = 0 ∧
      nativePoleCompactInverseDerivative s f s = 0 := by
  have hv := continuous_supported_endpoint_values (nativePoleCompactInverse_continuous_of_memLp s hf)
    (fun x hx => nativePoleCompactInverse_zero_outside hs hsupport hplus hminus hx)
  have hd := continuous_supported_endpoint_values
    (nativePoleCompactInverseDerivative_continuous_of_memLp s hf)
    (fun x hx => nativePoleCompactInverseDerivative_zero_outside hs hsupport hplus hminus hx)
  exact ⟨hv.1, hv.2, hd.1, hd.2⟩

/-- General compact pole-neutral L2 inputs give three actual L2 jet
representatives; continuity of the input is not a premise. -/
theorem nativePoleCompactInverse_memLp_jet_representatives {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    MemLp (nativePoleCompactInverse s f) 2 volume ∧
      MemLp (nativePoleCompactInverseDerivative s f) 2 volume ∧
      MemLp (fun x : ℝ => (1 / 4 : ℂ) * nativePoleCompactInverse s f x + f x) 2 volume := by
  have hg : MemLp (nativePoleCompactInverse s f) 2 volume :=
    (nativePoleCompactInverse_continuous_of_memLp s hf).memLp_of_hasCompactSupport
      (nativePoleCompactInverse_hasCompactSupport hs hsupport hplus hminus)
  have hd : MemLp (nativePoleCompactInverseDerivative s f) 2 volume :=
    (nativePoleCompactInverseDerivative_continuous_of_memLp s hf).memLp_of_hasCompactSupport
      (nativePoleCompactInverseDerivative_hasCompactSupport hs hsupport hplus hminus)
  exact ⟨hg, hd, (hg.const_mul (1 / 4 : ℂ)).add hf⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleWeightedSource_locallyIntegrable
#print axioms Zeta23.CCM.nativePolePrimitive_continuous_of_memLp
#print axioms Zeta23.CCM.nativePoleCompactInverse_continuous_of_memLp
#print axioms Zeta23.CCM.nativePoleCompactInverseDerivative_continuous_of_memLp
#print axioms Zeta23.CCM.nativePoleCompactInverse_ae_hasDerivAt
#print axioms Zeta23.CCM.nativePoleCompactInverseDerivative_ae_hasDerivAt
#print axioms Zeta23.CCM.nativePoleCompactInverse_memLp_clamped_values
#print axioms Zeta23.CCM.nativePoleCompactInverse_memLp_jet_representatives
