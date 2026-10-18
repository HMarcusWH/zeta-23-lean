import Zeta23.CCM.NativeDampedCompletionPrerequisites
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The actual damped native completion as a bounded L2 operator

The operator is the strong integral of the literal floor kernel times the
actual delay x-t on L2 equivalence classes. Integrability and the operator
bound follow from strong continuity of delays, their isometry, and the
proved mass certificate for the unchanged kernel. No Young bound is an
input. Pointwise convolution identification requires its separate Fubini
bridge. No inverse, range membership, prime-field L2 membership, or RH
conclusion follows from this construction alone.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ENNReal

namespace Zeta23.CCM

abbrev NativeCompletionL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Strong continuity concerns the L2 class, not a chosen representative. -/
theorem nativeCompletionL2Delay_continuous (f : NativeCompletionL2) :
    Continuous (fun t : ℝ => nativeCompletionL2Delay t f) := by
  let shifts : ℝ → C(ℝ, ℝ) := fun t => ⟨fun x => x - t, continuous_id.sub continuous_const⟩
  have hshifts : Continuous shifts :=
    ContinuousMap.continuous_of_continuous_uncurry shifts
      (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hshifts
    (fun t => measurePreserving_sub_right volume t) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

def nativeDampedCompletionL2Integrand (epsilon : ℝ) (f : NativeCompletionL2)
    (t : ℝ) : NativeCompletionL2 :=
  nativeDampedCompletionKernel epsilon t • nativeCompletionL2Delay t f

theorem nativeDampedCompletionL2Integrand_norm (epsilon t : ℝ) (f : NativeCompletionL2) :
    ‖nativeDampedCompletionL2Integrand epsilon f t‖ =
      ‖nativeDampedCompletionKernel epsilon t‖ * ‖f‖ := by
  rw [nativeDampedCompletionL2Integrand, norm_smul, nativeCompletionL2Delay_norm]

/-- This is genuine Bochner integrability, before defining a linear map. -/
theorem nativeDampedCompletionL2Integrand_integrable {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (f : NativeCompletionL2) :
    Integrable (nativeDampedCompletionL2Integrand epsilon f) := by
  have hstrong : AEStronglyMeasurable (nativeDampedCompletionL2Integrand epsilon f) :=
    (nativeDampedCompletionKernel_measurable epsilon).aestronglyMeasurable.smul
      (nativeCompletionL2Delay_continuous f).aestronglyMeasurable
  apply ((nativeDampedCompletionKernel_integrable hepsilon).norm.mul_const ‖f‖).mono' hstrong
  exact Filter.Eventually.of_forall fun t => (nativeDampedCompletionL2Integrand_norm epsilon t f).le

def nativeDampedCompletionL2Value (epsilon : ℝ) (f : NativeCompletionL2) : NativeCompletionL2 :=
  ∫ t : ℝ, nativeDampedCompletionL2Integrand epsilon f t

theorem nativeDampedCompletionL2Value_norm_le {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (f : NativeCompletionL2) :
    ‖nativeDampedCompletionL2Value epsilon f‖ ≤
      (∫ t : ℝ, ‖nativeDampedCompletionKernel epsilon t‖) * ‖f‖ := by
  unfold nativeDampedCompletionL2Value
  calc
    _ ≤ ∫ t : ℝ, ‖nativeDampedCompletionL2Integrand epsilon f t‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [nativeDampedCompletionL2Integrand_norm]
      rw [integral_mul_const]

def nativeDampedCompletionL2LinearMap (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    NativeCompletionL2 →ₗ[ℂ] NativeCompletionL2 where
  toFun := nativeDampedCompletionL2Value epsilon
  map_add' f g := by
    unfold nativeDampedCompletionL2Value
    have hpoint : nativeDampedCompletionL2Integrand epsilon (f + g) =
        fun t => nativeDampedCompletionL2Integrand epsilon f t +
          nativeDampedCompletionL2Integrand epsilon g t := by
      funext t
      simp only [nativeDampedCompletionL2Integrand, map_add, smul_add]
    rw [hpoint, integral_add (nativeDampedCompletionL2Integrand_integrable hepsilon f)
      (nativeDampedCompletionL2Integrand_integrable hepsilon g)]
  map_smul' c f := by
    unfold nativeDampedCompletionL2Value
    have hpoint : nativeDampedCompletionL2Integrand epsilon (c • f) =
        fun t => c • nativeDampedCompletionL2Integrand epsilon f t := by
      funext t
      simp only [nativeDampedCompletionL2Integrand, map_smul]
      exact smul_comm _ _ _
    rw [hpoint, integral_smul]
    rfl

/-- The actual full-line L2 operator; the nonnegative damping condition
is exactly the condition needed for the inherited kernel bound. -/
def nativeDampedCompletionL2Operator (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    NativeCompletionL2 →L[ℂ] NativeCompletionL2 :=
  (nativeDampedCompletionL2LinearMap epsilon hepsilon).mkContinuous
    (∫ t : ℝ, ‖nativeDampedCompletionKernel epsilon t‖)
    (nativeDampedCompletionL2Value_norm_le hepsilon)

theorem nativeDampedCompletionL2Operator_apply (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (f : NativeCompletionL2) :
    nativeDampedCompletionL2Operator epsilon hepsilon f =
      ∫ t : ℝ, nativeDampedCompletionKernel epsilon t • nativeCompletionL2Delay t f := rfl

theorem nativeDampedCompletionL2Operator_norm_le_kernel_mass (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    ‖nativeDampedCompletionL2Operator epsilon hepsilon‖ ≤
      ∫ t : ℝ, ‖nativeDampedCompletionKernel epsilon t‖ :=
  LinearMap.mkContinuous_norm_le _
    (integral_nonneg (fun _ => norm_nonneg _))
    (nativeDampedCompletionL2Value_norm_le hepsilon)

theorem nativeDampedCompletionL2Operator_norm_lt_605_div_621 (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    ‖nativeDampedCompletionL2Operator epsilon hepsilon‖ < (605 / 621 : ℝ) :=
  (nativeDampedCompletionL2Operator_norm_le_kernel_mass epsilon hepsilon).trans_lt
    (nativeDampedCompletionKernel_integral_norm_lt_605_div_621 hepsilon)

theorem nativeDampedCompletionL2Operator_norm_lt_one (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) : ‖nativeDampedCompletionL2Operator epsilon hepsilon‖ < 1 :=
  (nativeDampedCompletionL2Operator_norm_lt_605_div_621 epsilon hepsilon).trans (by norm_num)

/-- The actual causal equivalence classes form a complex submodule. -/
def nativeCompletionCausalL2 : Submodule ℂ NativeCompletionL2 where
  carrier := {f | ∀ᵐ x : ℝ, x < 0 → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx
    intro _
    exact hx
  add_mem' := by
    intro f g hf hg
    change ∀ᵐ x : ℝ, x < 0 → (f + g) x = 0
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx
    intro hxneg
    rw [hx, Pi.add_apply, hfx hxneg, hgx hxneg, add_zero]
  smul_mem' := by
    intro c f hf
    change ∀ᵐ x : ℝ, x < 0 → (c • f) x = 0
    filter_upwards [Lp.coeFn_smul c f, hf] with x hx hfx
    intro hxneg
    rw [hx, Pi.smul_apply, hfx hxneg, smul_zero]

/-- Closedness is proved from actual L2 convergence and an a.e. convergent
subsequence, rather than assuming support passes through strong integrals. -/
theorem nativeCompletionCausalL2_isClosed :
    IsClosed (nativeCompletionCausalL2 : Set NativeCompletionL2) := by
  apply IsSeqClosed.isClosed
  intro fs f hfs hlim
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ x : ℝ, ∀ n : ℕ, x < 0 → fs n x = 0 :=
    ae_all_iff.mpr hfs
  change ∀ᵐ x : ℝ, x < 0 → f x = 0
  filter_upwards [hae, hall] with x hx hfx
  intro hxneg
  have hzero : (fun n : ℕ => fs (ns n) x) = fun _ => (0 : ℂ) :=
    funext (fun n => hfx (ns n) hxneg)
  rw [hzero] at hx
  exact tendsto_nhds_unique hx tendsto_const_nhds

instance nativeCompletionCausalL2_completeSpace : CompleteSpace nativeCompletionCausalL2 :=
  nativeCompletionCausalL2_isClosed.completeSpace_coe

theorem nativeDampedCompletionL2Integrand_causal (epsilon : ℝ)
    (f : nativeCompletionCausalL2) (t : ℝ) :
    nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) t ∈
      nativeCompletionCausalL2 := by
  by_cases ht : 0 ≤ t
  · have hd := nativeCompletionL2Delay_causal ht (f : NativeCompletionL2) f.property
    change ∀ᵐ x : ℝ, x < 0 →
      nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) t x = 0
    filter_upwards [Lp.coeFn_smul (nativeDampedCompletionKernel epsilon t)
      (nativeCompletionL2Delay t (f : NativeCompletionL2)), hd] with x hx hdx
    intro hxneg
    rw [nativeDampedCompletionL2Integrand, hx, Pi.smul_apply, hdx hxneg, smul_zero]
  · rw [nativeDampedCompletionL2Integrand,
      nativeDampedCompletionKernel_zero_of_neg epsilon (lt_of_not_ge ht), zero_smul]
    exact nativeCompletionCausalL2.zero_mem

/-- Causality passes through the strong integral in the proved closed
causal space. This does not assert a pointwise Fubini formula. -/
theorem nativeDampedCompletionL2Operator_causal (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (f : nativeCompletionCausalL2) :
    nativeDampedCompletionL2Operator epsilon hepsilon (f : NativeCompletionL2) ∈
      nativeCompletionCausalL2 := by
  let lifted : ℝ → nativeCompletionCausalL2 := fun t =>
    ⟨nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) t,
      nativeDampedCompletionL2Integrand_causal epsilon f t⟩
  let total : nativeCompletionCausalL2 := ∫ t : ℝ, lifted t
  have hi := (nativeCompletionCausalL2.subtypeₗᵢ).integral_comp_comm (μ := volume) lifted
  change (∫ t : ℝ, nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) t) =
    (total : NativeCompletionL2) at hi
  change nativeDampedCompletionL2Value epsilon (f : NativeCompletionL2) ∈ nativeCompletionCausalL2
  unfold nativeDampedCompletionL2Value
  rw [hi]
  exact total.property

/-- Restrict both domain and range to the proved closed causal space. -/
def nativeDampedCompletionCausalL2Operator (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeCompletionCausalL2 →L[ℂ] nativeCompletionCausalL2 :=
  ContinuousLinearMap.codRestrict
    ((nativeDampedCompletionL2Operator epsilon hepsilon).domRestrict nativeCompletionCausalL2)
    nativeCompletionCausalL2
    (fun f => nativeDampedCompletionL2Operator_causal epsilon hepsilon f)

theorem nativeDampedCompletionCausalL2Operator_coe_apply (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (f : nativeCompletionCausalL2) :
    (nativeDampedCompletionCausalL2Operator epsilon hepsilon f : NativeCompletionL2) =
      nativeDampedCompletionL2Operator epsilon hepsilon (f : NativeCompletionL2) := rfl

theorem nativeDampedCompletionCausalL2Operator_norm_le_full (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    ‖nativeDampedCompletionCausalL2Operator epsilon hepsilon‖ ≤
      ‖nativeDampedCompletionL2Operator epsilon hepsilon‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖nativeDampedCompletionL2Operator epsilon hepsilon (f : NativeCompletionL2)‖ ≤
    ‖nativeDampedCompletionL2Operator epsilon hepsilon‖ * ‖(f : NativeCompletionL2)‖
  exact (nativeDampedCompletionL2Operator epsilon hepsilon).le_opNorm _

theorem nativeDampedCompletionCausalL2Operator_norm_lt_605_div_621 (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    ‖nativeDampedCompletionCausalL2Operator epsilon hepsilon‖ < (605 / 621 : ℝ) :=
  (nativeDampedCompletionCausalL2Operator_norm_le_full epsilon hepsilon).trans_lt
    (nativeDampedCompletionL2Operator_norm_lt_605_div_621 epsilon hepsilon)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCompletionL2Delay_continuous
#print axioms Zeta23.CCM.nativeDampedCompletionL2Integrand_integrable
#print axioms Zeta23.CCM.nativeDampedCompletionL2Operator_apply
#print axioms Zeta23.CCM.nativeDampedCompletionL2Operator_norm_lt_605_div_621
#print axioms Zeta23.CCM.nativeDampedCompletionL2Operator_norm_lt_one
#print axioms Zeta23.CCM.nativeCompletionCausalL2_isClosed
#print axioms Zeta23.CCM.nativeDampedCompletionL2Operator_causal
#print axioms Zeta23.CCM.nativeDampedCompletionCausalL2Operator_coe_apply
#print axioms Zeta23.CCM.nativeDampedCompletionCausalL2Operator_norm_lt_605_div_621
