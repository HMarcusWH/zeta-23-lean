import Zeta23.CCM.NativeDampedCompletionOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Finite residual descent for the actual causal completion

The adjoint here is the Hilbert adjoint of the actual bounded operator on
the proved closed causal L2 space. It is not the full-line adjoint.
Finite residual iteration preserves the projection onto its adjoint
kernel and decreases the norm by an explicit amount. None of these facts
asserts that this invariant projection vanishes, that the residual tends
to zero, or that an independently defined forcing belongs to the range.
-/

noncomputable section

open scoped InnerProduct

namespace Zeta23.CCM

def nativeDampedCompletionCausalL2Adjoint (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeCompletionCausalL2 →L[ℂ] nativeCompletionCausalL2 :=
  (nativeDampedCompletionCausalL2Operator epsilon hepsilon).adjoint

theorem nativeDampedCompletionCausalL2Adjoint_norm_lt_605_div_621
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon‖ < (605 / 621 : ℝ) := by
  unfold nativeDampedCompletionCausalL2Adjoint
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact nativeDampedCompletionCausalL2Operator_norm_lt_605_div_621 epsilon hepsilon

def nativeAdjointResidualStep (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) : nativeCompletionCausalL2 :=
  e - nativeDampedCompletionCausalL2Operator epsilon hepsilon
    (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e)

def nativeAdjointResidualIterate (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) : ℕ → nativeCompletionCausalL2
  | 0 => e
  | n + 1 => nativeAdjointResidualStep epsilon hepsilon
      (nativeAdjointResidualIterate epsilon hepsilon e n)

theorem nativeAdjointResidualIterate_zero (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) : nativeAdjointResidualIterate epsilon hepsilon e 0 = e := rfl

theorem nativeAdjointResidualIterate_succ (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) (n : ℕ) :
    nativeAdjointResidualIterate epsilon hepsilon e (n + 1) =
      nativeAdjointResidualIterate epsilon hepsilon e n -
        nativeDampedCompletionCausalL2Operator epsilon hepsilon
          (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon
            (nativeAdjointResidualIterate epsilon hepsilon e n)) := rfl

theorem nativeAdjointResidual_norm_identity (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) :
    ‖nativeAdjointResidualStep epsilon hepsilon e‖ ^ 2 = ‖e‖ ^ 2 -
      2 * ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e‖ ^ 2 +
        ‖nativeDampedCompletionCausalL2Operator epsilon hepsilon
          (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e)‖ ^ 2 := by
  rw [nativeAdjointResidualStep, norm_sub_sq (𝕜 := ℂ)]
  have hi := (nativeDampedCompletionCausalL2Operator epsilon hepsilon).adjoint_inner_left
    (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e) e
  change inner ℂ (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e)
      (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e) =
    inner ℂ e (nativeDampedCompletionCausalL2Operator epsilon hepsilon
      (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e)) at hi
  rw [← hi, inner_self_eq_norm_sq]

/-- The norm decrease is source-independent operator algebra, instantiated
at the actual native causal operator and its proved mass bound. -/
theorem nativeAdjointResidual_norm_loss (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) :
    ‖nativeAdjointResidualStep epsilon hepsilon e‖ ^ 2 ≤ ‖e‖ ^ 2 -
      (2 - (605 / 621 : ℝ) ^ 2) *
        ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e‖ ^ 2 := by
  have hbound := (nativeDampedCompletionCausalL2Operator epsilon hepsilon).le_opNorm
    (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e)
  have hmass := (nativeDampedCompletionCausalL2Operator_norm_lt_605_div_621
    epsilon hepsilon).le
  have hnorm : ‖nativeDampedCompletionCausalL2Operator epsilon hepsilon
      (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e)‖ ≤
        (605 / 621 : ℝ) * ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e‖ :=
    hbound.trans (mul_le_mul_of_nonneg_right hmass (norm_nonneg _))
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mpr hnorm
  rw [mul_pow] at hsq
  rw [nativeAdjointResidual_norm_identity]
  nlinarith

theorem nativeAdjointResidualStep_norm_le (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) :
    ‖nativeAdjointResidualStep epsilon hepsilon e‖ ≤ ‖e‖ := by
  have h := nativeAdjointResidual_norm_loss epsilon hepsilon e
  have hs := sq_nonneg ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e‖
  nlinarith [norm_nonneg e, norm_nonneg (nativeAdjointResidualStep epsilon hepsilon e)]

theorem nativeAdjointResidualStep_norm_lt (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2)
    (he : nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e ≠ 0) :
    ‖nativeAdjointResidualStep epsilon hepsilon e‖ < ‖e‖ := by
  have h := nativeAdjointResidual_norm_loss epsilon hepsilon e
  have hs : 0 < ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr he) 2
  nlinarith [norm_nonneg e, norm_nonneg (nativeAdjointResidualStep epsilon hepsilon e)]

theorem nativeAdjointResidual_norm_antitone (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) :
    Antitone (fun n => ‖nativeAdjointResidualIterate epsilon hepsilon e n‖) := by
  apply antitone_nat_of_succ_le
  intro n
  exact nativeAdjointResidualStep_norm_le epsilon hepsilon _

/-- This separate ratio measures the residual's current adjoint coupling.
It is neither a geometric phase-depth exponent nor a spectral attenuation. -/
def nativeAdjointResidualKappa (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) : ℝ :=
  ‖nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e‖ ^ 2 / ‖e‖ ^ 2

theorem nativeAdjointResidualKappa_nonneg (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) : 0 ≤ nativeAdjointResidualKappa epsilon hepsilon e :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem nativeAdjointResidualKappa_le (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) :
    nativeAdjointResidualKappa epsilon hepsilon e ≤ (605 / 621 : ℝ) ^ 2 := by
  by_cases he : e = 0
  · simp [nativeAdjointResidualKappa, he]
    positivity
  have hden : 0 < ‖e‖ ^ 2 := pow_pos (norm_pos_iff.mpr he) 2
  rw [nativeAdjointResidualKappa, div_le_iff₀ hden]
  have hnorm := (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon).le_opNorm e
  have hmass := (nativeDampedCompletionCausalL2Adjoint_norm_lt_605_div_621
    epsilon hepsilon).le
  have hb := hnorm.trans (mul_le_mul_of_nonneg_right hmass (norm_nonneg e))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg e))).mpr hb
  simpa only [mul_pow] using hs

theorem nativeAdjointResidual_norm_loss_kappa (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) :
    ‖nativeAdjointResidualStep epsilon hepsilon e‖ ^ 2 ≤
      (1 - (2 - (605 / 621 : ℝ) ^ 2) * nativeAdjointResidualKappa epsilon hepsilon e) *
        ‖e‖ ^ 2 := by
  by_cases he : e = 0
  · simp [nativeAdjointResidualStep, he]
  have hden : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have hr := nativeAdjointResidual_norm_loss epsilon hepsilon e
  unfold nativeAdjointResidualKappa
  field_simp
  nlinarith

def nativeCompletionAdjointKernel (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    Submodule ℂ nativeCompletionCausalL2 :=
  (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon).ker

instance nativeCompletionAdjointKernel_completeSpace (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    CompleteSpace (nativeCompletionAdjointKernel epsilon hepsilon) :=
  (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon).isClosed_ker.completeSpace_coe

def nativeCompletionAdjointKernelProjection (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeCompletionCausalL2 →L[ℂ] nativeCompletionAdjointKernel epsilon hepsilon :=
  (nativeCompletionAdjointKernel epsilon hepsilon).orthogonalProjectionOnto

theorem nativeAdjointResidualStep_kernelProjection_preserved
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (e : nativeCompletionCausalL2) :
    nativeCompletionAdjointKernelProjection epsilon hepsilon
        (nativeAdjointResidualStep epsilon hepsilon e) =
      nativeCompletionAdjointKernelProjection epsilon hepsilon e := by
  have hz : nativeDampedCompletionCausalL2Operator epsilon hepsilon
      (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon e) ∈
        (nativeCompletionAdjointKernel epsilon hepsilon)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro z hz
    change nativeDampedCompletionCausalL2Adjoint epsilon hepsilon z = 0 at hz
    rw [← (nativeDampedCompletionCausalL2Operator epsilon hepsilon).adjoint_inner_left]
    change inner ℂ (nativeDampedCompletionCausalL2Adjoint epsilon hepsilon z) _ = 0
    rw [hz, inner_zero_left]
  unfold nativeAdjointResidualStep nativeCompletionAdjointKernelProjection
  rw [map_sub, (nativeCompletionAdjointKernel epsilon hepsilon).orthogonalProjectionOnto_eq_zero_iff.mpr hz,
    sub_zero]

theorem nativeAdjointResidual_kernelProjection_preserved
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (e : nativeCompletionCausalL2) (n : ℕ) :
    nativeCompletionAdjointKernelProjection epsilon hepsilon
        (nativeAdjointResidualIterate epsilon hepsilon e n) =
      nativeCompletionAdjointKernelProjection epsilon hepsilon e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [nativeAdjointResidualIterate, nativeAdjointResidualStep_kernelProjection_preserved, ih]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDampedCompletionCausalL2Adjoint_norm_lt_605_div_621
#print axioms Zeta23.CCM.nativeAdjointResidual_norm_identity
#print axioms Zeta23.CCM.nativeAdjointResidual_norm_loss
#print axioms Zeta23.CCM.nativeAdjointResidual_norm_antitone
#print axioms Zeta23.CCM.nativeAdjointResidual_norm_loss_kappa
#print axioms Zeta23.CCM.nativeAdjointResidual_kernelProjection_preserved
