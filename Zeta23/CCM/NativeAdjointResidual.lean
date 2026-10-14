import Zeta23.CCM.NativeDampedCompletionResidual
import Zeta23.CCM.NativeCompletedInput

/-!
# Actual Y-initialized native adjoint residuals

The independent c * U stability theorem supplies the actual causal Yepsilon
as initial residual. Finite iterates satisfy the literal normal-update
identity and preserve its actual adjoint-kernel projection. No theorem
here makes this projection zero or concludes that Yepsilon lies in the
closure of the range. Those are the separate B-Y closing law.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.CCM

def nativeCompletedInputCausalL2 (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeCompletionCausalL2 :=
  ⟨nativeDampedCompletedInputL2 epsilon hepsilon,
    nativeDampedCompletedInputL2_causal epsilon hepsilon⟩

theorem nativeCompletedInputCausalL2_coeFn (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (nativeCompletedInputCausalL2 epsilon hepsilon : NativeCompletionL2) =ᵐ[volume]
      nativeDampedCompletedInput epsilon :=
  nativeDampedCompletedInputL2_coeFn epsilon hepsilon

def nativeAdjointApproximationIterate (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (e : nativeCompletionCausalL2) : ℕ → nativeCompletionCausalL2
  | 0 => 0
  | n + 1 => nativeAdjointApproximationIterate epsilon hepsilon e n +
      nativeDampedCompletionCausalL2Adjoint epsilon hepsilon
        (nativeAdjointResidualIterate epsilon hepsilon e n)

/-- Every finite residual is the actual forcing minus the actual operator
applied to its finite normal-update approximation. -/
theorem nativeAdjointResidualIterate_eq_forcing_sub_image
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (e : nativeCompletionCausalL2) (n : ℕ) :
    nativeAdjointResidualIterate epsilon hepsilon e n = e -
      nativeDampedCompletionCausalL2Operator epsilon hepsilon
        (nativeAdjointApproximationIterate epsilon hepsilon e n) := by
  induction n with
  | zero => simp [nativeAdjointResidualIterate, nativeAdjointApproximationIterate]
  | succ n ih =>
      rw [nativeAdjointResidualIterate_succ, nativeAdjointApproximationIterate, map_add, ih]
      abel

def nativeCompletedInputResidualIterate (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (n : ℕ) : nativeCompletionCausalL2 :=
  nativeAdjointResidualIterate epsilon hepsilon (nativeCompletedInputCausalL2 epsilon hepsilon) n

def nativeCompletedInputApproximationIterate (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (n : ℕ) : nativeCompletionCausalL2 :=
  nativeAdjointApproximationIterate epsilon hepsilon (nativeCompletedInputCausalL2 epsilon hepsilon) n

theorem nativeCompletedInputResidualIterate_zero (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeCompletedInputResidualIterate epsilon hepsilon 0 =
      nativeCompletedInputCausalL2 epsilon hepsilon := rfl

theorem nativeCompletedInputResidualIterate_eq_forcing_sub_image
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    nativeCompletedInputResidualIterate epsilon hepsilon n =
      nativeCompletedInputCausalL2 epsilon hepsilon -
        nativeDampedCompletionCausalL2Operator epsilon hepsilon
          (nativeCompletedInputApproximationIterate epsilon hepsilon n) :=
  nativeAdjointResidualIterate_eq_forcing_sub_image epsilon hepsilon _ n

theorem nativeCompletedInputResidual_norm_antitone (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    Antitone (fun n => ‖nativeCompletedInputResidualIterate epsilon hepsilon n‖) :=
  nativeAdjointResidual_norm_antitone epsilon hepsilon _

theorem nativeCompletedInputResidual_kernelProjection_preserved
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    nativeCompletionAdjointKernelProjection epsilon hepsilon
        (nativeCompletedInputResidualIterate epsilon hepsilon n) =
      nativeCompletionAdjointKernelProjection epsilon hepsilon
        (nativeCompletedInputCausalL2 epsilon hepsilon) :=
  nativeAdjointResidual_kernelProjection_preserved epsilon hepsilon _ n

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCompletedInputCausalL2_coeFn
#print axioms Zeta23.CCM.nativeAdjointResidualIterate_eq_forcing_sub_image
#print axioms Zeta23.CCM.nativeCompletedInputResidual_norm_antitone
#print axioms Zeta23.CCM.nativeCompletedInputResidual_kernelProjection_preserved
