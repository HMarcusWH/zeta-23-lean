import Zeta23.CCM.Step123OutputFieldEvidence
import Zeta23.CCM.NativeCompletionEquation
import Zeta23.CCM.NativeCompletionPublicAPI
import Zeta23.CCM.NativeDampedCompletionResidual
import Zeta23.CCM.NativeIntegerDriveFiniteOrderBounds
import Zeta23.ExceptionalZero.GeneratedStep123BoundaryPacket

/-!
# N29-N34 arithmetic/range source-connected output evidence

All proof fields are obtained from the frozen physical q/k/j prime
source and the actual native completion kernel; the packet has no
caller-supplied divisor, Laplace, causal range, compact inverse, or
residual-iteration hypothesis. The same source underlies both arithmetic
and range views, while actual rho-derived nonrange remains in G04.

These are proof-carrying native facts (and finite residual control),
not any of the OPEN universal A-X/B-Y/C-Schur closing laws.
-/

noncomputable section
open MeasureTheory
namespace Zeta23.CCM
open Zeta23.ExceptionalZero

/-- Verified arithmetic and L2-causal range geometry at the same
fixed native source, attached to the actual retained output. -/
structure Step123NativeArithmeticRangeEvidence
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) where
  original_prime_field_identity :
    out.arithmeticView.1 = nativeOriginalPrimeField
  original_integer_drive_identity :
    out.arithmeticView.2 = nativeOriginalIntegerDrive
  original_range_input_identity :
    out.rangeView.1 = nativeCompletedInput
  original_range_correction_identity :
    out.rangeView.2 = nativeCompletionCorrection
  integer_divisor_exact :
    ∀ t : ℝ, nativeIntegerTranslateAction nativeOriginalPrimeField t =
      nativeOriginalIntegerDrive t
  integer_drive_all_fixed_exponential_rates :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
        |nativeOriginalIntegerDrive t| ≤ C * Real.exp (-A * t)
  true_native_completion_equation :
    ∀ t : ℝ,
      (∫ s : ℝ, nativePositiveCompletion s *
        nativeOriginalPrimeField (t - s)) = nativeCompletedInput t
  completion_kernel_norm_strict :
    ∀ (ε : ℝ) (hε : 0 ≤ ε),
      ‖nativeDampedCompletionCausalL2Operator ε hε‖ < (605 / 621 : ℝ)
  native_adjoint_residual_norm_antitone :
    ∀ (ε : ℝ) (hε : 0 ≤ ε) (e : nativeCompletionCausalL2),
      Antitone (fun n => ‖nativeAdjointResidualIterate ε hε e n‖)
  native_adjoint_kernel_component_invariant :
    ∀ (ε : ℝ) (hε : 0 ≤ ε) (e : nativeCompletionCausalL2) (n : ℕ),
      nativeCompletionAdjointKernelProjection ε hε
          (nativeAdjointResidualIterate ε hε e n) =
        nativeCompletionAdjointKernelProjection ε hε e

/-- A compiler-checkable source-specific proof bundle. Each field is
filled from an EXACT native theorem, not by metadata strings. -/
def Step123NativeArithmeticRangeEvidence.fromNative
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    Step123NativeArithmeticRangeEvidence out where
  original_prime_field_identity := out.arithmeticView_eq_fixed.1
  original_integer_drive_identity := out.arithmeticView_eq_fixed.2
  original_range_input_identity := out.rangeView_eq_actual.1
  original_range_correction_identity := out.rangeView_eq_actual.2
  integer_divisor_exact := native_divisor_convolution_identity
  integer_drive_all_fixed_exponential_rates :=
    nativeOriginalIntegerDrive_rapid_bound
  true_native_completion_equation := nativeCompletedInput_equation
  completion_kernel_norm_strict :=
    nativeDampedCompletionCausalL2Operator_norm_lt_605_div_621
  native_adjoint_residual_norm_antitone :=
    nativeAdjointResidual_norm_antitone
  native_adjoint_kernel_component_invariant :=
    nativeAdjointResidual_kernelProjection_preserved

/-- Reuse the cofinal zero-generated detector and the SAME boundary
packet; never select a second ground just to construct arithmetic/range
fields. -/
structure GeneratedStep123IntegratedPacket
    (ρ : zetaZeroConfig.carrier) (β : ℝ)
    (σ : ReversalParity) (R : ℝ) where
  boundary : GeneratedStep123BoundaryPacket ρ β σ R
  arithmetic : Step123NativeArithmeticRangeEvidence boundary.generated.native

def GeneratedStep123IntegratedPacket.fromActualBoundary
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (boundary : GeneratedStep123BoundaryPacket ρ β σ R) :
    GeneratedStep123IntegratedPacket ρ β σ R where
  boundary := boundary
  arithmetic := Step123NativeArithmeticRangeEvidence.fromNative
    boundary.generated.native

theorem exists_generatedStep123IntegratedPacket
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    Nonempty (GeneratedStep123IntegratedPacket ρ β σ R) := by
  obtain ⟨boundary⟩ :=
    exists_generatedStep123BoundaryPacket ρ hβ hβρ σ R
  exact ⟨GeneratedStep123IntegratedPacket.fromActualBoundary boundary⟩

theorem exists_generatedStep123IntegratedPacket_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123IntegratedPacket ρ β σ R,
      max R 4 < fixedOriginalSincTrialAperture
        out.boundary.generated.sourceData.separation := by
  obtain ⟨boundary, hL⟩ :=
    exists_generatedStep123BoundaryPacket_cofinal ρ hβ hβρ σ R
  exact ⟨GeneratedStep123IntegratedPacket.fromActualBoundary boundary, hL⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeArithmeticRangeEvidence.fromNative
#print axioms Zeta23.CCM.GeneratedStep123IntegratedPacket.fromActualBoundary
#print axioms Zeta23.CCM.exists_generatedStep123IntegratedPacket
#print axioms Zeta23.CCM.exists_generatedStep123IntegratedPacket_cofinal
