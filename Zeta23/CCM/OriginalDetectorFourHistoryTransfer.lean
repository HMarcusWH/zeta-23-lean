import Zeta23.CCM.OriginalDetectorPrimeHistoryCovariance
import Zeta23.CCM.OriginalDetectorFourHistoryLocalDuality

/-!
# Four original-prime histories transferred to the native X field

For the ACTUAL fixed original kernel F_k and its native P-image X,
the compact neutral L2 inverse's continuous representative gives an
exact local pairing with X after every original translation/reflection.
This transfers four separate histories on a finite interval. Neither
the source nor X is assumed globally L2, no cancelling histories are
discarded, and no RH closing assumption is introduced.

The aggregate four-history signed bound, normalized predecessor
projection and quantitative 16*kappa local-X estimate remain separate
obligations; this file does not claim those estimates.
-/

noncomputable section
open MeasureTheory Set
namespace Zeta23.CCM

/-- General local compact-inverse P transfer. X here must be the ACTUAL
pointwise P-image of the specified smooth observation F. The pairing
identity is derived; it is not an extra input hypothesis. -/
theorem NativeCompactPoleH2.localP_transfer_of_continuous
    {s : ℝ} {f F X : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f)
    (hf : Continuous f) (hF : ContDiff ℝ 2 F)
    (hPX : ∀ x : ℝ, universalSincDifferential F x = X x) :
    (∫ x in (-s)..s, f x * F x) =
      ∫ x in (-s)..s, u.value x * X x := by
  calc
    (∫ x in (-s)..s, f x * F x) =
        ∫ x in (-s)..s, u.value x * universalSincDifferential F x := by
      simpa only [universalSincDifferential] using
        u.localP_duality_of_continuous hf hF
    _ = ∫ x in (-s)..s, u.value x * X x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact congrArg (fun z : ℂ => u.value x * z) (hPX x)

/-- Source-specific native four-history transfer, with the original
reflected signs in the ARGUMENTS, not yet summed. All four X values
come from the genuine von Mangoldt field, not a supplied surrogate. -/
theorem NativeCompactPoleH2.originalFourHistories_to_actualX
    {s : ℝ} {f : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f) (hf : Continuous f) (a : ℝ) :
    let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
    let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
    let F := nativeOriginalKernelPrimeField
    let X := fun t : ℝ => (nativeOriginalPrimeField t : ℂ)
    (∫ x in (-s)..s, f x * F (x - c)) =
      ∫ x in (-s)..s, u.value x * X (x - c) ∧
    (∫ x in (-s)..s, f x * F (c - x)) =
      ∫ x in (-s)..s, u.value x * X (c - x) ∧
    (∫ x in (-s)..s, f x * F (L - x - c)) =
      ∫ x in (-s)..s, u.value x * X (L - x - c) ∧
    (∫ x in (-s)..s, f x * F (x + c - L)) =
      ∫ x in (-s)..s, u.value x * X (x + c - L) := by
  dsimp only
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
  let F := nativeOriginalKernelPrimeField
  have hF : ContDiff ℝ 2 F :=
    nativeOriginalKernelPrimeField_contDiff.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h1 : ContDiff ℝ 2 (fun t : ℝ => F (t - c)) :=
    hF.comp (by fun_prop)
  have h2 : ContDiff ℝ 2 (fun t : ℝ => F (c - t)) :=
    hF.comp (by fun_prop)
  have h3 : ContDiff ℝ 2 (fun t : ℝ => F (L - t - c)) :=
    hF.comp (by fun_prop)
  have h4 : ContDiff ℝ 2 (fun t : ℝ => F (t + c - L)) :=
    hF.comp (by fun_prop)
  refine ⟨u.localP_transfer_of_continuous hf h1 ?_,
          u.localP_transfer_of_continuous hf h2 ?_,
          u.localP_transfer_of_continuous hf h3 ?_,
          u.localP_transfer_of_continuous hf h4 ?_⟩
  · intro x
    exact (originalDetector_fourPrimeHistory_poleImages a x).1
  · intro x
    exact (originalDetector_fourPrimeHistory_poleImages a x).2.1
  · intro x
    exact (originalDetector_fourPrimeHistory_poleImages a x).2.2.1
  · intro x
    exact (originalDetector_fourPrimeHistory_poleImages a x).2.2.2

end Zeta23.CCM

#print axioms Zeta23.CCM.NativeCompactPoleH2.localP_transfer_of_continuous
#print axioms Zeta23.CCM.NativeCompactPoleH2.originalFourHistories_to_actualX
