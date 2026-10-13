import Zeta23.CCM.UniversalSincDetector
import Zeta23.ExceptionalZero.UniversalSincDetectorVisibility
import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.CCM.NativeIntegerPrimeSource
import Zeta23.CCM.NativeIntegerPrimeField
import Zeta23.CCM.NativePositiveCompletion
import Zeta23.CCM.Step123PrimeSeam
import Zeta23.RHRC.SourceCandidateResolution
import Lean.Util.CollectAxioms

open Lean Lean.Elab Command

/-!
Audit of the implemented components only. None of the missing output-producer
roots is replaced by a generic interface here. The complete M25 acceptance
remains open until the original mandatory producer declarations exist.
Uses the repository's existing compiler-backed source-candidate resolver.
-/

run_cmd do
  let some checkedHead ← liftIO <| IO.getEnv "POST290_CHECKED_HEAD"
    | throwError "Missing POST290_CHECKED_HEAD compiler context"
  let some checkedTree ← liftIO <| IO.getEnv "POST290_CHECKED_TREE"
    | throwError "Missing POST290_CHECKED_TREE compiler context"
  liftIO <| IO.println s!"POST290_COMPILER_CONTEXT\t{checkedHead}\t{checkedTree}"
  let roots : Array (Name × String) := #[
    (``Zeta23.CCM.UniversalSinc.hasSum_width, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.summable_norm_sinc_sub_one, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.multipliable_sinc, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.hasProdUniformlyOn_compact, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.analyticAt_product, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.fixed_coincident_factor_zeros, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.product_ne_zero_of_im_ne_zero, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.fixed_product_ne_zero_of_im_ne_zero, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_ne_zero_at_off_line_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.ExceptionalZero.fixed_originalSincMultiplier_square_ne_zero_at_off_line_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_eq_zero_iff_of_im_ne_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_deriv_ne_zero_at_elementary_pair,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.CCM.canonicalPoleOddFunctional_evenIndex, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.poleNeutralIndexLinearMap_injective, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.poleNeutralIndexLinearMap_surjective, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.canonicalSourceMatrix_mulVec_eq_negative_arch_prime_of_profiles,
      "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.inner_poleNeutralEvenCompressedCanonical_self, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.inner_poleNeutralOddCompressedCanonical_self, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.canonicalSourceMatrix_mulVec_poleNeutralEven_eq_negative_arch_prime,
      "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.native_primeCoefficients_unique, "Zeta23.CCM.NativeIntegerPrimeSource"),
    (``Zeta23.CCM.native_weighted_dirichlet_identity, "Zeta23.CCM.NativeIntegerPrimeSource"),
    (``Zeta23.CCM.nativePrimeField_eq_history_sum, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativeIntegerDriveField_eq_history_sum, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePrimeField_zero_before_firstPrime, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePrimeField_frozen_firstPrime_atom, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePrimeField_continuous, "Zeta23.CCM.NativeIntegerPrimeField"),
    (``Zeta23.CCM.nativePositiveCompletion_nonneg, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletion_le_exp, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletion_integrableOn, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.step123_enteringPrimeSourceMatrix_zero, "Zeta23.CCM.Step123PrimeSeam"),
    (``Zeta23.CCM.step123_qBasis_logSeam_zero, "Zeta23.CCM.Step123PrimeSeam")]
  let queries := roots.map fun (name, mod) =>
    ({ sourceId := name.toString, moduleName := mod, shortName := name.toString,
       sourceKind := "THEOREM" } : Zeta23.RHRC.SourceCandidateQuery)
  Zeta23.RHRC.resolveSourceCandidates queries
  for (name, _) in roots do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    let names := String.intercalate "," (axioms.toList.map Name.toString)
    liftIO <| IO.println s!"POST290_AXIOMS\t{name}\t{names}"
