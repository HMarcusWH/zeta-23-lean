import Zeta23.CCM.UniversalSincDetector
import Zeta23.ExceptionalZero.UniversalSincDetectorVisibility
import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.CCM.NativeIntegerPrimeSource
import Zeta23.CCM.NativePositiveCompletion
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
  let roots : Array (Name × String) := #[
    (``Zeta23.CCM.UniversalSinc.hasSum_width, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.summable_norm_sinc_sub_one, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.multipliable_sinc, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.CCM.UniversalSinc.product_ne_zero_of_im_ne_zero, "Zeta23.CCM.UniversalSincDetector"),
    (``Zeta23.ExceptionalZero.originalSincMultiplier_ne_zero_at_off_line_zero,
      "Zeta23.ExceptionalZero.UniversalSincDetectorVisibility"),
    (``Zeta23.CCM.canonicalPoleOddFunctional_evenIndex, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.poleNeutralIndexLinearMap_injective, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.poleNeutralIndexLinearMap_surjective, "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.canonicalSourceMatrix_mulVec_eq_negative_arch_prime_of_profiles,
      "Zeta23.CCM.CanonicalPoleNeutralGeometry"),
    (``Zeta23.CCM.native_primeCoefficients_unique, "Zeta23.CCM.NativeIntegerPrimeSource"),
    (``Zeta23.CCM.native_weighted_dirichlet_identity, "Zeta23.CCM.NativeIntegerPrimeSource"),
    (``Zeta23.CCM.nativePositiveCompletion_nonneg, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletion_le_exp, "Zeta23.CCM.NativePositiveCompletion"),
    (``Zeta23.CCM.nativePositiveCompletion_integrableOn, "Zeta23.CCM.NativePositiveCompletion")]
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
