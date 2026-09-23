import Zeta23.CCM.GlobalParityBottomResidualState
import Zeta23.CCM.GlobalParityBottomGroundTrial
import Zeta23.CCM.GlobalParityBottomEvenStrictNormalForm
import Zeta23.CCM.GlobalParityBottomOddStrictNormalForm
import Zeta23.CCM.GlobalParityBottomReverseGroundTransfer
import Zeta23.CCM.GlobalParityBottomTieNormalForm

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — typed branch package

The base residual state records provenance, the globally aligned shift and a
parity-safe branch. This module derives the stronger branch mathematics as a
separate dependent object. Any downstream arithmetic object that stores this
package is therefore forced to depend on the strict-even / strict-odd / tie
geometry rather than merely importing it decoratively.
-/

/-- Strong branch data derived from one globally aligned residual state. -/
inductive GlobalBottomBranchPackage {Q : ℕ}
    (s : GlobalBottomResidualState Q) : Type
  | evenStrict
      (hp : s.aligned.firstBad.p = .even)
      (hstrict :
        parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1) <
          parityRayleighBottom .odd s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))
      (hground :
        s.aligned.lam =
          parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))
      (hsame :
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) =
          (s.aligned.evenShiftedTrial : EuclideanSpace ℂ
            (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))))
      (horient :
        0 < s.aligned.retainedRealSourceScalar *
              s.aligned.retainedRealMomentFour ∧
        0 < s.aligned.retainedRealSourceScalar *
              s.aligned.retainedRealCrossParityGamma ∧
        0 < s.aligned.retainedRealSourceScalar *
              s.aligned.retainedRealCompletedSourceScalar ∧
        0 < s.aligned.retainedRealCrossParityGamma *
              s.aligned.retainedRealMomentFour ∧
        0 ≤ s.aligned.retainedOddResolventCorrection)
  | oddStrict
      (hp : s.aligned.firstBad.p = .odd)
      (hstrict :
        parityRayleighBottom .odd s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1) <
          parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))
      (hground :
        s.aligned.lam =
          parityRayleighBottom .odd s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))
      (hgamma :
        ∃ hneg : parityRayleighBottom .odd s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) < 0,
          crossParitySecularGamma s.aligned.firstBad.L_pos
              s.aligned.firstBad.Nstar
              (s.aligned.firstBad.predecessorNonnegative_anyParity .odd)
              (parityRayleighBottom .odd s.aligned.firstBad.L
                (s.aligned.firstBad.Nstar + 1)) hneg ≠ 0)
      (halpha :
        ∃ hneg : parityRayleighBottom .odd s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) < 0,
          let alpha :=
            crossParitySecularAlpha s.aligned.firstBad.L_pos
              s.aligned.firstBad.Nstar
              (s.aligned.firstBad.predecessorNonnegative_anyParity .odd)
              (parityRayleighBottom .odd s.aligned.firstBad.L
                (s.aligned.firstBad.Nstar + 1)) hneg
          let S :=
            evenQuadraticSourceMoment s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1)
              (cubicSecularTrialVector .even s.aligned.firstBad.L_pos
                s.aligned.firstBad.Nstar
                (s.aligned.firstBad.predecessorNonnegative_anyParity .even)
                (parityRayleighBottom .odd s.aligned.firstBad.L
                  (s.aligned.firstBad.Nstar + 1)) hneg)
          alpha = 0 ↔ S = 0)
      (hreverse :
        ∃ w : euclideanOddBoundaryFlatSubspace
              (s.aligned.firstBad.Nstar + 1),
          w ≠ 0 ∧
          parityCompressedCanonical .odd s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) w =
            (parityRayleighBottom .odd s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) : ℂ) • w ∧
          evenQuadraticSourceMoment s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1)
              ((euclideanEvenOddBoundaryFlatLinearEquiv
                (s.aligned.firstBad.Nstar + 1) (by omega)).symm w) ≠ 0)
  | tieEven
      (hp : s.aligned.firstBad.p = .even)
      (htie :
        parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1) =
          parityRayleighBottom .odd s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))
      (hground :
        s.aligned.lam =
          parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1))
      (hsame :
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) =
          (s.aligned.evenShiftedTrial : EuclideanSpace ℂ
            (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))))
      (hsaturation :
        ∃ hneg : parityRayleighBottom .even s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) < 0,
          let lam := parityRayleighBottom .even s.aligned.firstBad.L
            (s.aligned.firstBad.Nstar + 1)
          let alpha :=
            crossParitySecularAlpha s.aligned.firstBad.L_pos
              s.aligned.firstBad.Nstar
              (s.aligned.firstBad.predecessorNonnegative_anyParity .odd)
              lam hneg
          let Gamma :=
            crossParitySecularGamma s.aligned.firstBad.L_pos
              s.aligned.firstBad.Nstar
              (s.aligned.firstBad.predecessorNonnegative_anyParity .odd)
              lam hneg
          let u :=
            cubicSecularTrialVector .even s.aligned.firstBad.L_pos
              s.aligned.firstBad.Nstar
              (s.aligned.firstBad.predecessorNonnegative_anyParity .even)
              lam hneg
          let S :=
            evenQuadraticSourceMoment s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) u
          (Gamma = 0 ∧
              (2 * (s.aligned.firstBad.Nstar : ℂ) - 1) * alpha =
                2 * (s.aligned.firstBad.Nstar : ℂ) + 5) ∨
            (S = 0 ∧
              parityCompressedCanonical .odd s.aligned.firstBad.L
                  (s.aligned.firstBad.Nstar + 1)
                  (euclideanEvenToOddIndexLinearMap
                    (s.aligned.firstBad.Nstar + 1) u) =
                (lam : ℂ) •
                  euclideanEvenToOddIndexLinearMap
                    (s.aligned.firstBad.Nstar + 1) u))

/-- Every residual state has exactly the strengthened package associated to its
stored branch. -/
theorem GlobalBottomResidualState.exists_branchPackage
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    Nonempty (GlobalBottomBranchPackage s) := by
  cases hbranch : s.branch with
  | evenStrict hp hstrict =>
      have hground :
          s.aligned.lam =
            parityRayleighBottom .even s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) := by
        rw [s.aligned_lam_is_global, globalParitySuccessorBottom,
          min_eq_left (le_of_lt hstrict)]
      have hsame :=
        s.groundTrial_coe_eq_evenShiftedTrial_of_even hp
      have horient :=
        s.aligned.retainedEvenStrict_orientationPackage
          hp hground hstrict
      exact ⟨.evenStrict hp hstrict hground hsame horient⟩
  | oddStrict hp hstrict =>
      have hground :
          s.aligned.lam =
            parityRayleighBottom .odd s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) := by
        rw [s.aligned_lam_is_global, globalParitySuccessorBottom,
          min_eq_right (le_of_lt hstrict)]
      have hbad := s.aligned.firstBad.anyParityBad_succ
      obtain ⟨hnegG, hgamma⟩ :=
        globalBottom_oddStrict_gamma_ne_zero
          s.aligned.firstBad.L_pos s.aligned.firstBad.Nstar
          s.aligned.firstBad.one_le_Nstar
          s.aligned.firstBad.predecessorNonnegative_anyParity
          hbad hstrict
      obtain ⟨hnegA, halpha⟩ :=
        globalBottom_oddStrict_alpha_eq_zero_iff_source_eq_zero
          s.aligned.firstBad.L_pos s.aligned.firstBad.Nstar
          s.aligned.firstBad.one_le_Nstar
          s.aligned.firstBad.predecessorNonnegative_anyParity
          hbad hstrict
      obtain ⟨w, hwne, hweig⟩ :=
        exists_eigenmode_at_parityRayleighBottom_succ
          .odd s.aligned.firstBad.L s.aligned.firstBad.Nstar
          s.aligned.firstBad.one_le_Nstar
      have hsource :
          evenQuadraticSourceMoment s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1)
              ((euclideanEvenOddBoundaryFlatLinearEquiv
                (s.aligned.firstBad.Nstar + 1) (by omega)).symm w) ≠ 0 := by
        simpa using
          oddGround_pulledBack_source_ne_zero_of_strict
            s.aligned.firstBad.L_pos s.aligned.firstBad.Nstar
            s.aligned.firstBad.one_le_Nstar hstrict w hwne hweig
      exact ⟨.oddStrict hp hstrict hground
        ⟨hnegG, hgamma⟩ ⟨hnegA, halpha⟩
        ⟨w, hwne, hweig, hsource⟩⟩
  | tieEven hp htie =>
      have hground :
          s.aligned.lam =
            parityRayleighBottom .even s.aligned.firstBad.L
              (s.aligned.firstBad.Nstar + 1) := by
        rw [s.aligned_lam_is_global, globalParitySuccessorBottom,
          min_eq_left (le_of_eq htie)]
      have hsame :=
        s.groundTrial_coe_eq_evenShiftedTrial_of_even hp
      have hbad := s.aligned.firstBad.anyParityBad_succ
      obtain ⟨hneg, hsaturation⟩ :=
        globalBottom_tie_saturation
          s.aligned.firstBad.L_pos s.aligned.firstBad.Nstar
          s.aligned.firstBad.one_le_Nstar
          s.aligned.firstBad.predecessorNonnegative_anyParity
          hbad htie
      exact ⟨.tieEven hp htie hground hsame ⟨hneg, hsaturation⟩⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomBranchPackage
#print axioms Zeta23.CCM.GlobalBottomResidualState.exists_branchPackage
