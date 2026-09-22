import Zeta23.CCM.RegularFirstBadSourceKernelRealPhase
import Zeta23.CCM.RegularFirstBadCrossParitySecularCompletion
import Zeta23.CCM.RegularFirstBadCrossParityGramDisk
import Zeta23.CCM.RealBudgetDisk

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Retained completed-source real geometry

PR #236 fixes the phase of the selected-even retained negative-root trial and
therefore makes the exact retained source scalar real.  The same conjugation
infrastructure also makes the retained fourth centered moment real.

This module composes those reality statements with the already-proved
cross-parity completed-source budget and sharp Gram disk.  On the
selected-even / odd-good branch the formerly complex geometry is reduced to the
real scalar corridor

  B > 0,
  q > 0,
  c >= 0,
  B <= s*f,
  (q-f)^2 <= Rsharp,

where
  s = retained source scalar,
  m = retained fourth moment,
  c = real odd resolvent correction,
  f = m - s*c,
  B = (-lambda)||u_-||^2,
  q = ||shell||^2.

No proof of Rsharp <= q^2, no selected-even branch exclusion, no parity-complete
closure, and no RH theorem is asserted.
-/

/-- Real fourth-moment coordinate of the retained selected-even trial. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedRealMomentFour
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  Complex.re
    (centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial))

/-- Real odd resolvent correction already known to be conjugation-fixed. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedOddResolventCorrection
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  Complex.re
    (oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg)

/-- Real completed-source scalar f = m - s*c. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  c.retainedRealMomentFour -
    c.retainedRealSourceScalar * c.retainedOddResolventCorrection

/-- Strict negative-shift budget carried by the odd canonical trial. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedOddShiftBudget
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  (-c.lam) *
    ‖cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg‖ ^ 2

/-- Positive cubic-shell self center q = ||shell||^2. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedOddShellCenter
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  ‖(intrinsicCubicShellPart .odd c.firstBad.Nstar :
      euclideanParityBoundaryFlatSubspace .odd
        (c.firstBad.Nstar + 1))‖ ^ 2

/-- The retained fourth moment is conjugation-fixed on the selected-even branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.star_evenShiftedMomentFour_eq_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    star
        (centeredMoment (c.firstBad.Nstar + 1) 4
          (evenBoundaryFlatRawCoefficients
            (c.firstBad.Nstar + 1) c.evenShiftedTrial)) =
      centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial) := by
  let K := c.firstBad.Nstar + 1
  let v := c.evenShiftedTrial
  let u := evenBoundaryFlatRawCoefficients K v
  have hv := c.evenShiftedTrial_conj_fixed_of_even hp
  have hval := congrArg Subtype.val hv
  have hconj :
      euclideanConj
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) =
        (v : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
    simpa [K, v, parityConj] using hval
  have hcoords :=
    congrArg
      (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) =>
        (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)
      hconj
  rw [euclideanConj_coordinates] at hcoords
  have hu : star u = u := by
    simpa [u, evenBoundaryFlatRawCoefficients] using hcoords
  have hm := centeredMoment_star_coefficients K 4 u
  rw [hu] at hm
  simpa [K, v, u] using hm.symm

/-- Human-facing imaginary-part form of retained M4 reality. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedMomentFour_im_eq_zero_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    Complex.im
        (centeredMoment (c.firstBad.Nstar + 1) 4
          (evenBoundaryFlatRawCoefficients
            (c.firstBad.Nstar + 1) c.evenShiftedTrial)) = 0 := by
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  have hstar : star M4 = M4 := by
    simpa [M4] using c.star_evenShiftedMomentFour_eq_of_even hp
  have him := congrArg Complex.im hstar
  have him' : -M4.im = M4.im := by
    simpa using him
  have hzero : M4.im = 0 := by
    linarith
  simpa [M4] using hzero

/-- The retained complex fourth moment is exactly the coercion of its real
coordinate. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedMomentFour_eq_realScalar_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial) =
      (c.retainedRealMomentFour : ℂ) := by
  apply Complex.ext
  · simp [RegularCellMinimalNegativeEnergyCertificate.retainedRealMomentFour]
  · simpa using c.evenShiftedMomentFour_im_eq_zero_of_even hp

/-- The retained explicit production source moment is exactly its one real
source scalar from PR #236. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMoment_eq_realScalar_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial =
      (c.retainedRealSourceScalar : ℂ) := by
  rw [c.evenShiftedExplicitCanonicalSourceMoment_eq_sourceKernelRHS]
  apply Complex.ext
  · simp [RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceScalar]
  · simpa using c.evenShiftedSourceKernel_im_eq_zero_of_even hp

/-- The odd resolvent quadratic value is exactly the coercion of its retained
real correction coordinate. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddResolventQuadratic_eq_realCorrection
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg =
      (c.retainedOddResolventCorrection : ℂ) := by
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  have hstar : star C = C := by
    simpa [C] using
      star_oddCubicGeneratorResolventQuadratic_eq
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
  have him := congrArg Complex.im hstar
  have him' : -C.im = C.im := by
    simpa using him
  have hzero : C.im = 0 := by
    linarith
  apply Complex.ext
  · simp [C,
      RegularCellMinimalNegativeEnergyCertificate.retainedOddResolventCorrection]
  · simpa [C] using hzero

/-- The exact completed source M4 - S*C is a real scalar after PR #236. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCompletedSource_eq_realScalar_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    centeredMoment (c.firstBad.Nstar + 1) 4
          (evenBoundaryFlatRawCoefficients
            (c.firstBad.Nstar + 1) c.evenShiftedTrial) -
        explicitCanonicalSourceMoment
            c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial *
          oddCubicGeneratorResolventQuadratic
            c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .odd)
            c.lam c.lam_neg =
      (c.retainedRealCompletedSourceScalar : ℂ) := by
  rw [c.evenShiftedMomentFour_eq_realScalar_of_even hp,
    c.evenShiftedSourceMoment_eq_realScalar_of_even hp,
    c.oddResolventQuadratic_eq_realCorrection]
  apply Complex.ext <;>
    simp [RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar]

/-- The odd negative-shift budget is strictly positive. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedOddShiftBudget_pos
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    0 < c.retainedOddShiftBudget := by
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  have hne : uMinus ≠ 0 := by
    simpa [uMinus] using
      cubicSecularTrialVector_ne_zero
        .odd c.firstBad.L_pos c.firstBad.Nstar
        c.firstBad.one_le_Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
  have hnorm : 0 < ‖uMinus‖ := norm_pos_iff.mpr hne
  have hlam : 0 < -c.lam := neg_pos.mpr c.lam_neg
  have hsq : 0 < ‖uMinus‖ ^ 2 := sq_pos_of_pos hnorm
  simpa [RegularCellMinimalNegativeEnergyCertificate.retainedOddShiftBudget,
    uMinus] using mul_pos hlam hsq

/-- The cubic shell self center is strictly positive. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedOddShellCenter_pos
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    0 < c.retainedOddShellCenter := by
  have hshell :
      intrinsicCubicShellPart .odd c.firstBad.Nstar ≠ 0 :=
    intrinsicCubicShellPart_ne_zero
      .odd c.firstBad.Nstar c.firstBad.one_le_Nstar
  have hshell' :
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1)) ≠ 0 := by
    intro hzero
    apply hshell
    apply Subtype.ext
    simpa using hzero
  have hnorm :
      0 <
        ‖(intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))‖ := by
    exact norm_pos_iff.mpr hshell'
  simpa [RegularCellMinimalNegativeEnergyCertificate.retainedOddShellCenter]
    using sq_pos_of_pos hnorm

/-- The real odd resolvent correction is nonnegative. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedOddResolventCorrection_nonneg
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    0 ≤ c.retainedOddResolventCorrection := by
  simpa [RegularCellMinimalNegativeEnergyCertificate.retainedOddResolventCorrection]
    using
      oddCubicGeneratorResolventQuadratic_re_nonnegative
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg

/-- Scalarized completed-source budget: B <= s*f. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedCompletedSourceBudget_real_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedOddShiftBudget ≤
      c.retainedRealSourceScalar * c.retainedRealCompletedSourceScalar := by
  have h :=
    c.evenShiftedCrossParitySecularBudget_of_even_of_not_oddBad hp hodd
  dsimp only at h
  rw [c.evenShiftedCompletedSource_eq_realScalar_of_even hp,
    c.evenShiftedSourceMoment_eq_realScalar_of_even hp] at h
  simpa [RegularCellMinimalNegativeEnergyCertificate.retainedOddShiftBudget]
    using h

/-- Scalarized sharp Gram disk: (q-f)^2 <= Rsharp. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedCompletedSourceSharpDisk_real_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    (c.retainedOddShellCenter - c.retainedRealCompletedSourceScalar) ^ 2 ≤
      c.retainedSourceKernelSharpRadiusSq := by
  have h :=
    c.evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad hp hodd
  dsimp only at h
  let shell :=
    (intrinsicCubicShellPart .odd c.firstBad.Nstar :
      euclideanParityBoundaryFlatSubspace .odd
        (c.firstBad.Nstar + 1))
  have hq :
      inner ℂ shell shell = (c.retainedOddShellCenter : ℂ) := by
    simpa [shell,
      RegularCellMinimalNegativeEnergyCertificate.retainedOddShellCenter]
      using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) shell)
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  change
    ‖inner ℂ shell shell - M4 + S * C‖ ^ 2 ≤
      c.retainedSourceKernelSharpRadiusSq at h
  have hcenter :
      inner ℂ shell shell - M4 + S * C =
        inner ℂ shell shell - (M4 - S * C) := by
    ring
  have hF : M4 - S * C = (c.retainedRealCompletedSourceScalar : ℂ) := by
    simpa [M4, S, C] using
      c.evenShiftedCompletedSource_eq_realScalar_of_even hp
  rw [hcenter, hq, hF] at h
  have hnorm :
      ‖(c.retainedOddShellCenter : ℂ) -
          (c.retainedRealCompletedSourceScalar : ℂ)‖ =
        |c.retainedOddShellCenter - c.retainedRealCompletedSourceScalar| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, sq_abs] at h
  exact h

/-- Quantitative real coercivity of the source/M4 pairing. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceMoment_coercive_real_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedOddShiftBudget +
        c.retainedRealSourceScalar ^ 2 *
          c.retainedOddResolventCorrection ≤
      c.retainedRealSourceScalar * c.retainedRealMomentFour := by
  have hbudget :=
    c.retainedCompletedSourceBudget_real_of_even_of_not_oddBad hp hodd
  calc
    c.retainedOddShiftBudget +
          c.retainedRealSourceScalar ^ 2 *
            c.retainedOddResolventCorrection ≤
        c.retainedRealSourceScalar * c.retainedRealCompletedSourceScalar +
          c.retainedRealSourceScalar ^ 2 *
            c.retainedOddResolventCorrection := by
      exact add_le_add hbudget (le_refl _)
    _ = c.retainedRealSourceScalar * c.retainedRealMomentFour := by
      simp [RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar]
      ring

/-- The real source and real M4 have the same strict orientation on the
selected-even / odd-good branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSource_mul_momentFour_pos_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 < c.retainedRealSourceScalar * c.retainedRealMomentFour := by
  have hcoerc :=
    c.retainedSourceMoment_coercive_real_of_even_of_not_oddBad hp hodd
  have hB := c.retainedOddShiftBudget_pos
  have hc := c.retainedOddResolventCorrection_nonneg
  have hcorr :
      0 ≤ c.retainedRealSourceScalar ^ 2 *
        c.retainedOddResolventCorrection :=
    mul_nonneg (sq_nonneg _) hc
  linarith

/-- The #235 center deficit is bounded by the oriented displacement from the
completed-source scalar to the positive shell center. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelCenterDeficit_le_source_mul_completedOffset
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedSourceKernelCenterDeficit ≤
      c.retainedRealSourceScalar *
        (c.retainedRealCompletedSourceScalar - c.retainedOddShellCenter) := by
  have hbudget :=
    c.retainedCompletedSourceBudget_real_of_even_of_not_oddBad hp hodd
  unfold RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelCenterDeficit
  change
    c.retainedOddShiftBudget -
        c.retainedOddShellCenter * c.retainedRealSourceScalar ≤
      c.retainedRealSourceScalar *
        (c.retainedRealCompletedSourceScalar - c.retainedOddShellCenter)
  nlinarith

/-- Full same-state real corridor exposed by the selected-even / odd-good
branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceCorridor_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 < c.retainedOddShiftBudget ∧
    0 < c.retainedOddShellCenter ∧
    0 ≤ c.retainedOddResolventCorrection ∧
    c.retainedOddShiftBudget ≤
      c.retainedRealSourceScalar * c.retainedRealCompletedSourceScalar ∧
    (c.retainedOddShellCenter - c.retainedRealCompletedSourceScalar) ^ 2 ≤
      c.retainedSourceKernelSharpRadiusSq ∧
    c.retainedOddShiftBudget +
        c.retainedRealSourceScalar ^ 2 *
          c.retainedOddResolventCorrection ≤
      c.retainedRealSourceScalar * c.retainedRealMomentFour ∧
    c.retainedSourceKernelCenterDeficit ≤
      c.retainedRealSourceScalar *
        (c.retainedRealCompletedSourceScalar - c.retainedOddShellCenter) := by
  exact ⟨
    c.retainedOddShiftBudget_pos,
    c.retainedOddShellCenter_pos,
    c.retainedOddResolventCorrection_nonneg,
    c.retainedCompletedSourceBudget_real_of_even_of_not_oddBad hp hodd,
    c.retainedCompletedSourceSharpDisk_real_of_even_of_not_oddBad hp hodd,
    c.retainedSourceMoment_coercive_real_of_even_of_not_oddBad hp hodd,
    c.retainedSourceKernelCenterDeficit_le_source_mul_completedOffset hp hodd
  ⟩

/-- Conditional sign interface for the next arithmetic obstruction.

This theorem does not prove the sharp-radius/shell barrier.  It states exactly
what follows if independent arithmetic establishes Rsharp <= q^2. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceScalar_pos_of_sharpRadius_le_shellCenter_sq
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hbarrier :
      c.retainedSourceKernelSharpRadiusSq ≤
        c.retainedOddShellCenter ^ 2) :
    0 < c.retainedRealSourceScalar := by
  exact
    realBudgetDisk_source_pos
      c.retainedOddShiftBudget_pos
      (c.retainedCompletedSourceBudget_real_of_even_of_not_oddBad hp hodd)
      c.retainedOddShellCenter_pos
      (c.retainedCompletedSourceSharpDisk_real_of_even_of_not_oddBad hp hodd)
      hbarrier

/-- The same radius barrier also orients the completed-source scalar positively. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar_pos_of_sharpRadius_le_shellCenter_sq
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hbarrier :
      c.retainedSourceKernelSharpRadiusSq ≤
        c.retainedOddShellCenter ^ 2) :
    0 < c.retainedRealCompletedSourceScalar := by
  have hs :=
    c.retainedRealSourceScalar_pos_of_sharpRadius_le_shellCenter_sq
      hp hodd hbarrier
  exact
    realBudgetDisk_completed_pos
      c.retainedOddShiftBudget_pos
      (c.retainedCompletedSourceBudget_real_of_even_of_not_oddBad hp hodd)
      hs

/-- Under the radius barrier, M4 is positive as well. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealMomentFour_pos_of_sharpRadius_le_shellCenter_sq
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hbarrier :
      c.retainedSourceKernelSharpRadiusSq ≤
        c.retainedOddShellCenter ^ 2) :
    0 < c.retainedRealMomentFour := by
  have hs :=
    c.retainedRealSourceScalar_pos_of_sharpRadius_le_shellCenter_sq
      hp hodd hbarrier
  have hsm :=
    c.retainedRealSource_mul_momentFour_pos_of_even_of_not_oddBad hp hodd
  by_contra hmpos
  have hmle : c.retainedRealMomentFour ≤ 0 := le_of_not_gt hmpos
  have hmul :
      c.retainedRealSourceScalar * c.retainedRealMomentFour ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) hmle
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.star_evenShiftedMomentFour_eq_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedCompletedSourceBudget_real_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedCompletedSourceSharpDisk_real_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedSourceMoment_coercive_real_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelCenterDeficit_le_source_mul_completedOffset
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceCorridor_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceScalar_pos_of_sharpRadius_le_shellCenter_sq
