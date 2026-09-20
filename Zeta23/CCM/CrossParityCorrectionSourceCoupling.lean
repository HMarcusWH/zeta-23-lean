import Zeta23.CCM.CrossParityCorrectionFunctionalRiesz
import Zeta23.CCM.CanonicalOneStepDomination

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: correction source coupling

The #229 Riesz representative for the safe odd predecessor-correction
functional is routed into the existing canonical shell/source coupling.

For every odd predecessor direction `y`,

  star (chi y) * <c,c> = cubicShellCoupling (R y),

where `c` is the odd cubic shell, `R` is the safe negative-shift
predecessor resolvent, and the shell coupling is the exact production-channel
pairing already used by the one-step domination layer.

The alpha and Gamma correction coefficients are specializations of the same
identity.  No sign, phase, domination, negative-root exclusion, or RH claim is
made.
-/

/-- The #229 correction-functional Riesz pairing is exactly the canonical
shell/source coupling after conjugating into the shell-coupling orientation. -/
theorem
    star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (y : intrinsicParityPredecessorSubspace .odd N) :
    star
        (oddSafeSecularCorrectionFunctional
          hL N hprevOdd lam hlam y) *
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      cubicShellCoupling .odd L N
        (shiftedIntrinsicPredecessorResolvent
          .odd hL N hprevOdd lam hlam y) := by
  let c := intrinsicCubicShellPart .odd N
  let b := intrinsicShellToPredecessor .odd L N c
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let chi := oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
  let den :=
    inner ℂ
      (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
      (c : euclideanParityBoundaryFlatSubspace .odd (N + 1))
  have hden : den ≠ 0 := by
    simpa [den, c] using
      inner_intrinsicCubicShellPart_self_ne_zero .odd N hN
  have hrepr :=
    oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div
      hL N hN hprevOdd lam hlam y
  change
    chi y =
      inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (y : euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
        den at hrepr
  have hsym :=
    shiftedIntrinsicPredecessorResolvent_isSymmetric
      .odd hL N hprevOdd hlam b y
  change
    inner ℂ
        ((R b : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (y : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      inner ℂ
        (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        ((R y : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) at hsym
  have hnumStar :
      (starRingEnd ℂ)
          (inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (y : euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        cubicShellCoupling .odd L N (R y) := by
    calc
      (starRingEnd ℂ)
          (inner ℂ
            ((R b : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (y : euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        (starRingEnd ℂ)
          (inner ℂ
            (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
            ((R y : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) :=
        congrArg (starRingEnd ℂ) hsym
      _ =
        inner ℂ
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        exact
          inner_conj_symm
            ((R y : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
      _ = cubicShellCoupling .odd L N (R y) := by
        rfl
  have hdenStar : (starRingEnd ℂ) den = den := by
    simp [den]
  have hreprStar := congrArg (starRingEnd ℂ) hrepr
  simp only [map_div] at hreprStar
  rw [hdenStar, hnumStar] at hreprStar
  change (starRingEnd ℂ) (chi y) * den =
    cubicShellCoupling .odd L N (R y)
  rw [hreprStar]
  field_simp [hden]

/-- Production-channel form of the correction-functional source-coupling
identity. -/
theorem
    star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_channels
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (y : intrinsicParityPredecessorSubspace .odd N) :
    star
        (oddSafeSecularCorrectionFunctional
          hL N hprevOdd lam hlam y) *
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      canonicalSourceChannelPairing L (N + 1)
        (((shiftedIntrinsicPredecessorResolvent
            .odd hL N hprevOdd lam hlam y :
            intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
        ((intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
  rw [
    star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling
      hL N hN hprevOdd lam hlam y,
    cubicShellCoupling_eq_channels .odd hL N
      (shiftedIntrinsicPredecessorResolvent
        .odd hL N hprevOdd lam hlam y)
  ]

/-- The remaining alpha correction is the shell coupling evaluated on the
resolvent of the transported index-cubic predecessor direction. -/
theorem
    star_one_sub_crossParitySecularAlpha_mul_shellInner_eq_cubicShellCoupling
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star
        (1 - crossParitySecularAlpha
          hL N hprevOdd lam hlam) *
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      cubicShellCoupling .odd L N
        (shiftedIntrinsicPredecessorResolvent
          .odd hL N hprevOdd lam hlam
          (oddIndexCubicShellPredecessorPart N)) := by
  have halpha :
      1 - crossParitySecularAlpha hL N hprevOdd lam hlam =
        oddSafeSecularCorrectionFunctional
          hL N hprevOdd lam hlam
          (oddIndexCubicShellPredecessorPart N) := by
    change
      1 -
          (1 -
            oddSafeSecularCorrectionFunctional
              hL N hprevOdd lam hlam
              (oddIndexCubicShellPredecessorPart N)) =
        oddSafeSecularCorrectionFunctional
          hL N hprevOdd lam hlam
          (oddIndexCubicShellPredecessorPart N)
    ring
  rw [halpha]
  exact
    star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling
      hL N hN hprevOdd lam hlam (oddIndexCubicShellPredecessorPart N)

/-- The remaining Gamma correction is the shell coupling evaluated on the
resolvent of the odd cubic-generator predecessor direction. -/
theorem
    star_one_sub_crossParitySecularGamma_mul_shellInner_eq_cubicShellCoupling
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star
        (1 - crossParitySecularGamma
          hL N hprevOdd lam hlam) *
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      cubicShellCoupling .odd L N
        (shiftedIntrinsicPredecessorResolvent
          .odd hL N hprevOdd lam hlam
          (oddCubicGeneratorPredecessorPart N)) := by
  have hgamma :
      1 - crossParitySecularGamma hL N hprevOdd lam hlam =
        oddSafeSecularCorrectionFunctional
          hL N hprevOdd lam hlam
          (oddCubicGeneratorPredecessorPart N) := by
    change
      1 -
          (1 -
            oddSafeSecularCorrectionFunctional
              hL N hprevOdd lam hlam
              (oddCubicGeneratorPredecessorPart N)) =
        oddSafeSecularCorrectionFunctional
          hL N hprevOdd lam hlam
          (oddCubicGeneratorPredecessorPart N)
    ring
  rw [hgamma]
  exact
    star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling
      hL N hN hprevOdd lam hlam (oddCubicGeneratorPredecessorPart N)

/-- Rearranged Gamma form used directly by the retained source-completion
identity. -/
theorem
    star_crossParitySecularGamma_mul_shellInner_eq_shellInner_sub_cubicShellCoupling
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star
        (crossParitySecularGamma
          hL N hprevOdd lam hlam) *
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
        cubicShellCoupling .odd L N
          (shiftedIntrinsicPredecessorResolvent
            .odd hL N hprevOdd lam hlam
            (oddCubicGeneratorPredecessorPart N)) := by
  have h :=
    star_one_sub_crossParitySecularGamma_mul_shellInner_eq_cubicShellCoupling
      hL N hN hprevOdd lam hlam
  simp only [map_sub, map_one] at h
  calc
    star
        (crossParitySecularGamma
          hL N hprevOdd lam hlam) *
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
      inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) -
        (1 -
          star
            (crossParitySecularGamma
              hL N hprevOdd lam hlam)) *
          inner ℂ
            (intrinsicCubicShellPart .odd N :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (intrinsicCubicShellPart .odd N :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        ring
    _ = _ := by rw [h]

end Zeta23.CCM

#print axioms Zeta23.CCM.star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling
#print axioms Zeta23.CCM.star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_channels
#print axioms Zeta23.CCM.star_one_sub_crossParitySecularAlpha_mul_shellInner_eq_cubicShellCoupling
#print axioms Zeta23.CCM.star_one_sub_crossParitySecularGamma_mul_shellInner_eq_cubicShellCoupling
#print axioms Zeta23.CCM.star_crossParitySecularGamma_mul_shellInner_eq_shellInner_sub_cubicShellCoupling
