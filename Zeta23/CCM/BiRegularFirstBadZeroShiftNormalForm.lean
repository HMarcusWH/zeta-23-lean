import Zeta23.CCM.BiRegularFirstBadCanonicalEnergy
import Zeta23.CCM.RegularFirstBadZeroShiftSchurClassification
import Zeta23.CCM.RegularFirstBadZeroShiftKernelBalance

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: bi-regular zero-shift normal form

Simultaneous predecessor regularity removes every predecessor-kernel coordinate
at the retained aperture.  This kills the retained actual-shell resonance
coordinate, the #219 cubic-generator correction coordinate, and the #220
transported-index correction coordinate independently.

The exact #221 good/bad classification then becomes a pure zero-shift endpoint
sign classification.  The endpoint/response identity turns that into the sign
of the canonical shell response.  On the selected-even branch the existing
direct zero-shift cross-parity transfer therefore yields one scalar normal form

  sigma_- = alpha_0 * sigma_+ + Gamma_0 * mu_0,

with re(sigma_+) < 0 and odd badness equivalent to re(sigma_-) < 0.

The three kernel vectors are not identified; they vanish because the target
predecessor kernel itself is trivial.  No sign of the transferred odd scalar
is proved here, the odd-selected route remains open, and no negative-root,
finite-to-infinite, or RH theorem is claimed.
-/

/-- On a regular predecessor block every canonical kernel coordinate vanishes. -/
theorem intrinsicPredecessorKernelPart_eq_zero_of_regular
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorKernelPart p L N w = 0 := by
  have hinj : Function.Injective (intrinsicPredecessorBlock p L N) :=
    (intrinsicPredecessorRegular_iff_injective p L N).1 hreg
  have hsurj : Function.Surjective (intrinsicPredecessorBlock p L N) :=
    (LinearMap.injective_iff_surjective).1 hinj
  obtain ⟨x, hx⟩ := hsurj w
  exact
    (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range p L N).2
      ⟨x, hx⟩

/-- Bi-regularity kills the actual odd cubic shell-coupling kernel coordinate. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.oddCubicCouplingKernelPart_eq_zero
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q) :
    cubicCouplingKernelPart .odd
      c.energy.firstBad.L c.energy.firstBad.Nstar = 0 := by
  simpa [cubicCouplingKernelPart] using
    intrinsicPredecessorKernelPart_eq_zero_of_regular
      .odd c.energy.firstBad.L c.energy.firstBad.Nstar c.regular_odd
      (intrinsicShellToPredecessor .odd
        c.energy.firstBad.L c.energy.firstBad.Nstar
        (intrinsicCubicShellPart .odd c.energy.firstBad.Nstar))

/-- Bi-regularity independently kills the #219 odd cubic-generator correction
kernel coordinate. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.oddCubicGeneratorKernelPart_eq_zero
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q) :
    oddCubicGeneratorKernelPart
      c.energy.firstBad.L c.energy.firstBad.Nstar = 0 := by
  simpa [oddCubicGeneratorKernelPart] using
    intrinsicPredecessorKernelPart_eq_zero_of_regular
      .odd c.energy.firstBad.L c.energy.firstBad.Nstar c.regular_odd
      (oddCubicGeneratorPredecessorPart c.energy.firstBad.Nstar)

/-- Bi-regularity independently kills the #220 centered-index transported
correction kernel coordinate. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.oddIndexCubicShellKernelPart_eq_zero
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q) :
    oddIndexCubicShellKernelPart
      c.energy.firstBad.L c.energy.firstBad.Nstar = 0 := by
  simpa [oddIndexCubicShellKernelPart] using
    intrinsicPredecessorKernelPart_eq_zero_of_regular
      .odd c.energy.firstBad.L c.energy.firstBad.Nstar c.regular_odd
      (oddIndexCubicShellPredecessorPart c.energy.firstBad.Nstar)

/-- Both parity cubic shell couplings have unique zero-shift preimages at the
bi-regular retained aperture. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.existsUnique_zeroShiftPreimage
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (p : ReversalParity) :
    ∃! x₀ : intrinsicParityPredecessorSubspace p c.energy.firstBad.Nstar,
      intrinsicPredecessorBlock p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀ =
        intrinsicShellToPredecessor p
          c.energy.firstBad.L c.energy.firstBad.Nstar
          (intrinsicCubicShellPart p c.energy.firstBad.Nstar) := by
  cases p with
  | even =>
      exact existsUnique_cubicZeroShiftPreimage_of_regular
        .even c.energy.firstBad.L c.energy.firstBad.Nstar c.regular_even
  | odd =>
      exact existsUnique_cubicZeroShiftPreimage_of_regular
        .odd c.energy.firstBad.L c.energy.firstBad.Nstar c.regular_odd

/-- Once a zero-shift preimage is supplied, retained successor badness is
exactly strict negativity of its zero-shift Schur endpoint. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.successorParityBad_iff_zeroShiftEndpoint_re_neg
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (p : ReversalParity)
    (x₀ : intrinsicParityPredecessorSubspace p c.energy.firstBad.Nstar)
    (hx₀ :
      intrinsicPredecessorBlock p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀ =
        intrinsicShellToPredecessor p
          c.energy.firstBad.L c.energy.firstBad.Nstar
          (intrinsicCubicShellPart p c.energy.firstBad.Nstar)) :
    ParityBad p c.energy.firstBad.L (c.energy.firstBad.Nstar + 1) ↔
      Complex.re
        (cubicZeroShiftSchurEndpoint p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀) < 0 := by
  constructor
  · intro hbad
    exact
      cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
        p c.energy.firstBad.L_pos c.energy.firstBad.Nstar
        c.energy.firstBad.one_le_Nstar
        (c.energy.firstBad.predecessorNonnegative_anyParity p)
        hbad x₀ hx₀
  · intro hneg
    exact
      parityBad_of_cubicZeroShiftSchurEndpoint_re_neg
        p c.energy.firstBad.L c.energy.firstBad.Nstar
        c.energy.firstBad.one_le_Nstar x₀ hx₀ hneg

/-- Bi-regular retained badness is exactly strict negativity of the canonical
zero-shift shell response. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.successorParityBad_iff_zeroShiftShellResponse_re_neg
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (p : ReversalParity)
    (x₀ : intrinsicParityPredecessorSubspace p c.energy.firstBad.Nstar)
    (hx₀ :
      intrinsicPredecessorBlock p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀ =
        intrinsicShellToPredecessor p
          c.energy.firstBad.L c.energy.firstBad.Nstar
          (intrinsicCubicShellPart p c.energy.firstBad.Nstar)) :
    ParityBad p c.energy.firstBad.L (c.energy.firstBad.Nstar + 1) ↔
      Complex.re
        (cubicZeroShiftShellResponseScalar p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀) < 0 := by
  let shell :=
    (intrinsicCubicShellPart p c.energy.firstBad.Nstar :
      euclideanParityBoundaryFlatSubspace p (c.energy.firstBad.Nstar + 1))
  have hshell : shell ≠ 0 := by
    intro hzero
    exact (intrinsicCubicShellPart_ne_zero
      p c.energy.firstBad.Nstar c.energy.firstBad.one_le_Nstar)
      (Subtype.ext hzero)
  have hnorm : 0 < ‖shell‖ ^ 2 := by positivity
  have heq :=
    cubicZeroShiftSchurEndpoint_re_eq_shellResponse_re_mul_norm_sq
      p c.energy.firstBad.L c.energy.firstBad.Nstar
      c.energy.firstBad.one_le_Nstar x₀ hx₀
  constructor
  · intro hbad
    have hneg :=
      (c.successorParityBad_iff_zeroShiftEndpoint_re_neg p x₀ hx₀).1 hbad
    change
      Complex.re (cubicZeroShiftSchurEndpoint p
        c.energy.firstBad.L c.energy.firstBad.Nstar x₀) < 0 at hneg
    rw [heq] at hneg
    nlinarith
  · intro hresponse
    apply
      (c.successorParityBad_iff_zeroShiftEndpoint_re_neg p x₀ hx₀).2
    rw [heq]
    exact mul_neg_of_neg_of_pos hresponse hnorm

/-- Complementary good-sector form of the pure response-sign classification. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.not_successorParityBad_iff_zeroShiftShellResponse_re_nonnegative
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (p : ReversalParity)
    (x₀ : intrinsicParityPredecessorSubspace p c.energy.firstBad.Nstar)
    (hx₀ :
      intrinsicPredecessorBlock p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀ =
        intrinsicShellToPredecessor p
          c.energy.firstBad.L c.energy.firstBad.Nstar
          (intrinsicCubicShellPart p c.energy.firstBad.Nstar)) :
    (¬ ParityBad p c.energy.firstBad.L (c.energy.firstBad.Nstar + 1)) ↔
      0 ≤ Complex.re
        (cubicZeroShiftShellResponseScalar p
          c.energy.firstBad.L c.energy.firstBad.Nstar x₀) := by
  rw [c.successorParityBad_iff_zeroShiftShellResponse_re_neg p x₀ hx₀]
  exact not_lt

/-- Selected-even route-facing normal form.  Both zero-shift preimages exist at
the same aperture, the even response is strictly negative, the odd response
satisfies the exact direct cross-parity transfer, and odd badness is exactly
the sign of that transferred scalar. -/
theorem
    BiRegularCellMinimalNegativeEnergyCertificate.exists_evenOddZeroShiftScalarNormalForm_of_even
    {Q : ℕ}
    (c : BiRegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.energy.firstBad.p = ReversalParity.even) :
    ∃ xPlus : intrinsicParityPredecessorSubspace .even c.energy.firstBad.Nstar,
      ∃ xMinus : intrinsicParityPredecessorSubspace .odd c.energy.firstBad.Nstar,
        intrinsicPredecessorBlock .even
            c.energy.firstBad.L c.energy.firstBad.Nstar xPlus =
          intrinsicShellToPredecessor .even
            c.energy.firstBad.L c.energy.firstBad.Nstar
            (intrinsicCubicShellPart .even c.energy.firstBad.Nstar) ∧
        intrinsicPredecessorBlock .odd
            c.energy.firstBad.L c.energy.firstBad.Nstar xMinus =
          intrinsicShellToPredecessor .odd
            c.energy.firstBad.L c.energy.firstBad.Nstar
            (intrinsicCubicShellPart .odd c.energy.firstBad.Nstar) ∧
        Complex.re
          (cubicZeroShiftShellResponseScalar .even
            c.energy.firstBad.L c.energy.firstBad.Nstar xPlus) < 0 ∧
        cubicZeroShiftShellResponseScalar .odd
            c.energy.firstBad.L c.energy.firstBad.Nstar xMinus =
          crossParityZeroShiftAlpha c.energy.firstBad.Nstar xMinus *
              cubicZeroShiftShellResponseScalar .even
                c.energy.firstBad.L c.energy.firstBad.Nstar xPlus +
            crossParityZeroShiftGamma c.energy.firstBad.Nstar xMinus *
              explicitCanonicalSourceMoment
                c.energy.firstBad.L (c.energy.firstBad.Nstar + 1)
                (cubicZeroShiftTrialVector .even
                  c.energy.firstBad.L c.energy.firstBad.Nstar xPlus) ∧
        (ParityBad .odd
            c.energy.firstBad.L (c.energy.firstBad.Nstar + 1) ↔
          Complex.re
            (cubicZeroShiftShellResponseScalar .odd
              c.energy.firstBad.L c.energy.firstBad.Nstar xMinus) < 0) := by
  obtain ⟨xPlus, hxPlus, _huniqPlus⟩ :=
    c.existsUnique_zeroShiftPreimage .even
  obtain ⟨xMinus, hxMinus, _huniqMinus⟩ :=
    c.existsUnique_zeroShiftPreimage .odd
  refine ⟨xPlus, xMinus, hxPlus, hxMinus, ?_, ?_, ?_⟩
  · exact
      c.energy.evenZeroShiftShellResponse_re_neg_of_even
        hp xPlus hxPlus
  · exact
      cubicZeroShiftShellResponseScalar_crossParity_explicitSource_transfer
        c.energy.firstBad.L_pos c.energy.firstBad.Nstar
        c.energy.firstBad.one_le_Nstar
        xPlus hxPlus xMinus hxMinus
  · exact
      c.successorParityBad_iff_zeroShiftShellResponse_re_neg
        .odd xMinus hxMinus

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessorKernelPart_eq_zero_of_regular
#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate.oddCubicCouplingKernelPart_eq_zero
#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate.oddCubicGeneratorKernelPart_eq_zero
#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate.oddIndexCubicShellKernelPart_eq_zero
#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate.successorParityBad_iff_zeroShiftShellResponse_re_neg
#print axioms Zeta23.CCM.BiRegularCellMinimalNegativeEnergyCertificate.exists_evenOddZeroShiftScalarNormalForm_of_even
