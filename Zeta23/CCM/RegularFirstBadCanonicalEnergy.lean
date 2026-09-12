import Zeta23.CCM.CellMinimalRegularFirstBad
import Zeta23.CCM.ConstrainedParitySpectrum
import Zeta23.CCM.CubicExplicitSecular
import Zeta23.CCM.CanonicalSourceEnergy

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4R6: regular first-bad canonical energy

Cell-minimality supplies predecessor nonnegativity at the regular aperture.
The already-proved finite spectral and Schur machinery then turns successor
badness into a negative explicit Schur root.  Regularity supplies the unique
zero-shift preimage, and the existing canonical energy theorem converts the
root into strict negativity of the exact pole/arch/scalar/prime source-channel
energy on the canonical zero-shift trial.

PR #153 retains that entire state instead of projecting away the predecessor
nonnegativity, explicit Schur root equation, whole-cell ancestry, and preimage.
The historical tuple theorem remains available as a compatibility projection.

This is a finite conditional certificate.  It is not a positivity theorem,
negative-root exclusion theorem, finite-to-infinite theorem, or RH theorem.
-/

/-- Full regular first-bad state carrying both the construction ancestry and the
negative canonical zero-shift energy. -/
structure RegularCellMinimalNegativeEnergyCertificate (Q : ℕ) where
  firstBad : RegularCellMinimalFirstBadCertificate Q
  predecessorNonnegative :
    ∀ x : EuclideanSpace ℂ (Fin (2 * firstBad.Nstar + 1)),
      x ∈ euclideanParityBoundaryFlatSubspace firstBad.p firstBad.Nstar →
        0 ≤ Complex.re
          (inner ℂ
            ((canonicalSourceMatrix firstBad.L firstBad.Nstar).toEuclideanLin x)
            x)
  x₀ : intrinsicParityPredecessorSubspace firstBad.p firstBad.Nstar
  lam : ℝ
  lam_neg : lam < 0
  explicit_root :
    cubicExplicitSchurScalar firstBad.p firstBad.L_pos firstBad.Nstar
      predecessorNonnegative lam lam_neg = 0
  preimage :
    intrinsicPredecessorBlock
        firstBad.p firstBad.L firstBad.Nstar x₀ =
      intrinsicShellToPredecessor
        firstBad.p firstBad.L firstBad.Nstar
        (intrinsicCubicShellPart firstBad.p firstBad.Nstar)
  parityEnergyNeg :
    parityCanonicalSourceEnergy
        firstBad.p firstBad.L (firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          firstBad.p firstBad.L firstBad.Nstar x₀) < 0
  channelEnergyNeg :
    canonicalSourceChannelEnergy
        firstBad.L (firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector
          firstBad.p firstBad.L firstBad.Nstar x₀ :
          EuclideanSpace ℂ (Fin (2 * (firstBad.Nstar + 1) + 1))) < 0

/-- A bad cutoff cell produces the complete regular cell-minimal negative-energy
certificate. -/
theorem exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hex : ∃ K : ℕ, CellAnyParityBad Q K) :
    Nonempty (RegularCellMinimalNegativeEnergyCertificate Q) := by
  obtain ⟨c⟩ := exists_regular_cellMinimal_firstBadCertificate Q hQ hex
  have hNlt : c.Nstar < c.Kstar := by
    omega
  have hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * c.Nstar + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace c.p c.Nstar →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix c.L c.Nstar).toEuclideanLin x) x) := by
    intro x hx
    exact euclideanParity_nonnegative_of_lt_least_anyParityBad
      c.L c.smaller_good c.p hNlt x hx
  have hbadSucc : ParityBad c.p c.L (c.Nstar + 1) := by
    rw [c.succ_eq]
    exact c.bad
  obtain ⟨lam, hlam, v, hvne, hveig⟩ :=
    exists_negative_eigenmode_of_parityBad hbadSucc
  have hroot :
      cubicExplicitSchurScalar c.p c.L_pos c.Nstar hprev lam hlam = 0 :=
    (cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
      c.p c.L_pos c.Nstar c.one_le_Nstar hprev lam hlam).2
      ⟨v, hvne, hveig⟩
  obtain ⟨x₀, hx₀, _hunique⟩ :=
    existsUnique_cubicZeroShiftPreimage_of_regular c.p c.L c.Nstar c.regular
  have henergyNeg :
      parityCanonicalSourceEnergy c.p c.L (c.Nstar + 1)
        (cubicZeroShiftTrialVector c.p c.L c.Nstar x₀) < 0 :=
    parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_neg_of_explicit_root
      c.p c.L_pos c.Nstar c.one_le_Nstar hprev x₀ hx₀ lam hlam hroot
  have henergyEq :=
    parityCanonicalSourceEnergy_eq_channels
      c.p c.L_pos (c.Nstar + 1)
        (cubicZeroShiftTrialVector c.p c.L c.Nstar x₀)
  have hchannelNeg :
      canonicalSourceChannelEnergy c.L (c.Nstar + 1)
        (cubicZeroShiftTrialVector c.p c.L c.Nstar x₀ :
          EuclideanSpace ℂ (Fin (2 * (c.Nstar + 1) + 1))) < 0 := by
    rw [← henergyEq]
    exact henergyNeg
  exact ⟨{
    firstBad := c
    predecessorNonnegative := hprev
    x₀ := x₀
    lam := lam
    lam_neg := hlam
    explicit_root := hroot
    preimage := hx₀
    parityEnergyNeg := henergyNeg
    channelEnergyNeg := hchannelNeg
  }⟩

/-- Compatibility projection retaining the pre-#153 theorem surface. -/
theorem exists_regular_cellMinimal_negativeCanonicalEnergy
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hex : ∃ K : ℕ, CellAnyParityBad Q K) :
    ∃ N : ℕ,
      ∃ L : ℝ,
        ∃ p : ReversalParity,
          ∃ x₀ : intrinsicParityPredecessorSubspace p N,
            ∃ lam : ℝ,
              1 ≤ N ∧
              L ∈ fixedCanonicalCutoffCell Q ∧
              IntrinsicPredecessorRegular p L N ∧
              lam < 0 ∧
              intrinsicPredecessorBlock p L N x₀ =
                intrinsicShellToPredecessor p L N
                  (intrinsicCubicShellPart p N) ∧
              parityCanonicalSourceEnergy p L (N + 1)
                  (cubicZeroShiftTrialVector p L N x₀) < 0 ∧
              canonicalSourceChannelEnergy L (N + 1)
                  (cubicZeroShiftTrialVector p L N x₀ :
                    EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
  obtain ⟨c⟩ :=
    exists_regular_cellMinimal_negativeCanonicalEnergyCertificate Q hQ hex
  exact ⟨c.firstBad.Nstar, c.firstBad.L, c.firstBad.p, c.x₀, c.lam,
    c.firstBad.one_le_Nstar, c.firstBad.L_mem, c.firstBad.regular,
    c.lam_neg, c.preimage, c.parityEnergyNeg, c.channelEnergyNeg⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate
#print axioms Zeta23.CCM.exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
#print axioms Zeta23.CCM.exists_regular_cellMinimal_negativeCanonicalEnergy