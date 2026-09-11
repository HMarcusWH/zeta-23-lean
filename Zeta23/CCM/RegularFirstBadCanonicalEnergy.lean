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

This is a finite conditional certificate.  It is not a positivity theorem,
negative-root exclusion theorem, finite-to-infinite theorem, or RH theorem.
-/

/-- A bad cutoff cell contains a regular cell-minimal first-bad state whose
canonical zero-shift trial has strictly negative *exact source-channel* energy.
-/
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
  obtain ⟨Kstar, N, L, p, hKtwo, hN, hsucc, hLcell,
      hbad, hmin, hreg⟩ :=
    exists_regular_cellMinimal_firstBad Q hQ hex
  have hLpos : 0 < L := fixedCanonicalCutoffCell_subset_Ioi hQ hLcell
  have hNlt : N < Kstar := by omega
  have hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x) := by
    intro x hx
    exact euclideanParity_nonnegative_of_lt_least_anyParityBad
      L hmin p hNlt x hx
  have hbadSucc : ParityBad p L (N + 1) := by
    rw [hsucc]
    exact hbad
  obtain ⟨lam, hlam, v, hvne, hveig⟩ :=
    exists_negative_eigenmode_of_parityBad hbadSucc
  have hroot : cubicExplicitSchurScalar p hLpos N hprev lam hlam = 0 :=
    (cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
      p hLpos N hN hprev lam hlam).2 ⟨v, hvne, hveig⟩
  obtain ⟨x₀, hx₀, _hunique⟩ :=
    existsUnique_cubicZeroShiftPreimage_of_regular p L N hreg
  have henergyNeg :
      parityCanonicalSourceEnergy p L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀) < 0 :=
    parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_neg_of_explicit_root
      p hLpos N hN hprev x₀ hx₀ lam hlam hroot
  have henergyEq :=
    parityCanonicalSourceEnergy_eq_channels
      p hLpos (N + 1) (cubicZeroShiftTrialVector p L N x₀)
  have hchannelNeg :
      canonicalSourceChannelEnergy L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀ :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
    rw [← henergyEq]
    exact henergyNeg
  exact ⟨N, L, p, x₀, lam, hN, hLcell, hreg, hlam, hx₀,
    henergyNeg, hchannelNeg⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_regular_cellMinimal_negativeCanonicalEnergy
