import Zeta23.ExceptionalZero.ApertureFreedom
import Zeta23.CCM.RegularFirstBadCanonicalEnergy

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Real Set
open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A4R7: exceptional-zero regular first-bad closure

A hypothetical off-line zeta zero already forces finite canonical badness at
every sufficiently large aperture.  We choose one sufficiently large physical
prime-cutoff cell, seed cell-badness at an interior point, and then hand the
problem to the pure CCM regular-first-bad theorem.

PR #153 retains the complete CCM certificate through this exceptional-zero
wrapper.  The historical tuple theorem remains available as a projection.

The output is a finite regular canonical state with strictly negative exact
pole/arch/scalar/prime channel energy.  No theorem here proves that this energy
is nonnegative, excludes the hypothetical zero, or proves RH.
-/

/-- Above every real threshold there is an interior point of a physical cutoff
cell whose cutoff index is at least one. -/
theorem exists_fixedCanonicalCutoffCell_point_above
    (L₀ : ℝ) :
    ∃ Q : ℕ,
      1 ≤ Q ∧
      ∃ L : ℝ,
        L ∈ fixedCanonicalCutoffCell Q ∧
        L₀ < L := by
  obtain ⟨Q, hQbig⟩ := exists_nat_gt (Real.exp L₀ + 1)
  have hQoneR : (1 : ℝ) < (Q : ℝ) := by
    have hexppos : 0 < Real.exp L₀ := Real.exp_pos L₀
    linarith
  have hQone : 1 < Q := by exact_mod_cast hQoneR
  have hQ : 1 ≤ Q := by omega
  have hQpos : (0 : ℝ) < (Q : ℝ) := by positivity
  have hQ1pos : (0 : ℝ) < ((Q + 1 : ℕ) : ℝ) := by positivity
  have hQQ1 : (Q : ℝ) < ((Q + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self Q
  have hloglt :
      Real.log (Q : ℝ) < Real.log ((Q + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log hQpos hQ1pos hQQ1
  let L : ℝ :=
    (Real.log (Q : ℝ) + Real.log ((Q + 1 : ℕ) : ℝ)) / 2
  have hLcell : L ∈ fixedCanonicalCutoffCell Q := by
    change Real.log (Q : ℝ) < L ∧
      L < Real.log ((Q + 1 : ℕ) : ℝ)
    dsimp [L]
    constructor <;> linarith
  have hexpQ : Real.exp L₀ < (Q : ℝ) := by linarith
  have hL₀logQ : L₀ < Real.log (Q : ℝ) :=
    (Real.lt_log_iff_exp_lt hQpos).2 hexpQ
  have hL₀L : L₀ < L := lt_trans hL₀logQ hLcell.1
  exact ⟨Q, hQ, L, hLcell, hL₀L⟩

/-- A hypothetical off-line zero forces a complete regular cell-minimal
negative-energy certificate in some physical cutoff cell. -/
theorem exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ Q : ℕ,
      Nonempty (RegularCellMinimalNegativeEnergyCertificate Q) := by
  obtain ⟨L₀, _hL₀pos, hbadAll⟩ :=
    eventually_all_apertures_have_anyParityBad_of_offLine_zero ρ₀ hoff
  obtain ⟨Q, hQ, Lseed, hLseedCell, hLseedBig⟩ :=
    exists_fixedCanonicalCutoffCell_point_above L₀
  obtain ⟨K, hbadSeed⟩ := hbadAll Lseed hLseedBig
  have hcellBad : CellAnyParityBad Q K :=
    ⟨Lseed, hLseedCell, hbadSeed⟩
  exact ⟨Q,
    exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
      Q hQ ⟨K, hcellBad⟩⟩

/-- Compatibility projection of the stronger off-line-zero certificate. -/
theorem exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ Q N : ℕ,
      ∃ L : ℝ,
        ∃ p : ReversalParity,
          ∃ x₀ : intrinsicParityPredecessorSubspace p N,
            ∃ lam : ℝ,
              1 ≤ Q ∧
              1 ≤ N ∧
              L ∈ fixedCanonicalCutoffCell Q ∧
              IntrinsicPredecessorRegular p L N ∧
              lam < 0 ∧
              intrinsicPredecessorBlock p L N x₀ =
                intrinsicShellToPredecessor p L N
                  (intrinsicCubicShellPart p N) ∧
              canonicalSourceChannelEnergy L (N + 1)
                  (cubicZeroShiftTrialVector p L N x₀ :
                    EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
  obtain ⟨Q, c⟩ :=
    exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero ρ₀ hoff
  obtain ⟨c⟩ := c
  exact ⟨Q, c.firstBad.Nstar, c.firstBad.L, c.firstBad.p, c.x₀, c.lam,
    c.firstBad.one_le_Q, c.firstBad.one_le_Nstar, c.firstBad.L_mem,
    c.firstBad.regular, c.lam_neg, c.preimage, c.channelEnergyNeg⟩

/-- Existential off-line-zero wrapper. -/
theorem exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ Q N : ℕ,
      ∃ L : ℝ,
        ∃ p : ReversalParity,
          ∃ x₀ : intrinsicParityPredecessorSubspace p N,
            1 ≤ Q ∧
            1 ≤ N ∧
            L ∈ fixedCanonicalCutoffCell Q ∧
            IntrinsicPredecessorRegular p L N ∧
            canonicalSourceChannelEnergy L (N + 1)
                (cubicZeroShiftTrialVector p L N x₀ :
                  EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  obtain ⟨Q, N, L, p, x₀, _lam, hQ, hN, hLcell, hreg,
      _hlam, _hx₀, hneg⟩ :=
    exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero ρ₀ hρ₀
  exact ⟨Q, N, L, p, x₀, hQ, hN, hLcell, hreg, hneg⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_fixedCanonicalCutoffCell_point_above
#print axioms Zeta23.ExceptionalZero.exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero