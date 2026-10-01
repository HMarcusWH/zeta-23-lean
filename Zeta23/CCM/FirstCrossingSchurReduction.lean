import Zeta23.CCM.CanonicalParityFirstCrossingShell
import Zeta23.CCM.ZeroShiftSchurClassification
import Zeta23.CCM.CanonicalApertureRegularityScaffold

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#278 first-crossing Schur reduction

This module isolates the static one-step algebra needed at nearby bad points.

The predecessor hypothesis is exactly the one consumed by the existing
zero-shift Schur classification.  A nonnegative predecessor parity bottom
supplies that hypothesis directly.  The N=1 predecessor carrier is
zero-dimensional and is handled separately.

At a regular predecessor block, successor badness therefore forces a genuine
negative zero-shift Schur endpoint.  No aperture barrier is asserted here.
-/

/-- The exact predecessor-sector nonnegativity premise used by the one-step
Schur machinery. -/
def PredecessorSectorNonnegative
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop :=
  ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
    x ∈ euclideanParityBoundaryFlatSubspace p N →
      0 ≤ Complex.re
        (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x)

/-- A nonnegative parity Rayleigh bottom gives the exact all-vector predecessor
nonnegativity premise. -/
theorem predecessorSectorNonnegative_of_parityBottom_nonnegative
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hbottom : 0 ≤ parityRayleighBottom p L N) :
    PredecessorSectorNonnegative p L N := by
  intro x hx
  let v : euclideanParityBoundaryFlatSubspace p N := ⟨x, hx⟩
  have hq :=
    parityRayleighBottom_mul_norm_sq_le p L N v
  have hleft :
      0 ≤ parityRayleighBottom p L N * ‖v‖ ^ 2 :=
    mul_nonneg hbottom (sq_nonneg ‖v‖)
  have hcomp :
      0 ≤ Complex.re
        (inner ℂ (parityCompressedCanonical p L N v) v) :=
    le_trans hleft hq
  have hbridge :=
    re_inner_parityCompressedCanonical_self p L N v
  calc
    0 ≤ Complex.re
        (inner ℂ (parityCompressedCanonical p L N v) v) := hcomp
    _ =
      Complex.re
        (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x) := by
          simpa [v] using hbridge

/-- The legal parity predecessor carrier at size one is zero-dimensional, so
its canonical quadratic form is nonnegative at every aperture. -/
theorem predecessorSectorNonnegative_one
    (p : ReversalParity) (L : ℝ) :
    PredecessorSectorNonnegative p L 1 := by
  intro x hx
  let v : euclideanParityBoundaryFlatSubspace p 1 := ⟨x, hx⟩
  have hfin :
      Module.finrank ℂ (euclideanParityBoundaryFlatSubspace p 1) = 0 := by
    simpa using
      (finrank_euclideanParityBoundaryFlatSubspace p 1 (by norm_num))
  have hsub :
      Subsingleton (euclideanParityBoundaryFlatSubspace p 1) :=
    (Module.finrank_zero_iff).mp hfin
  have hv : v = 0 := @Subsingleton.elim _ hsub v 0
  have hx0 : x = 0 := by
    have hval := congrArg Subtype.val hv
    simpa [v] using hval
  subst x
  simp

/-- Static regular-branch compression: over a nonnegative predecessor, every
bad successor with a regular predecessor block has a canonical zero-shift
preimage whose Schur endpoint is strictly negative. -/
theorem exists_zeroShiftEndpoint_neg_of_regular_parityBad
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev : PredecessorSectorNonnegative p L N)
    (hbad : ParityBad p L (N + 1))
    (hreg : IntrinsicPredecessorRegular p L N) :
    ∃ x₀ : intrinsicParityPredecessorSubspace p N,
      intrinsicPredecessorBlock p L N x₀ =
        intrinsicShellToPredecessor p L N
          (intrinsicCubicShellPart p N) ∧
      Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) < 0 := by
  obtain ⟨x₀, hx₀, _huniq⟩ :=
    existsUnique_cubicZeroShiftPreimage_of_regular p L N hreg
  refine ⟨x₀, hx₀, ?_⟩
  exact
    cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
      p hL N hN hprev hbad x₀ hx₀

/-- The first-crossing minimality theorem upgrades to the exact all-vector
predecessor nonnegativity premise on some punctured right-neighborhood of the
contact.  The k=1 edge is the zero-dimensional predecessor carrier. -/
theorem CanonicalParityFirstCrossingShell.exists_predecessorSectorNonnegative_right_window
    (c : CanonicalParityFirstCrossingShell) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ L : ℝ, c.Lstar < L → L < c.Lstar + δ →
        PredecessorSectorNonnegative c.p L c.k := by
  rcases c.predecessorGround_stable with hk | hstable
  · refine ⟨1, by norm_num, ?_⟩
    intro L _hLlo _hLhi
    simpa [hk] using predecessorSectorNonnegative_one c.p L
  · obtain ⟨δ, hδ, hstable⟩ := hstable
    refine ⟨δ, hδ, ?_⟩
    intro L hLlo hLhi
    by_cases hk : c.k = 1
    · simpa [hk] using predecessorSectorNonnegative_one c.p L
    · have hk1 : 1 ≤ c.k := le_trans c.one_le_n c.n_le_k
      have hk2 : 2 ≤ c.k := by omega
      have hground :=
        hstable L (le_of_lt hLlo) hLhi
      have hsucc : c.k - 1 + 1 = c.k := by omega
      have hbottom :
          0 ≤ parityRayleighBottom c.p L c.k := by
        simpa [paritySuccessorGround, hsucc] using hground
      exact
        predecessorSectorNonnegative_of_parityBottom_nonnegative
          c.p L c.k hbottom

/-- Strict negativity of the attained successor parity ground is exactly
enough to produce the existing finite `ParityBad` witness. -/
theorem parityBad_of_paritySuccessorGround_neg
    (p : ReversalParity)
    {L : ℝ}
    (N : ℕ) (hN : 1 ≤ N)
    (hneg : paritySuccessorGround p N L < 0) :
    ParityBad p L (N + 1) := by
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ p L N hN
  exact
    parityBad_of_negative_eigenmode
      (by simpa [paritySuccessorGround] using hneg)
      hvne hveig

/-- Every canonical first-crossing shell has successor-bad points arbitrarily
close to the right at which the one-step predecessor sector is still
nonnegative.  This is the dynamic bridge from N-flow minimality to the exact
Schur-classification hypotheses. -/
theorem CanonicalParityFirstCrossingShell.exists_badPoint_with_nonnegativePredecessor
    (c : CanonicalParityFirstCrossingShell)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ,
      c.Lstar < L ∧
      L < c.Lstar + ε ∧
      PredecessorSectorNonnegative c.p L c.k ∧
      ParityBad c.p L (c.k + 1) := by
  have hk1 : 1 ≤ c.k := le_trans c.one_le_n c.n_le_k
  have hbad_of_ground :
      ∀ {L : ℝ},
        paritySuccessorGround c.p c.k L < 0 →
          ParityBad c.p L (c.k + 1) := by
    intro L hneg
    exact parityBad_of_paritySuccessorGround_neg
      c.p c.k hk1 hneg

  rcases c.predecessorGround_stable with hk | hstable
  · obtain ⟨L, hLlo, hLhi, hLneg⟩ :=
      c.successor_right_crossing ε hε
    have hprev :
        PredecessorSectorNonnegative c.p L c.k := by
      simpa [hk] using predecessorSectorNonnegative_one c.p L
    exact ⟨L, hLlo, hLhi, hprev, hbad_of_ground hLneg⟩
  · obtain ⟨δ, hδ, hstable⟩ := hstable
    let η : ℝ := min ε δ
    have hη : 0 < η := lt_min hε hδ
    obtain ⟨L, hLlo, hLhiη, hLneg⟩ :=
      c.successor_right_crossing η hη
    have hLhiε : L < c.Lstar + ε := by
      have hηε : η ≤ ε := min_le_left _ _
      linarith
    have hLhiδ : L < c.Lstar + δ := by
      have hηδ : η ≤ δ := min_le_right _ _
      linarith
    by_cases hk : c.k = 1
    · have hprev :
          PredecessorSectorNonnegative c.p L c.k := by
        simpa [hk] using predecessorSectorNonnegative_one c.p L
      exact ⟨L, hLlo, hLhiε, hprev, hbad_of_ground hLneg⟩
    · have hpredGround :=
        hstable L (le_of_lt hLlo) hLhiδ
      have hk2 : 2 ≤ c.k := by omega
      have hsucc : c.k - 1 + 1 = c.k := by omega
      have hbottom :
          0 ≤ parityRayleighBottom c.p L c.k := by
        simpa [paritySuccessorGround, hsucc] using hpredGround
      have hprev :
          PredecessorSectorNonnegative c.p L c.k :=
        predecessorSectorNonnegative_of_parityBottom_nonnegative
          c.p L c.k hbottom
      exact ⟨L, hLlo, hLhiε, hprev, hbad_of_ground hLneg⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.predecessorSectorNonnegative_of_parityBottom_nonnegative
#print axioms Zeta23.CCM.predecessorSectorNonnegative_one
#print axioms Zeta23.CCM.exists_zeroShiftEndpoint_neg_of_regular_parityBad
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.exists_predecessorSectorNonnegative_right_window
#print axioms Zeta23.CCM.parityBad_of_paritySuccessorGround_neg
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.exists_badPoint_with_nonnegativePredecessor
