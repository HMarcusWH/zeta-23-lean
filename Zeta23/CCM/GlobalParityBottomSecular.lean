import Zeta23.CCM.GlobalParityBottomSpectrum
import Zeta23.CCM.CubicSecularGoodSectorMargin

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — global-bottom secular geometry

This module evaluates the existing exact cubic secular machinery at the true
two-parity spectral bottoms introduced by GlobalParityBottomSpectrum.

The historical good-sector theorem used successor goodness at zero.  Here the
common negative shift is instead chosen at one parity ground state.  A strict
separation between the two parity bottoms gives a positive shifted spectral gap
in the opposite parity even if that parity is itself bad at zero.

No cross-parity transfer is used yet; this file only proves the exact selected
root / opposite-margin trichotomy.
-/

/-- The shell-scaled secular value pays at least the exact distance from the
chosen negative shift to the true parity bottom. -/
theorem parityBottom_gap_mul_cubicTrial_norm_sq_le_shellPairing
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    (parityRayleighBottom p L (N + 1) - lam) *
        ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 ≤
      Complex.re
        (star (cubicSecularScalar p hL N hprev lam hlam) *
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  let u := cubicSecularTrialVector p hL N hprev lam hlam
  have hbottom :=
    parityRayleighBottom_mul_norm_sq_le
      p L (N + 1) u
  have henergy :=
    re_inner_cubicSecularTrialVector_eq
      p hL N hN hprev lam hlam
  change
    parityRayleighBottom p L (N + 1) * ‖u‖ ^ 2 ≤
      RCLike.re
        (inner ℂ (parityCompressedCanonical p L (N + 1) u) u) at hbottom
  change
    Complex.re
        (inner ℂ (parityCompressedCanonical p L (N + 1) u) u) =
      lam * ‖u‖ ^ 2 +
        Complex.re
          (star (cubicSecularScalar p hL N hprev lam hlam) *
            inner ℂ
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))) at henergy
  simpa only [RCLike.re_to_complex] at hbottom
  rw [henergy] at hbottom
  simpa [u] using (show
    (parityRayleighBottom p L (N + 1) - lam) * ‖u‖ ^ 2 ≤
      Complex.re
        (star (cubicSecularScalar p hL N hprev lam hlam) *
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) by
    linarith)

/-- A negative shift strictly below the true parity bottom forces a strictly
positive shell-scaled secular orientation.  Unlike the historical good-sector
margin, no goodness-at-zero hypothesis appears. -/
theorem cubicSecularScalar_shellPairing_pos_of_lt_parityBottom
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hbelow : lam < parityRayleighBottom p L (N + 1)) :
    0 <
      Complex.re
        (star (cubicSecularScalar p hL N hprev lam hlam) *
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  have hmargin :=
    parityBottom_gap_mul_cubicTrial_norm_sq_le_shellPairing
      p hL N hN hprev lam hlam
  have hune :
      cubicSecularTrialVector p hL N hprev lam hlam ≠ 0 :=
    cubicSecularTrialVector_ne_zero p hL N hN hprev lam hlam
  have hnorm :
      0 < ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 := by
    positivity
  have hleft :
      0 <
        (parityRayleighBottom p L (N + 1) - lam) *
          ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 :=
    mul_pos (sub_pos.mpr hbelow) hnorm
  exact lt_of_lt_of_le hleft hmargin

/-- At a negative true parity bottom the exact cubic secular scalar vanishes,
because the bottom is attained and the existing explicit secular criterion is
an iff with genuine eigenmodes. -/
theorem cubicSecularScalar_eq_zero_at_parityBottom
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hneg : parityRayleighBottom p L (N + 1) < 0) :
    cubicSecularScalar p hL N hprev
        (parityRayleighBottom p L (N + 1)) hneg = 0 := by
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ p L N hN
  have hexp :
      cubicExplicitSchurScalar p hL N hprev
          (parityRayleighBottom p L (N + 1)) hneg = 0 :=
    (cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
      p hL N hN hprev
        (parityRayleighBottom p L (N + 1)) hneg).2
      ⟨v, hvne, hveig⟩
  exact
    (cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
      p hL N hN hprev
        (parityRayleighBottom p L (N + 1)) hneg).1 hexp

/-- Strict even-bottom branch: the even ground state is an exact secular root,
while the odd secular shell pairing is strictly positive at the same shift. -/
theorem globalBottom_evenStrict_secular
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hbad : AnyParityBad L (N + 1))
    (hstrict :
      parityRayleighBottom .even L (N + 1) <
        parityRayleighBottom .odd L (N + 1)) :
    ∃ hneg : parityRayleighBottom .even L (N + 1) < 0,
      cubicSecularScalar .even hL N (hprevBoth .even)
          (parityRayleighBottom .even L (N + 1)) hneg = 0 ∧
      0 <
        Complex.re
          (star
              (cubicSecularScalar .odd hL N (hprevBoth .odd)
                (parityRayleighBottom .even L (N + 1)) hneg) *
            inner ℂ
              (intrinsicCubicShellPart .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))
              (intrinsicCubicShellPart .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
  have hglobal :=
    globalParitySuccessorBottom_neg_of_anyParityBad hbad
  have hmin :
      globalParitySuccessorBottom L N =
        parityRayleighBottom .even L (N + 1) := by
    exact min_eq_left (le_of_lt hstrict)
  rw [hmin] at hglobal
  let hneg : parityRayleighBottom .even L (N + 1) < 0 := hglobal
  refine ⟨hneg, ?_, ?_⟩
  · exact cubicSecularScalar_eq_zero_at_parityBottom
      .even hL N hN (hprevBoth .even) hneg
  · exact cubicSecularScalar_shellPairing_pos_of_lt_parityBottom
      .odd hL N hN (hprevBoth .odd)
      (parityRayleighBottom .even L (N + 1)) hneg hstrict

/-- Strict odd-bottom branch: the odd ground state is an exact secular root,
while the even secular shell pairing is strictly positive at the same shift. -/
theorem globalBottom_oddStrict_secular
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hbad : AnyParityBad L (N + 1))
    (hstrict :
      parityRayleighBottom .odd L (N + 1) <
        parityRayleighBottom .even L (N + 1)) :
    ∃ hneg : parityRayleighBottom .odd L (N + 1) < 0,
      cubicSecularScalar .odd hL N (hprevBoth .odd)
          (parityRayleighBottom .odd L (N + 1)) hneg = 0 ∧
      0 <
        Complex.re
          (star
              (cubicSecularScalar .even hL N (hprevBoth .even)
                (parityRayleighBottom .odd L (N + 1)) hneg) *
            inner ℂ
              (intrinsicCubicShellPart .even N :
                euclideanParityBoundaryFlatSubspace .even (N + 1))
              (intrinsicCubicShellPart .even N :
                euclideanParityBoundaryFlatSubspace .even (N + 1))) := by
  have hglobal :=
    globalParitySuccessorBottom_neg_of_anyParityBad hbad
  have hmin :
      globalParitySuccessorBottom L N =
        parityRayleighBottom .odd L (N + 1) := by
    exact min_eq_right (le_of_lt hstrict)
  rw [hmin] at hglobal
  let hneg : parityRayleighBottom .odd L (N + 1) < 0 := hglobal
  refine ⟨hneg, ?_, ?_⟩
  · exact cubicSecularScalar_eq_zero_at_parityBottom
      .odd hL N hN (hprevBoth .odd) hneg
  · exact cubicSecularScalar_shellPairing_pos_of_lt_parityBottom
      .even hL N hN (hprevBoth .even)
      (parityRayleighBottom .odd L (N + 1)) hneg hstrict

/-- Tied-bottom branch: the same negative shift is an exact secular root in
both parity sectors. -/
theorem globalBottom_tie_secular
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hbad : AnyParityBad L (N + 1))
    (htie :
      parityRayleighBottom .even L (N + 1) =
        parityRayleighBottom .odd L (N + 1)) :
    ∃ hneg : parityRayleighBottom .even L (N + 1) < 0,
      cubicSecularScalar .even hL N (hprevBoth .even)
          (parityRayleighBottom .even L (N + 1)) hneg = 0 ∧
      cubicSecularScalar .odd hL N (hprevBoth .odd)
          (parityRayleighBottom .even L (N + 1)) hneg = 0 := by
  have hglobal :=
    globalParitySuccessorBottom_neg_of_anyParityBad hbad
  have hmin :
      globalParitySuccessorBottom L N =
        parityRayleighBottom .even L (N + 1) := by
    exact min_eq_left (le_of_eq htie)
  rw [hmin] at hglobal
  let hneg : parityRayleighBottom .even L (N + 1) < 0 := hglobal
  have heven :=
    cubicSecularScalar_eq_zero_at_parityBottom
      .even hL N hN (hprevBoth .even) hneg
  have hoddNeg :
      parityRayleighBottom .odd L (N + 1) < 0 := by
    rw [← htie]
    exact hneg
  have hoddRaw :=
    cubicSecularScalar_eq_zero_at_parityBottom
      .odd hL N hN (hprevBoth .odd) hoddNeg
  have hodd :
      cubicSecularScalar .odd hL N (hprevBoth .odd)
          (parityRayleighBottom .even L (N + 1)) hneg = 0 := by
    simpa [htie] using hoddRaw
  exact ⟨hneg, heven, hodd⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.parityBottom_gap_mul_cubicTrial_norm_sq_le_shellPairing
#print axioms Zeta23.CCM.cubicSecularScalar_shellPairing_pos_of_lt_parityBottom
#print axioms Zeta23.CCM.cubicSecularScalar_eq_zero_at_parityBottom
#print axioms Zeta23.CCM.globalBottom_evenStrict_secular
#print axioms Zeta23.CCM.globalBottom_oddStrict_secular
#print axioms Zeta23.CCM.globalBottom_tie_secular
