import Zeta23.ExceptionalZero.TwoTranslateRadiusCompleteness

noncomputable section

namespace Zeta23.ExceptionalZero

/-!
# X4.6 corollaries: tail negativity and a countable-bank critical-line criterion

The canonical radius sequence from X4.6 is eventually visible at every nontrivial zero.
This file records two direct consequences that were previously only derived in the research
handover:

* every hypothetical off-line zero forces negative determinant gaps for every sufficiently late
  detector in the explicit canonical sequence, with an aperture allowed to depend on the detector;
* universal nonnegativity over the explicit countable detector bank and nonnegative apertures is
  exactly equivalent to the repository's critical-line statement.

The second theorem is an RH-equivalent repackaging, not a weaker positivity target and not a
proof of RH. Countability compresses the detector architecture; it does not reduce the logical
strength of the required positivity statement.
-/

/-- Every hypothetical off-line zero contaminates the entire tail of the explicit countable
canonical detector bank: for every sufficiently late detector there is a nonnegative aperture at
which the complete two-translate determinant gap is strictly negative. -/
theorem eventually_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ a : ℝ, 0 ≤ a ∧
        twoTranslateDeterminantGap zetaZeroConfig
          (canonicalPoleKilledTest (canonicalRadiusSequence n)) (2 * a) < 0 := by
  obtain ⟨ρR, _hprov, hright⟩ :=
    exists_rightHalf_reflection_of_offLine ρ₀ hoff
  obtain ⟨N, hvis⟩ :=
    eventually_canonicalPoleKilledSequence_visible_at_zero ρR
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hk, hkc, heven, hreal⟩ :=
    canonicalPoleKilledTest_admissible (canonicalRadiusSequence n)
  have hnot :=
    not_subexponential_weilRelativeCorrelation_of_right_zero
      hk hkc hreal heven ρR hright (hvis n hn)
  obtain ⟨a, ha, hgt⟩ :=
    exists_nonneg_gt_of_not_subexponential
      hnot
      ‖zetaZeroConfig.W
        (canonicalPoleKilledTest (canonicalRadiusSequence n))
        (canonicalPoleKilledTest (canonicalRadiusSequence n))‖
  refine ⟨a, ha, ?_⟩
  exact twoTranslateDeterminantGap_neg_of_diagonal_norm_lt
    zetaZeroConfig (canonicalPoleKilledTest (canonicalRadiusSequence n)) (2 * a) hgt

/-- Universal nonnegativity for the explicit countable canonical detector bank, restricted to
nonnegative apertures. -/
def CanonicalRadiusSequenceDeterminantNonnegative : Prop :=
  ∀ n : ℕ, ∀ a : ℝ, 0 ≤ a →
    0 ≤ twoTranslateDeterminantGap zetaZeroConfig
      (canonicalPoleKilledTest (canonicalRadiusSequence n)) (2 * a)

/-- Countable-bank positivity excludes every off-line zero. -/
theorem criticalLine_of_canonicalRadiusSequenceDeterminantNonnegative
    (hdet : CanonicalRadiusSequenceDeterminantNonnegative) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  let ρ₀ : zetaZeroConfig.carrier := ⟨ρ, hρ⟩
  have hoff' : (ρ₀ : ℂ).re ≠ 1 / 2 := by
    simpa [ρ₀] using hoff
  obtain ⟨n, a, ha, hneg⟩ :=
    exists_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero ρ₀ hoff'
  exact (not_lt_of_ge (hdet n a ha)) hneg

/-- Critical-line placement implies nonnegativity for every detector in the explicit countable
canonical bank. -/
theorem canonicalRadiusSequenceDeterminantNonnegative_of_criticalLine
    (hRH : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) :
    CanonicalRadiusSequenceDeterminantNonnegative := by
  intro n a _ha
  obtain ⟨hk, hkc, heven, hreal⟩ :=
    canonicalPoleKilledTest_admissible (canonicalRadiusSequence n)
  exact
    universalRealEvenTwoTranslateDeterminantNonnegative_of_criticalLine hRH
      (canonicalPoleKilledTest (canonicalRadiusSequence n))
      hk hkc heven hreal a

/-- **Countable-bank X4.6 endpoint.** Universal determinant nonnegativity on one explicit
countable detector sequence, at all nonnegative apertures, is exactly equivalent to the
repository's critical-line statement.

This theorem is deliberately classified as RH-equivalent rather than as a weakening of RH. -/
theorem canonicalRadiusSequenceDeterminantNonnegative_iff_criticalLine :
    CanonicalRadiusSequenceDeterminantNonnegative ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 :=
  ⟨criticalLine_of_canonicalRadiusSequenceDeterminantNonnegative,
    canonicalRadiusSequenceDeterminantNonnegative_of_criticalLine⟩

#print axioms Zeta23.ExceptionalZero.eventually_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.criticalLine_of_canonicalRadiusSequenceDeterminantNonnegative
#print axioms Zeta23.ExceptionalZero.canonicalRadiusSequenceDeterminantNonnegative_of_criticalLine
#print axioms Zeta23.ExceptionalZero.canonicalRadiusSequenceDeterminantNonnegative_iff_criticalLine

end Zeta23.ExceptionalZero
