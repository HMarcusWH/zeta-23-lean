import Zeta23.CCM.GlobalParityBottomIntertwining

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — reverse ground-state parity transfer

The forward secular transfer is intentionally not treated as symmetric.  What
is available unconditionally is the exact algebraic inverse of the centered
index equivalence.  This module records the corresponding reverse statement at
the true odd ground level.

No claim is made that the parity equivalence is unitary.  The argument keeps
the even norm after pullback and uses only the exact rank-one defect plus the
strict even spectral gap.
-/

/-- Every nonzero odd ground eigenvector in a strict-odd branch pulls back to an
even vector with nonzero canonical source defect. -/
theorem oddGround_pulledBack_source_ne_zero_of_strict
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hstrict :
      parityRayleighBottom .odd L (N + 1) <
        parityRayleighBottom .even L (N + 1))
    (w : euclideanOddBoundaryFlatSubspace (N + 1))
    (hwne : w ≠ 0)
    (hweig :
      parityCompressedCanonical .odd L (N + 1) w =
        (parityRayleighBottom .odd L (N + 1) : ℂ) • w) :
    let E :=
      euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)
    let v := E.symm w
    evenQuadraticSourceMoment L (N + 1) v ≠ 0 := by
  let E :=
    euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)
  let v : euclideanEvenBoundaryFlatSubspace (N + 1) := E.symm w
  have hvne : v ≠ 0 := by
    intro hv
    apply hwne
    have hmap := congrArg E hv
    simpa [v, E] using hmap
  have hshift :=
    parityRayleighBottom_gap_mul_norm_sq_le_shifted
      .even L (N + 1)
      (parityRayleighBottom .odd L (N + 1)) v
  have hident :=
    oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic
      hL (N + 1) (by omega)
      (parityRayleighBottom .odd L (N + 1)) w hweig
  dsimp only at hident
  change
    parityCompressedCanonical .even L (N + 1) v -
        (parityRayleighBottom .odd L (N + 1) : ℂ) • v =
      -(evenQuadraticSourceMoment L (N + 1) v) •
        pulledBackCubicCompressionVector (N + 1) (by omega) at hident
  rw [hident] at hshift
  intro hsource
  rw [hsource] at hshift
  simp at hshift
  have hnorm : 0 < ‖v‖ ^ 2 := by
    positivity
  have hleft :
      0 <
        (parityRayleighBottom .even L (N + 1) -
            parityRayleighBottom .odd L (N + 1)) * ‖v‖ ^ 2 :=
    mul_pos (sub_pos.mpr hstrict) hnorm
  exact (not_lt_of_ge hshift) hleft

/-- Exact reverse ground-state transfer package. -/
theorem oddGround_reverse_rankOne_package
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hstrict :
      parityRayleighBottom .odd L (N + 1) <
        parityRayleighBottom .even L (N + 1))
    (w : euclideanOddBoundaryFlatSubspace (N + 1))
    (hwne : w ≠ 0)
    (hweig :
      parityCompressedCanonical .odd L (N + 1) w =
        (parityRayleighBottom .odd L (N + 1) : ℂ) • w) :
    let E :=
      euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)
    let v := E.symm w
    v ≠ 0 ∧
    evenQuadraticSourceMoment L (N + 1) v ≠ 0 ∧
    parityCompressedCanonical .even L (N + 1) v -
        (parityRayleighBottom .odd L (N + 1) : ℂ) • v =
      -(evenQuadraticSourceMoment L (N + 1) v) •
        pulledBackCubicCompressionVector (N + 1) (by omega) := by
  let E :=
    euclideanEvenOddBoundaryFlatLinearEquiv (N + 1) (by omega)
  let v : euclideanEvenBoundaryFlatSubspace (N + 1) := E.symm w
  have hvne : v ≠ 0 := by
    intro hv
    apply hwne
    have hmap := congrArg E hv
    simpa [v, E] using hmap
  have hsource :
      evenQuadraticSourceMoment L (N + 1) v ≠ 0 := by
    simpa [v, E] using
      oddGround_pulledBack_source_ne_zero_of_strict
        hL N hN hstrict w hwne hweig
  have hident :=
    oddEigenmode_pulledBack_shiftedEven_eq_neg_sourceCubic
      hL (N + 1) (by omega)
      (parityRayleighBottom .odd L (N + 1)) w hweig
  simpa [v, E] using And.intro hvne (And.intro hsource hident)

end Zeta23.CCM

#print axioms Zeta23.CCM.oddGround_pulledBack_source_ne_zero_of_strict
#print axioms Zeta23.CCM.oddGround_reverse_rankOne_package
