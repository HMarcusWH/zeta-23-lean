import Zeta23.CCM.GlobalParityBottomCrossParity
import Zeta23.CCM.GlobalParityBottomIntertwining
import Zeta23.CCM.CubicSecularEquation

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — tied global-bottom saturation normal form

A tied parity bottom is not treated as contradictory.  The exact transfer gives
Gamma*S = 0, and each factor-zero branch is converted into a stronger equality
case:

* Gamma = 0 fixes alpha through the one-coefficient collapse;
* S = 0 makes the centered-index image of the normalized even ground trial an
  exact odd ground eigenmode at the same eigenvalue.

This is an equality/saturation normal form, not a branch exclusion.
-/

/-- Tie branch sharpened into the two exact saturation alternatives. -/
theorem globalBottom_tie_saturation
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
      let lam := parityRayleighBottom .even L (N + 1)
      let alpha :=
        crossParitySecularAlpha hL N (hprevBoth .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma hL N (hprevBoth .odd) lam hneg
      let u :=
        cubicSecularTrialVector .even hL N (hprevBoth .even) lam hneg
      let S := evenQuadraticSourceMoment L (N + 1) u
      (Gamma = 0 ∧
          (2 * (N : ℂ) - 1) * alpha = 2 * (N : ℂ) + 5) ∨
        (S = 0 ∧
          parityCompressedCanonical .odd L (N + 1)
              (euclideanEvenToOddIndexLinearMap (N + 1) u) =
            (lam : ℂ) •
              euclideanEvenToOddIndexLinearMap (N + 1) u) := by
  obtain ⟨hneg, hplus, _hminus⟩ :=
    globalBottom_tie_secular
      hL N hN hprevBoth hbad htie
  obtain ⟨hnegSplit, hsplit⟩ :=
    globalBottom_tie_gamma_or_source_zero
      hL N hN hprevBoth hbad htie
  have hsproof : hnegSplit = hneg := Subsingleton.elim _ _
  subst hnegSplit
  refine ⟨hneg, ?_⟩
  dsimp
  rcases hsplit with hGamma | hS
  · left
    refine ⟨hGamma, ?_⟩
    exact globalBottom_tie_alpha_equation_of_gamma_zero
      hL N hN hprevBoth hneg hGamma
  · right
    refine ⟨hS, ?_⟩
    have hveig :
        parityCompressedCanonical .even L (N + 1)
            (cubicSecularTrialVector .even hL N
              (hprevBoth .even)
              (parityRayleighBottom .even L (N + 1)) hneg) =
          (parityRayleighBottom .even L (N + 1) : ℂ) •
            cubicSecularTrialVector .even hL N
              (hprevBoth .even)
              (parityRayleighBottom .even L (N + 1)) hneg :=
      (cubicSecularScalar_eq_zero_iff_trial_eigenmode
        .even hL N hN (hprevBoth .even)
        (parityRayleighBottom .even L (N + 1)) hneg).mp hplus
    exact
      evenGround_maps_to_oddEigenmode_of_source_zero
        hL N hN
        (cubicSecularTrialVector .even hL N
          (hprevBoth .even)
          (parityRayleighBottom .even L (N + 1)) hneg)
        hveig hS

/-- In the tied source-zero branch, the transported even ground trial is
nonzero, so the equality above is a genuine second ground eigenmode. -/
theorem globalBottom_tie_sourceZero_gives_nonzero_oddGround
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (hroot :
      cubicSecularScalar .even hL N (hprevBoth .even) lam hlam = 0)
    (hS :
      evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N
            (hprevBoth .even) lam hlam) = 0) :
    let u :=
      cubicSecularTrialVector .even hL N
        (hprevBoth .even) lam hlam
    euclideanEvenToOddIndexLinearMap (N + 1) u ≠ 0 ∧
    parityCompressedCanonical .odd L (N + 1)
        (euclideanEvenToOddIndexLinearMap (N + 1) u) =
      (lam : ℂ) •
        euclideanEvenToOddIndexLinearMap (N + 1) u := by
  let u :=
    cubicSecularTrialVector .even hL N
      (hprevBoth .even) lam hlam
  have hune : u ≠ 0 :=
    cubicSecularTrialVector_ne_zero
      .even hL N hN (hprevBoth .even) lam hlam
  have hmapne :
      euclideanEvenToOddIndexLinearMap (N + 1) u ≠ 0 := by
    intro hDu
    apply hune
    apply euclideanEvenToOddIndexLinearMap_injective (N + 1)
    simpa [u] using hDu
  have hveig :
      parityCompressedCanonical .even L (N + 1) u =
        (lam : ℂ) • u :=
    (cubicSecularScalar_eq_zero_iff_trial_eigenmode
      .even hL N hN (hprevBoth .even) lam hlam).mp hroot
  have hodd :=
    evenEigenmode_shiftedOdd_eq_sourceCubic
      hL (N + 1) (by omega) lam u hveig
  rw [hS, zero_smul] at hodd
  refine ⟨hmapne, ?_⟩
  change
    oddCompressedCanonical L (N + 1)
        (euclideanEvenToOddIndexLinearMap (N + 1) u) =
      (lam : ℂ) • euclideanEvenToOddIndexLinearMap (N + 1) u
  exact sub_eq_zero.mp hodd

end Zeta23.CCM

#print axioms Zeta23.CCM.globalBottom_tie_saturation
#print axioms Zeta23.CCM.globalBottom_tie_sourceZero_gives_nonzero_oddGround
