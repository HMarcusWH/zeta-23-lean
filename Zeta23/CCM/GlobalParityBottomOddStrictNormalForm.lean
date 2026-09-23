import Zeta23.CCM.GlobalParityBottomCrossParity
import Zeta23.CCM.CrossParitySecularRealTransfer

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — strict-odd global-bottom normal form

The forward transfer is asymmetric, so the odd-ground branch does not look like
the strict-even branch.  Nevertheless the existing one-coefficient collapse
already forces useful exact rigidity.

At the odd ground shift:
* F_odd = 0;
* F_even is nonzero;
* alpha * F_even + Gamma * S = 0;
* 6 Gamma + (2N-1) alpha = 2N+5.

From these equations alone Gamma cannot vanish.  Moreover alpha vanishes
exactly when the source moment vanishes, and in that subcase Gamma is forced by
the affine relation.  These are normal-form constraints, not a branch
exclusion.
-/

/-- Gamma cannot vanish in a strict-odd global-bottom state. -/
theorem globalBottom_oddStrict_gamma_ne_zero
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
      crossParitySecularGamma hL N (hprevBoth .odd)
          (parityRayleighBottom .odd L (N + 1)) hneg ≠ 0 := by
  obtain ⟨hneg, _hminus, hbalance, _hpos⟩ :=
    globalBottom_oddStrict_crossParity
      hL N hN hprevBoth hbad hstrict
  obtain ⟨hneg', hFne⟩ :=
    globalBottom_oddStrict_evenSecular_ne_zero
      hL N hN hprevBoth hbad hstrict
  have hproof : hneg' = hneg := Subsingleton.elim _ _
  subst hneg'
  let alpha :=
    crossParitySecularAlpha hL N (hprevBoth .odd)
      (parityRayleighBottom .odd L (N + 1)) hneg
  let Gamma :=
    crossParitySecularGamma hL N (hprevBoth .odd)
      (parityRayleighBottom .odd L (N + 1)) hneg
  let Fplus :=
    cubicSecularScalar .even hL N (hprevBoth .even)
      (parityRayleighBottom .odd L (N + 1)) hneg
  let S :=
    evenQuadraticSourceMoment L (N + 1)
      (cubicSecularTrialVector .even hL N (hprevBoth .even)
        (parityRayleighBottom .odd L (N + 1)) hneg)
  have hbal : alpha * Fplus + Gamma * S = 0 := by
    simpa [alpha, Gamma, Fplus, S] using hbalance
  have hF : Fplus ≠ 0 := by
    simpa [Fplus] using hFne
  intro hGammaRaw
  have hGamma : Gamma = 0 := by
    simpa [Gamma] using hGammaRaw
  rw [hGamma, zero_mul, add_zero] at hbal
  have hAlpha : alpha = 0 :=
    (mul_eq_zero.mp hbal).resolve_right hF
  have hlin :=
    six_mul_crossParitySecularGamma_add_index_mul_alpha
      hL N hN (hprevBoth .odd)
      (parityRayleighBottom .odd L (N + 1)) hneg
  change (6 : ℂ) * Gamma + (2 * (N : ℂ) - 1) * alpha =
      2 * (N : ℂ) + 5 at hlin
  rw [hGamma, hAlpha] at hlin
  have hre := congrArg Complex.re hlin
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  norm_num at hre
  linarith

/-- In the strict-odd branch, alpha vanishes exactly when the even source
moment vanishes. -/
theorem globalBottom_oddStrict_alpha_eq_zero_iff_source_eq_zero
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
      let alpha :=
        crossParitySecularAlpha hL N (hprevBoth .odd)
          (parityRayleighBottom .odd L (N + 1)) hneg
      let S :=
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even)
            (parityRayleighBottom .odd L (N + 1)) hneg)
      alpha = 0 ↔ S = 0 := by
  obtain ⟨hneg, _hminus, hbalance, _hpos⟩ :=
    globalBottom_oddStrict_crossParity
      hL N hN hprevBoth hbad hstrict
  obtain ⟨hnegGamma, hGammaNe⟩ :=
    globalBottom_oddStrict_gamma_ne_zero
      hL N hN hprevBoth hbad hstrict
  obtain ⟨hnegF, hFne⟩ :=
    globalBottom_oddStrict_evenSecular_ne_zero
      hL N hN hprevBoth hbad hstrict
  have hg : hnegGamma = hneg := Subsingleton.elim _ _
  have hf : hnegF = hneg := Subsingleton.elim _ _
  subst hnegGamma
  subst hnegF
  dsimp
  constructor
  · intro hAlpha
    have hbal := hbalance
    rw [hAlpha, zero_mul, zero_add] at hbal
    exact (mul_eq_zero.mp hbal).resolve_left hGammaNe
  · intro hS
    have hbal := hbalance
    rw [hS, mul_zero, add_zero] at hbal
    exact (mul_eq_zero.mp hbal).resolve_right hFne

/-- If the strict-odd source moment vanishes, alpha is zero and Gamma obeys the
exact scalar equation 6*Gamma = 2N+5. -/
theorem globalBottom_oddStrict_gamma_equation_of_source_zero
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
      let S :=
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even)
            (parityRayleighBottom .odd L (N + 1)) hneg)
      S = 0 →
        (6 : ℂ) *
            crossParitySecularGamma hL N (hprevBoth .odd)
              (parityRayleighBottom .odd L (N + 1)) hneg =
          2 * (N : ℂ) + 5 := by
  obtain ⟨hneg, hiff⟩ :=
    globalBottom_oddStrict_alpha_eq_zero_iff_source_eq_zero
      hL N hN hprevBoth hbad hstrict
  refine ⟨hneg, ?_⟩
  dsimp
  intro hS
  have hAlpha :
      crossParitySecularAlpha hL N (hprevBoth .odd)
          (parityRayleighBottom .odd L (N + 1)) hneg = 0 :=
    hiff.mpr hS
  have hlin :=
    six_mul_crossParitySecularGamma_add_index_mul_alpha
      hL N hN (hprevBoth .odd)
      (parityRayleighBottom .odd L (N + 1)) hneg
  rw [hAlpha, mul_zero, add_zero] at hlin
  exact hlin

end Zeta23.CCM

#print axioms Zeta23.CCM.globalBottom_oddStrict_gamma_ne_zero
#print axioms Zeta23.CCM.globalBottom_oddStrict_alpha_eq_zero_iff_source_eq_zero
#print axioms Zeta23.CCM.globalBottom_oddStrict_gamma_equation_of_source_zero
