import Zeta23.CCM.GlobalParityBottomSecular
import Zeta23.CCM.CrossParitySecularTransfer
import Zeta23.CCM.CrossParitySecularCorrectionCollapse

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — global-bottom cross-parity normal forms

The global-bottom secular trichotomy is now composed with the already-proved
exact cross-parity transfer

  F_odd = alpha * F_even + Gamma * S

and the exact one-coefficient correction collapse.

Nothing is divided by Gamma, alpha, or the source moment.  In particular the
tied-bottom branch is retained as the exact factor equation Gamma*S = 0 rather
than silently discarding either factor.
-/

/-- Strict-even ground branch: the opposite secular scalar is exactly
Gamma times the canonical source moment, and its shell-scaled orientation is
strictly positive because the odd ground energy is strictly higher. -/
theorem globalBottom_evenStrict_crossParity
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
      let lam := parityRayleighBottom .even L (N + 1)
      let Fplus :=
        cubicSecularScalar .even hL N (hprevBoth .even) lam hneg
      let Fminus :=
        cubicSecularScalar .odd hL N (hprevBoth .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma hL N (hprevBoth .odd) lam hneg
      let S :=
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even) lam hneg)
      Fplus = 0 ∧
      Fminus = Gamma * S ∧
      0 <
        Complex.re
          (star Fminus *
            inner ℂ
              (intrinsicCubicShellPart .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))
              (intrinsicCubicShellPart .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
  obtain ⟨hneg, hroot, hpos⟩ :=
    globalBottom_evenStrict_secular
      hL N hN hprevBoth hbad hstrict
  refine ⟨hneg, ?_⟩
  dsimp
  have htransfer :=
    cubicSecularScalar_crossParity_source_transfer
      hL N hN (hprevBoth .even) (hprevBoth .odd)
      (parityRayleighBottom .even L (N + 1)) hneg
  rw [hroot] at htransfer
  simp only [mul_zero, zero_add] at htransfer
  exact ⟨hroot, htransfer, hpos⟩

/-- Strict-odd ground branch: the odd secular scalar vanishes, the even scalar
has strictly positive shell orientation, and the transfer leaves the exact
one-coefficient balance alpha*F_even + Gamma*S = 0. -/
theorem globalBottom_oddStrict_crossParity
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
      let lam := parityRayleighBottom .odd L (N + 1)
      let Fplus :=
        cubicSecularScalar .even hL N (hprevBoth .even) lam hneg
      let Fminus :=
        cubicSecularScalar .odd hL N (hprevBoth .odd) lam hneg
      let alpha :=
        crossParitySecularAlpha hL N (hprevBoth .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma hL N (hprevBoth .odd) lam hneg
      let S :=
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even) lam hneg)
      Fminus = 0 ∧
      alpha * Fplus + Gamma * S = 0 ∧
      0 <
        Complex.re
          (star Fplus *
            inner ℂ
              (intrinsicCubicShellPart .even N :
                euclideanParityBoundaryFlatSubspace .even (N + 1))
              (intrinsicCubicShellPart .even N :
                euclideanParityBoundaryFlatSubspace .even (N + 1))) := by
  obtain ⟨hneg, hroot, hpos⟩ :=
    globalBottom_oddStrict_secular
      hL N hN hprevBoth hbad hstrict
  refine ⟨hneg, ?_⟩
  dsimp
  have htransfer :=
    cubicSecularScalar_crossParity_source_transfer
      hL N hN (hprevBoth .even) (hprevBoth .odd)
      (parityRayleighBottom .odd L (N + 1)) hneg
  rw [hroot] at htransfer
  exact ⟨hroot, htransfer.symm, hpos⟩

/-- Tied ground branch: both secular scalars vanish at the same negative shift,
so the cross-parity transfer collapses to the exact factor equation Gamma*S=0.
No factor is cancelled. -/
theorem globalBottom_tie_crossParity
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
      let Fplus :=
        cubicSecularScalar .even hL N (hprevBoth .even) lam hneg
      let Fminus :=
        cubicSecularScalar .odd hL N (hprevBoth .odd) lam hneg
      let Gamma :=
        crossParitySecularGamma hL N (hprevBoth .odd) lam hneg
      let S :=
        evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even) lam hneg)
      Fplus = 0 ∧ Fminus = 0 ∧ Gamma * S = 0 := by
  obtain ⟨hneg, hplus, hminus⟩ :=
    globalBottom_tie_secular
      hL N hN hprevBoth hbad htie
  refine ⟨hneg, ?_⟩
  dsimp
  have htransfer :=
    cubicSecularScalar_crossParity_source_transfer
      hL N hN (hprevBoth .even) (hprevBoth .odd)
      (parityRayleighBottom .even L (N + 1)) hneg
  rw [hplus, hminus] at htransfer
  simp only [mul_zero, zero_add] at htransfer
  exact ⟨hplus, hminus, htransfer.symm⟩

/-- Tied-bottom factor split.  This is deliberately the factor-preserving
endpoint: either the safe cross-parity Gamma coefficient vanishes or the actual
canonical source moment vanishes. -/
theorem globalBottom_tie_gamma_or_source_zero
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
      crossParitySecularGamma hL N (hprevBoth .odd)
          (parityRayleighBottom .even L (N + 1)) hneg = 0 ∨
      evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even)
            (parityRayleighBottom .even L (N + 1)) hneg) = 0 := by
  obtain ⟨hneg, _hplus, _hminus, hprod⟩ :=
    globalBottom_tie_crossParity
      hL N hN hprevBoth hbad htie
  exact ⟨hneg, mul_eq_zero.mp hprod⟩

/-- If the tied branch lands on Gamma=0, the one-coefficient collapse fixes
alpha exactly.  This records the branch without introducing a division premise. -/
theorem globalBottom_tie_alpha_equation_of_gamma_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    (hGamma :
      crossParitySecularGamma hL N (hprevBoth .odd) lam hlam = 0) :
    (2 * (N : ℂ) - 1) *
        crossParitySecularAlpha hL N (hprevBoth .odd) lam hlam =
      2 * (N : ℂ) + 5 := by
  have h :=
    six_mul_crossParitySecularGamma_add_index_mul_alpha
      hL N hN (hprevBoth .odd) lam hlam
  rw [hGamma, mul_zero, zero_add] at h
  exact h


/-- Strict-even ground separation forces both factors in the transferred
source term to be nonzero.  This is the first branch where global-bottom
selection removes the historical need for successor goodness at zero merely
to obtain source/Gamma nonvanishing. -/
theorem globalBottom_evenStrict_gamma_source_ne_zero
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
      crossParitySecularGamma hL N (hprevBoth .odd)
          (parityRayleighBottom .even L (N + 1)) hneg ≠ 0 ∧
      evenQuadraticSourceMoment L (N + 1)
          (cubicSecularTrialVector .even hL N (hprevBoth .even)
            (parityRayleighBottom .even L (N + 1)) hneg) ≠ 0 := by
  obtain ⟨hneg, hplus, htransfer, hpos⟩ :=
    globalBottom_evenStrict_crossParity
      hL N hN hprevBoth hbad hstrict
  let Fminus :=
    cubicSecularScalar .odd hL N (hprevBoth .odd)
      (parityRayleighBottom .even L (N + 1)) hneg
  let Gamma :=
    crossParitySecularGamma hL N (hprevBoth .odd)
      (parityRayleighBottom .even L (N + 1)) hneg
  let S :=
    evenQuadraticSourceMoment L (N + 1)
      (cubicSecularTrialVector .even hL N (hprevBoth .even)
        (parityRayleighBottom .even L (N + 1)) hneg)
  have hFne : Fminus ≠ 0 := by
    intro hzero
    have hp := hpos
    change
      0 <
        Complex.re
          (star Fminus *
            inner ℂ
              (intrinsicCubicShellPart .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))
              (intrinsicCubicShellPart .odd N :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) at hp
    rw [hzero] at hp
    simp at hp
  have hGS : Fminus = Gamma * S := by
    simpa [Fminus, Gamma, S] using htransfer
  have hGamma : Gamma ≠ 0 := by
    intro hzero
    apply hFne
    rw [hGS, hzero]
    simp
  have hS : S ≠ 0 := by
    intro hzero
    apply hFne
    rw [hGS, hzero]
    simp
  exact ⟨hneg, by simpa [Gamma] using hGamma, by simpa [S] using hS⟩

/-- In the strict-odd branch the even secular scalar at the odd ground shift
is necessarily nonzero. -/
theorem globalBottom_oddStrict_evenSecular_ne_zero
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
      cubicSecularScalar .even hL N (hprevBoth .even)
          (parityRayleighBottom .odd L (N + 1)) hneg ≠ 0 := by
  obtain ⟨hneg, _hminus, _hbalance, hpos⟩ :=
    globalBottom_oddStrict_crossParity
      hL N hN hprevBoth hbad hstrict
  refine ⟨hneg, ?_⟩
  intro hzero
  rw [hzero] at hpos
  simp at hpos

end Zeta23.CCM

#print axioms Zeta23.CCM.globalBottom_evenStrict_crossParity
#print axioms Zeta23.CCM.globalBottom_oddStrict_crossParity
#print axioms Zeta23.CCM.globalBottom_tie_crossParity
#print axioms Zeta23.CCM.globalBottom_tie_gamma_or_source_zero
#print axioms Zeta23.CCM.globalBottom_tie_alpha_equation_of_gamma_zero
#print axioms Zeta23.CCM.globalBottom_evenStrict_gamma_source_ne_zero
#print axioms Zeta23.CCM.globalBottom_oddStrict_evenSecular_ne_zero
