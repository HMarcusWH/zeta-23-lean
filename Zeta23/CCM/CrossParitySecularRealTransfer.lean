import Zeta23.CCM.CubicSecularRealGeometry
import Zeta23.CCM.CrossParitySecularCorrectionCollapse

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Real safe cross-parity secular transfer

The canonical odd safe negative-shift trial is fixed by coordinate conjugation.
Its metric overlap with the canonical odd cubic generator is therefore real,
so the existing overlap formula forces the transfer coefficient Gamma to be
real.  The existing affine Alpha/Gamma relation then forces Alpha to be real.

No sign of Alpha or Gamma, branch exclusion, negative-root exclusion, or RH
claim is asserted.
-/

/-- The safe cross-parity Gamma coefficient is fixed by complex conjugation. -/
theorem star_crossParitySecularGamma_eq_self
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star (crossParitySecularGamma hL N hprevOdd lam hlam) =
      crossParitySecularGamma hL N hprevOdd lam hlam := by
  let u := cubicSecularTrialVector .odd hL N hprevOdd lam hlam
  let g : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    successorParityCubicVector .odd N
  let c : euclideanParityBoundaryFlatSubspace .odd (N + 1) :=
    intrinsicCubicShellPart .odd N
  have hu :
      parityConj .odd (N + 1) u = u := by
    simpa [u] using
      cubicSecularTrialVector_conj_fixed
        .odd hL N hprevOdd lam hlam
  have hg :
      parityConj .odd (N + 1) g = g := by
    simpa [g] using successorParityCubicVector_conj_fixed .odd N
  have hnum :=
    inner_parityConj .odd (N + 1) u g
  rw [hu, hg] at hnum
  have hnumStar :
      star (inner ℂ u g) = inner ℂ u g := hnum.symm
  have hdenStar :
      star (inner ℂ c c) = inner ℂ c c := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [crossParitySecularGamma_eq_trial_cubic_overlap_div
    hL N hN hprevOdd lam hlam]
  rw [star_div₀, hnumStar, hdenStar]

/-- The safe cross-parity Gamma coefficient has zero imaginary part. -/
theorem crossParitySecularGamma_im_eq_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    (crossParitySecularGamma hL N hprevOdd lam hlam).im = 0 := by
  have hstar :=
    star_crossParitySecularGamma_eq_self
      hL N hN hprevOdd lam hlam
  have him := congrArg Complex.im hstar
  have hneg :
      -(crossParitySecularGamma hL N hprevOdd lam hlam).im =
        (crossParitySecularGamma hL N hprevOdd lam hlam).im := by
    simpa using him
  linarith

/-- The safe cross-parity Alpha coefficient is fixed by complex conjugation. -/
theorem star_crossParitySecularAlpha_eq_self
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    star (crossParitySecularAlpha hL N hprevOdd lam hlam) =
      crossParitySecularAlpha hL N hprevOdd lam hlam := by
  let coeff : ℂ := 2 * (N : ℂ) - 1
  let rhs : ℂ :=
    2 * (N : ℂ) + 5 -
      6 * crossParitySecularGamma hL N hprevOdd lam hlam
  have hcoeff : coeff ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    simp [coeff] at hre
    linarith
  have hlin :=
    six_mul_crossParitySecularGamma_add_index_mul_alpha
      hL N hN hprevOdd lam hlam
  have halphaMul :
      coeff * crossParitySecularAlpha hL N hprevOdd lam hlam = rhs := by
    dsimp [coeff, rhs]
    linear_combination hlin
  have halpha :
      crossParitySecularAlpha hL N hprevOdd lam hlam = rhs / coeff := by
    apply (eq_div_iff hcoeff).2
    rw [mul_comm]
    exact halphaMul
  rw [halpha, star_div₀]
  have hgamma :=
    star_crossParitySecularGamma_eq_self
      hL N hN hprevOdd lam hlam
  simp [rhs, coeff, hgamma]

/-- The safe cross-parity Alpha coefficient has zero imaginary part. -/
theorem crossParitySecularAlpha_im_eq_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    (crossParitySecularAlpha hL N hprevOdd lam hlam).im = 0 := by
  have hstar :=
    star_crossParitySecularAlpha_eq_self
      hL N hN hprevOdd lam hlam
  have him := congrArg Complex.im hstar
  have hneg :
      -(crossParitySecularAlpha hL N hprevOdd lam hlam).im =
        (crossParitySecularAlpha hL N hprevOdd lam hlam).im := by
    simpa using him
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.star_crossParitySecularGamma_eq_self
#print axioms Zeta23.CCM.crossParitySecularGamma_im_eq_zero
#print axioms Zeta23.CCM.star_crossParitySecularAlpha_eq_self
#print axioms Zeta23.CCM.crossParitySecularAlpha_im_eq_zero
