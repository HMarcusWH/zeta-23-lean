import Zeta23.ExceptionalZero.GeneratedFamilyFinalGate
import Zeta23.ExceptionalZero.BoundaryFlatFiniteWeil
import Zeta23.ExceptionalZero.TwoTranslateDeterminant
import Zeta23.CCM.RegularFirstBadRieszEnergy

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open Zeta23.CCM
open scoped ComplexConjugate

/-!
# Generated-family final-gate dumbassery firewall

PR #244 isolates the sufficient terminal gate
`NoArbitrarilyLargeWholeCellRetainedFamily`.

Before attempting to prove that gate by a generic large-aperture estimate, this
module checks its exact logical strength against Mathlib's
`RiemannHypothesis`.

The result is intentionally fail-closed: on the critical line every legal
diagonal Weil form is nonnegative, hence every canonical boundary-flat finite
quadratic form is nonnegative.  Therefore no retained negative-energy
certificate exists at all.  Combined with PR #244, the generated-family gate
is equivalent to RH.

Consequently a proof of the gate that uses only a renamed generic positivity
or prime-side upper-bound premise has not simplified RH; it has merely restated
it.  Any closing argument must supply genuinely new unconditional mathematics.
-/

/-- Reuse the theoremized critical-line reality of the centered spectral
coordinate. -/
theorem star_gammaOf_eq_gammaOf_of_re_eq_half
    (rho : zetaZeroConfig.carrier)
    (hrho : (rho : ℂ).re = 1 / 2) :
    star (Zeta23.gammaOf (rho : ℂ)) = Zeta23.gammaOf (rho : ℂ) :=
  gammaOf_star_eq_self_of_criticalLine rho hrho

/-- One diagonal Weil summand is nonnegative when its zero lies on the
critical line. -/
theorem zeta_Wsummand_self_re_nonnegative_of_re_eq_half
    (f : ℝ → ℂ)
    (rho : zetaZeroConfig.carrier)
    (hrho : (rho : ℂ).re = 1 / 2) :
    0 ≤ Complex.re (zetaZeroConfig.Wsummand f f rho) := by
  have hgamma :=
    star_gammaOf_eq_gammaOf_of_re_eq_half rho hrho
  unfold ZeroConfig.Wsummand
  rw [hgamma]
  let z : ℂ := Zeta23.paperFT f (Zeta23.gammaOf (rho : ℂ))
  change
    0 ≤ Complex.re
      (((zetaZeroConfig.mult (rho : ℂ) : ℕ) : ℂ) * z * star z)
  have hm : 0 ≤ (zetaZeroConfig.mult (rho : ℂ) : ℝ) :=
    Nat.cast_nonneg _
  simp [Complex.star_def, Complex.mul_re]
  nlinarith [hm, sq_nonneg z.re, sq_nonneg z.im]

/-- If every nontrivial zeta zero is on the critical line, every legal
diagonal zeta Weil form is nonnegative. -/
theorem zeta_W_self_re_nonnegative_of_criticalLine
    (hline : ∀ rho ∈ zetaZeroConfig.carrier, rho.re = 1 / 2)
    {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    0 ≤ Complex.re (zetaZeroConfig.W f f) := by
  have hsum :
      Summable (fun rho : zetaZeroConfig.carrier =>
        zetaZeroConfig.Wsummand f f rho) :=
    zeta_Wsummand_summable hf hf.continuous hfc hfc
  change
    0 ≤ Complex.re
      (∑' rho : zetaZeroConfig.carrier,
        zetaZeroConfig.Wsummand f f rho)
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg fun rho =>
    zeta_Wsummand_self_re_nonnegative_of_re_eq_half
      f rho (hline (rho : ℂ) rho.2)

/-- Critical-line positivity transported through the exact finite Weil/carrier
identity. -/
theorem canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine
    (hline : ∀ rho ∈ zetaZeroConfig.carrier, rho.re = 1 / 2)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hflat : BoundaryFlatCoefficients N u) :
    0 ≤ Complex.re (quadraticForm (canonicalSourceMatrix L N) u) := by
  let f : ℝ → ℂ := localizedFiniteVector L N u
  have hf : ContDiff ℝ 2 f := by
    simpa [f] using
      contDiff_localizedFiniteVector_of_boundaryFlat N u hL hflat
  have hfc : HasCompactSupport f := by
    simpa [f] using localizedFiniteVector_hasCompactSupport L N u
  have hW :=
    zeta_W_self_re_nonnegative_of_criticalLine hline hf hfc
  rw [zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
    N u hL hflat] at hW
  exact hW

/-- The complete canonical source-channel energy is nonnegative on every legal
boundary-flat Euclidean carrier if all zeta zeros are on the critical line. -/
theorem canonicalSourceChannelEnergy_nonnegative_of_criticalLine
    (hline : ∀ rho ∈ zetaZeroConfig.carrier, rho.re = 1 / 2)
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    0 ≤ canonicalSourceChannelEnergy L K x := by
  rw [← matrixRealEnergy_canonicalSourceMatrix_eq_channels hL K x]
  unfold matrixRealEnergy
  exact canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine
    hline K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)
      hL hflat

/-- Under critical-line positivity no retained regular negative-energy
certificate can exist. -/
theorem no_regularCellMinimalNegativeEnergyCertificate_of_criticalLine
    (hline : ∀ rho ∈ zetaZeroConfig.carrier, rho.re = 1 / 2)
    (Q : ℕ)
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    False := by
  have hnonneg :=
    canonicalSourceChannelEnergy_nonnegative_of_criticalLine
      hline c.firstBad.L_pos (c.firstBad.Nstar + 1)
      (cubicZeroShiftTrialVector
        c.firstBad.p c.firstBad.L c.firstBad.Nstar c.x₀ :
        EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1)))
      c.trial_boundaryFlat
  exact (not_lt_of_ge hnonneg) c.channelEnergyNeg

/-- The critical-line statement therefore implies the PR #244 generated-family
gate, in fact for the stronger reason that no retained certificate exists at
any aperture. -/
theorem noArbitrarilyLargeWholeCellRetainedFamily_of_criticalLine
    (hline : ∀ rho ∈ zetaZeroConfig.carrier, rho.re = 1 / 2) :
    NoArbitrarilyLargeWholeCellRetainedFamily := by
  refine ⟨0, ?_⟩
  intro Q c
  exact False.elim
    (no_regularCellMinimalNegativeEnergyCertificate_of_criticalLine
      hline Q c.retained.energy)

/-- Mathlib RH implies the generated-family final gate. -/
theorem noArbitrarilyLargeWholeCellRetainedFamily_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    NoArbitrarilyLargeWholeCellRetainedFamily := by
  apply noArbitrarilyLargeWholeCellRetainedFamily_of_criticalLine
  intro rho hrho
  exact RH_implies_on_line hRH (by simpa using hrho)

/-- **Dumbassery firewall.**  The PR #244 generated-family final gate is
logically equivalent to Mathlib's exact Riemann Hypothesis.

The forward direction is PR #244.  The reverse direction follows from exact
critical-line Weil positivity on the same finite canonical carrier.

This theorem is not a proof of RH.  It proves that a generic unconditional proof
of the aperture-bound gate must contain RH-strength information. -/
theorem noArbitrarilyLargeWholeCellRetainedFamily_iff_riemannHypothesis :
    NoArbitrarilyLargeWholeCellRetainedFamily ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_noArbitrarilyLargeWholeCellRetainedFamily,
    noArbitrarilyLargeWholeCellRetainedFamily_of_riemannHypothesis⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.zeta_W_self_re_nonnegative_of_criticalLine
#print axioms Zeta23.ExceptionalZero.canonicalSourceQuadraticForm_re_nonnegative_of_criticalLine
#print axioms Zeta23.ExceptionalZero.no_regularCellMinimalNegativeEnergyCertificate_of_criticalLine
#print axioms Zeta23.ExceptionalZero.noArbitrarilyLargeWholeCellRetainedFamily_of_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.noArbitrarilyLargeWholeCellRetainedFamily_iff_riemannHypothesis
