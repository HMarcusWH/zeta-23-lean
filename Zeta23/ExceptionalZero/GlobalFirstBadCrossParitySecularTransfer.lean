import Zeta23.CCM.CrossParitySecularTransfer
import Zeta23.ExceptionalZero.GlobalFirstBadZeroShiftBranchResponse

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A3c exceptional-zero endpoint

This module attaches the source-explicit cross-parity secular transfer to the
same global-first-bad finite state produced by the post-#128 obstruction
pipeline.

At the common negative shift, both predecessor parities are nonnegative.  The
exact transfer is therefore available whether the forced explicit secular root
has even or odd parity.

If the forced root is even, the odd secular scalar becomes the exact product of
the odd overlap coefficient and the canonical quadratic source moment.  If the
forced root is odd, no division is performed: the full source-explicit transfer
is retained as a zero identity.

Firewalls:
* D remains only algebraic; no unitary/isometric transport is used;
* the predecessor correction in D of the cubic shell is retained;
* no nonzeroness or sign is asserted for alpha, Gamma, the overlap, or the
  source moment;
* no branch exclusion, negative-root exclusion, positivity closure,
  finite-to-infinite closure, or RH theorem is claimed.
-/

/-- Exact cross-parity certificate at one already-selected first-bad explicit
root.  The first conjunct is the full source transfer.  The second records the
root in its actual parity without dividing by any unproved factor. -/
def crossParityFirstBadRootCertificate
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (p : ReversalParity)
    (lam : ℝ) (hlam : lam < 0) : Prop :=
  let hprevEven := hprevBoth .even
  let hprevOdd := hprevBoth .odd
  let Fplus := cubicSecularScalar .even hL N hprevEven lam hlam
  let Fminus := cubicSecularScalar .odd hL N hprevOdd lam hlam
  let alpha := crossParitySecularAlpha hL N hprevOdd lam hlam
  let gamma := crossParitySecularGamma hL N hprevOdd lam hlam
  let source := evenQuadraticSourceMoment L (N + 1)
    (cubicSecularTrialVector .even hL N hprevEven lam hlam)
  let overlap :=
    inner ℂ
        (cubicSecularTrialVector .odd hL N hprevOdd lam hlam)
        (successorParityCubicVector .odd N) /
      inner ℂ
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))
  Fminus = alpha * Fplus + gamma * source ∧
    ((p = .even ∧ Fplus = 0 ∧ Fminus = overlap * source) ∨
      (p = .odd ∧ Fminus = 0 ∧ alpha * Fplus + gamma * source = 0))

/-- The exact explicit Schur root at a first-bad state produces the complete
source-explicit parity certificate at the same `L`, `N`, and negative shift. -/
theorem crossParityFirstBadRootCertificate_of_explicit_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q N →
            0 ≤ Complex.re
              (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (p : ReversalParity)
    (lam : ℝ) (hlam : lam < 0)
    (hroot :
      cubicExplicitSchurScalar p hL N (hprevBoth p) lam hlam = 0) :
    crossParityFirstBadRootCertificate hL N hprevBoth p lam hlam := by
  unfold crossParityFirstBadRootCertificate
  dsimp
  have htransfer :=
    cubicSecularScalar_crossParity_source_transfer
      hL N hN (hprevBoth .even) (hprevBoth .odd) lam hlam
  refine ⟨htransfer, ?_⟩
  cases p with
  | even =>
      have hsec :
          cubicSecularScalar .even hL N (hprevBoth .even) lam hlam = 0 :=
        (cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
          .even hL N hN (hprevBoth .even) lam hlam).1 hroot
      refine Or.inl ⟨rfl, hsec, ?_⟩
      exact
        cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
          hL N hN (hprevBoth .even) (hprevBoth .odd) lam hlam hsec
  | odd =>
      have hsec :
          cubicSecularScalar .odd hL N (hprevBoth .odd) lam hlam = 0 :=
        (cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
          .odd hL N hN (hprevBoth .odd) lam hlam).1 hroot
      refine Or.inr ⟨rfl, hsec, ?_⟩
      exact htransfer.symm.trans hsec

/-- A hypothetical off-line zero forces a global-first-bad state carrying the
source-explicit cross-parity certificate at the same forced negative explicit
root. -/
theorem exists_globalFirstBad_crossParitySecularTransfer_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ lam : ℝ, ∃ hlam : lam < 0,
            ∃ hprevBoth :
              ∀ q : ReversalParity,
                ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                  x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
                    0 ≤ Complex.re
                      (inner ℂ
                        ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
              AnyParityBad L (Nprev + 1) ∧
              (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
              cubicExplicitSchurScalar p hL Nprev
                (hprevBoth p) lam hlam = 0 ∧
              crossParityFirstBadRootCertificate
                hL Nprev hprevBoth p lam hlam := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, hroot, _hbranch⟩ :=
    exists_globalFirstBad_zeroShiftBranchResponseDichotomy_of_offLine_zero
      ρ₀ hoff
  have hcert :=
    crossParityFirstBadRootCertificate_of_explicit_root
      hL Nprev hNprev hprevBoth p lam hlam hroot
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, hroot, hcert⟩

/-- Existential off-line-zero wrapper for the source-explicit cross-parity
first-bad certificate. -/
theorem exists_globalFirstBad_crossParitySecularTransfer_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ lam : ℝ, ∃ hlam : lam < 0,
            ∃ hprevBoth :
              ∀ q : ReversalParity,
                ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                  x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
                    0 ≤ Complex.re
                      (inner ℂ
                        ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
              AnyParityBad L (Nprev + 1) ∧
              (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
              cubicExplicitSchurScalar p hL Nprev
                (hprevBoth p) lam hlam = 0 ∧
              crossParityFirstBadRootCertificate
                hL Nprev hprevBoth p lam hlam := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_globalFirstBad_crossParitySecularTransfer_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.crossParityFirstBadRootCertificate_of_explicit_root
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_crossParitySecularTransfer_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_crossParitySecularTransfer_of_exists_offLine_zero
