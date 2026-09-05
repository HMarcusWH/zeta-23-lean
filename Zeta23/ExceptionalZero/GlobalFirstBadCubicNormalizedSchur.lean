import Zeta23.CCM.CubicNormalizedSchur
import Zeta23.ExceptionalZero.GlobalFirstBadCubicShell

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E2 exceptional-zero endpoint

PR #115 packages a hypothetical off-critical-line zero into one global
first-bad finite problem carrying both predecessor parities nonnegative, a
negative compressed eigenmode, KKT, exact cubic factorization, nonzero
negative-mode shell coordinate, nonzero canonical cubic shell coordinate, and
the shifted predecessor reduction.

E2 canonically normalizes the full negative eigenvector so that its shell
component is exactly `intrinsicCubicShellPart`. This file composes that theorem
back into the same global-first-bad state. The endpoint deliberately uses the
canonical shifted predecessor resolvent for both the original shell Schur
identity and the cubic-normalized Schur identity.

RH remains open.
-/

/-- A hypothetical off-line zero forces one global-first-bad finite problem
where the canonical shifted predecessor resolvent simultaneously resolves the
actual negative-mode shell component and satisfies the Schur identity on the
canonical cubic shell line. -/
theorem exists_globalFirstBad_cubicNormalizedSchur_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ Nprev : ℕ, 1 ≤ Nprev ∧
        ∃ p : ReversalParity,
          ∃ lam : ℝ, lam < 0 ∧
            ∃ v : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
              v ≠ 0 ∧
              parityCompressedCanonical p L (Nprev + 1) v =
                (lam : ℂ) • v ∧
              AnyParityBad L (Nprev + 1) ∧
              (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
              (∀ q : ReversalParity,
                ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                  x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
                    0 ≤ Complex.re
                      (inner ℂ
                        ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x)) ∧
              Module.finrank ℂ (intrinsicParitySuccShell p Nprev) = 1 ∧
              ParityKKTResidual p L (Nprev + 1) lam v ∧
              oddCubicCompressionVector (Nprev + 1) ≠ 0 ∧
              (∀ z : euclideanEvenBoundaryFlatSubspace (Nprev + 1),
                evenOddCompressedIntertwiningDefect L (Nprev + 1) z =
                  cubicDefectFunctional L (Nprev + 1) z •
                    oddCubicCompressionVector (Nprev + 1)) ∧
              intrinsicShellPart p Nprev v ≠ 0 ∧
              intrinsicCubicShellPart p Nprev ≠ 0 ∧
              Function.Bijective
                (shiftedIntrinsicPredecessorBlock p L Nprev lam) ∧
              ∃ R : intrinsicParityPredecessorSubspace p Nprev →ₗ[ℂ]
                    intrinsicParityPredecessorSubspace p Nprev,
                (∀ w : intrinsicParityPredecessorSubspace p Nprev,
                  R (shiftedIntrinsicPredecessorBlock p L Nprev lam w) = w) ∧
                intrinsicPredecessorPart p Nprev v =
                  - R
                    (intrinsicShellToPredecessor p L Nprev
                      (intrinsicShellPart p Nprev v)) ∧
                (let s := intrinsicShellPart p Nprev v
                 let b := intrinsicShellToPredecessor p L Nprev s
                 inner ℂ
                     (parityCompressedCanonical p L (Nprev + 1)
                       (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                     (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   (lam : ℂ) *
                     inner ℂ
                       (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                       (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   inner ℂ
                     ((R b : intrinsicParityPredecessorSubspace p Nprev) :
                       euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                     (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) ∧
                (let c := intrinsicCubicShellPart p Nprev
                 let b := intrinsicShellToPredecessor p L Nprev c
                 inner ℂ
                     (parityCompressedCanonical p L (Nprev + 1)
                       (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                     (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   (lam : ℂ) *
                     inner ℂ
                       (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                       (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   inner ℂ
                     ((R b : intrinsicParityPredecessorSubspace p Nprev) :
                       euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                     (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, v, hvne, hveig,
    hglobal, hmin, hprevBoth, hshellDim, hkkt, hcubicNe, hcubicFactor,
    hshellNe, hcubicShellNe, hbij, _Rold, _hRoldLeft, _hresOld, _hschurOld⟩ :=
    exists_globalFirstBad_cubicShell_shiftedSchur_of_offLine_zero ρ₀ hoff
  have hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x) :=
    hprevBoth p
  let E := shiftedIntrinsicPredecessorEquiv p hL Nprev hprev lam hlam
  let R : intrinsicParityPredecessorSubspace p Nprev →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p Nprev :=
    shiftedIntrinsicPredecessorResolvent p hL Nprev hprev lam hlam
  have hRleft :
      ∀ w : intrinsicParityPredecessorSubspace p Nprev,
        R (shiftedIntrinsicPredecessorBlock p L Nprev lam w) = w := by
    intro w
    change E.symm (E w) = w
    exact E.symm_apply_apply w
  have hresR :
      intrinsicPredecessorPart p Nprev v =
        - R
          (intrinsicShellToPredecessor p L Nprev
            (intrinsicShellPart p Nprev v)) := by
    simpa [R] using
      eigenmode_predecessorPart_eq_neg_resolvent_shell
        p hL Nprev hprev hlam hveig
  have hschurR :
      (let s := intrinsicShellPart p Nprev v
       let b := intrinsicShellToPredecessor p L Nprev s
       inner ℂ
           (parityCompressedCanonical p L (Nprev + 1)
             (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
           (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
         (lam : ℂ) *
           inner ℂ
             (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
             (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
         inner ℂ
           ((R b : intrinsicParityPredecessorSubspace p Nprev) :
             euclideanParityBoundaryFlatSubspace p (Nprev + 1))
           (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
    simpa [R] using
      eigenmode_shiftedSchur_identity p hL Nprev hprev hlam hveig
  have hcubicSchurR :
      (let c := intrinsicCubicShellPart p Nprev
       let b := intrinsicShellToPredecessor p L Nprev c
       inner ℂ
           (parityCompressedCanonical p L (Nprev + 1)
             (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
           (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
         (lam : ℂ) *
           inner ℂ
             (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
             (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
         inner ℂ
           ((R b : intrinsicParityPredecessorSubspace p Nprev) :
             euclideanParityBoundaryFlatSubspace p (Nprev + 1))
           (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
    simpa [R] using
      eigenmode_cubicNormalized_shiftedSchur_identity
        p hL Nprev hNprev hprev hlam hvne hveig
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, v, hvne, hveig,
    hglobal, hmin, hprevBoth, hshellDim, hkkt, hcubicNe, hcubicFactor,
    hshellNe, hcubicShellNe, hbij, R, hRleft, hresR, hschurR,
    hcubicSchurR⟩

/-- Existential off-line-zero wrapper for the E2 canonical cubic Schur
endpoint. -/
theorem exists_globalFirstBad_cubicNormalizedSchur_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ Nprev : ℕ, 1 ≤ Nprev ∧
        ∃ p : ReversalParity,
          ∃ lam : ℝ, lam < 0 ∧
            ∃ v : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
              v ≠ 0 ∧
              parityCompressedCanonical p L (Nprev + 1) v =
                (lam : ℂ) • v ∧
              AnyParityBad L (Nprev + 1) ∧
              (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
              (∀ q : ReversalParity,
                ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                  x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
                    0 ≤ Complex.re
                      (inner ℂ
                        ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x)) ∧
              Module.finrank ℂ (intrinsicParitySuccShell p Nprev) = 1 ∧
              ParityKKTResidual p L (Nprev + 1) lam v ∧
              oddCubicCompressionVector (Nprev + 1) ≠ 0 ∧
              (∀ z : euclideanEvenBoundaryFlatSubspace (Nprev + 1),
                evenOddCompressedIntertwiningDefect L (Nprev + 1) z =
                  cubicDefectFunctional L (Nprev + 1) z •
                    oddCubicCompressionVector (Nprev + 1)) ∧
              intrinsicShellPart p Nprev v ≠ 0 ∧
              intrinsicCubicShellPart p Nprev ≠ 0 ∧
              Function.Bijective
                (shiftedIntrinsicPredecessorBlock p L Nprev lam) ∧
              ∃ R : intrinsicParityPredecessorSubspace p Nprev →ₗ[ℂ]
                    intrinsicParityPredecessorSubspace p Nprev,
                (∀ w : intrinsicParityPredecessorSubspace p Nprev,
                  R (shiftedIntrinsicPredecessorBlock p L Nprev lam w) = w) ∧
                intrinsicPredecessorPart p Nprev v =
                  - R
                    (intrinsicShellToPredecessor p L Nprev
                      (intrinsicShellPart p Nprev v)) ∧
                (let s := intrinsicShellPart p Nprev v
                 let b := intrinsicShellToPredecessor p L Nprev s
                 inner ℂ
                     (parityCompressedCanonical p L (Nprev + 1)
                       (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                     (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   (lam : ℂ) *
                     inner ℂ
                       (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                       (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   inner ℂ
                     ((R b : intrinsicParityPredecessorSubspace p Nprev) :
                       euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                     (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) ∧
                (let c := intrinsicCubicShellPart p Nprev
                 let b := intrinsicShellToPredecessor p L Nprev c
                 inner ℂ
                     (parityCompressedCanonical p L (Nprev + 1)
                       (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                     (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   (lam : ℂ) *
                     inner ℂ
                       (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                       (c : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                   inner ℂ
                     ((R b : intrinsicParityPredecessorSubspace p Nprev) :
                       euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                     (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_cubicNormalizedSchur_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicNormalizedSchur_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicNormalizedSchur_of_exists_offLine_zero
