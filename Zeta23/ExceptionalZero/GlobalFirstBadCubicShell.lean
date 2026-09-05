import Zeta23.CCM.CubicShellIncidence
import Zeta23.ExceptionalZero.GlobalFirstBadShiftedSchur

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E1 exceptional-zero endpoint

PR #113 packages a hypothetical off-critical-line zero into one globally
first-bad finite problem carrying both predecessor parities nonnegative, a
negative compressed eigenmode, exact KKT and cubic factorization data, a
nonzero canonical one-dimensional shell coordinate, the safe shifted inverse,
predecessor reconstruction, and the scalar shifted Schur identity.

E1 proves that the parity-uniform cubic channel itself has a nonzero canonical
coordinate in that same intrinsic one-step shell.  This file composes those
facts without claiming that the cubic vector is pure shell or that the cubic
defect functional is nonzero.

RH remains open.
-/

/-- A hypothetical off-line zero forces a globally first-bad finite problem in
which both the negative eigenmode and the canonical parity-cubic channel have
nonzero coordinates in the same one-dimensional intrinsic successor shell.
All #113 shifted-Schur data remain available at that same finite problem. -/
theorem exists_globalFirstBad_cubicShell_shiftedSchur_of_offLine_zero
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
                     (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, v, hvne, hveig,
    hglobal, hmin, hprevBoth, hshellDim, hkkt, hcubicNe, hcubicFactor,
    hshellNe, hbij, R, hRleft, hresR, hschurR⟩ :=
    exists_globalFirstBad_shiftedSchur_cubicFactorization_of_offLine_zero
      ρ₀ hoff
  have hcubicShellNe : intrinsicCubicShellPart p Nprev ≠ 0 :=
    intrinsicCubicShellPart_ne_zero p Nprev hNprev
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, v, hvne, hveig,
    hglobal, hmin, hprevBoth, hshellDim, hkkt, hcubicNe, hcubicFactor,
    hshellNe, hcubicShellNe, hbij, R, hRleft, hresR, hschurR⟩

/-- Existential off-line-zero wrapper for the E1 cubic-shell endpoint. -/
theorem exists_globalFirstBad_cubicShell_shiftedSchur_of_exists_offLine_zero
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
                     (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_cubicShell_shiftedSchur_of_offLine_zero
    ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicShell_shiftedSchur_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicShell_shiftedSchur_of_exists_offLine_zero
