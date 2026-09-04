import Zeta23.CCM.FirstBadShiftedSchur
import Zeta23.CCM.ParityCubicFactorization
import Zeta23.ExceptionalZero.GlobalFirstBadRigidity

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-D2 exceptional-zero endpoint

PR #112 produced a globally first-bad negative parity eigenmode with both
predecessor parity sectors nonnegative, a one-dimensional intrinsic shell, KKT,
and the exact cubic parity-defect factorization.  The D2 CCM layer now resolves
all predecessor coordinates through the safe inverse of `A - lam I` and derives
a basis-free scalar shifted Schur identity.

This endpoint packages those facts at the same finite problem.  The inverse is
stated existentially as a concrete linear map `R`, so the theorem surface does
not depend on proof terms witnessing positivity/nonnegativity.

No shell invariance, exact nonzero rank-one defect, unitary D, resonance
exclusion, positivity theorem, finite-to-infinite theorem, or RH theorem is
claimed.
-/

/-- A hypothetical off-line zero forces a globally first-bad finite problem in
which the negative eigenmode has a nonzero canonical one-dimensional shell
coordinate, the shifted predecessor block is bijective, all predecessor
coordinates are resolved by a shifted inverse, and the resulting scalar Schur
identity holds.  The exact cubic parity-defect channel from #112 is available
at the same size. -/
theorem exists_globalFirstBad_shiftedSchur_cubicFactorization_of_offLine_zero
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
    hglobal, hmin, hprevBoth, _hshell, hshellDim, hkkt,
    hcubicNe, hcubicFactor⟩ :=
    exists_globalFirstBad_intrinsicShell_cubicFactorization_of_offLine_zero
      ρ₀ hoff
  have hprev := hprevBoth p
  obtain ⟨hsne, hbij, hres, hschur⟩ :=
    negative_eigenmode_shiftedSchur_package
      p hL Nprev hprev hlam hvne hveig
  let E := shiftedIntrinsicPredecessorEquiv p hL Nprev hprev lam hlam
  let R : intrinsicParityPredecessorSubspace p Nprev →ₗ[ℂ]
      intrinsicParityPredecessorSubspace p Nprev := E.symm.toLinearMap
  have hRleft :
      ∀ w : intrinsicParityPredecessorSubspace p Nprev,
        R (shiftedIntrinsicPredecessorBlock p L Nprev lam w) = w := by
    intro w
    have hEapply :
        E w = shiftedIntrinsicPredecessorBlock p L Nprev lam w := by
      rfl
    change E.symm (shiftedIntrinsicPredecessorBlock p L Nprev lam w) = w
    rw [← hEapply]
    exact E.symm_apply_apply w
  have hresR :
      intrinsicPredecessorPart p Nprev v =
        - R
          (intrinsicShellToPredecessor p L Nprev
            (intrinsicShellPart p Nprev v)) := by
    simpa [R, E, shiftedIntrinsicPredecessorResolvent] using hres
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
    simpa [R, E, shiftedIntrinsicPredecessorResolvent] using hschur
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, v, hvne, hveig,
    hglobal, hmin, hprevBoth, hshellDim, hkkt, hcubicNe, hcubicFactor,
    hsne, hbij, R, hRleft, hresR, hschurR⟩

/-- Existential off-line-zero wrapper. -/
theorem exists_globalFirstBad_shiftedSchur_cubicFactorization_of_exists_offLine_zero
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
  exact exists_globalFirstBad_shiftedSchur_cubicFactorization_of_offLine_zero
    ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_shiftedSchur_cubicFactorization_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_shiftedSchur_cubicFactorization_of_exists_offLine_zero
