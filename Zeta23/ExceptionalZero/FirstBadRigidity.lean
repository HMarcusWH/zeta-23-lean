import Zeta23.CCM.ParityNormalSpace
import Zeta23.ExceptionalZero.FirstBadParitySpectrum

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY exceptional-zero endpoint

A hypothetical off-critical-line zero now forces a first-bad fixed-parity
negative eigenmode with a nonzero component in the intrinsic one-dimensional
successor shell and an exact parity-specific KKT residual.

No negative-index theorem, shell invariance, Schur/Feshbach contradiction,
positivity theorem, finite-to-infinite theorem, or RH theorem is claimed.
-/

theorem exists_firstBadParity_shell_KKT_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ p : ReversalParity,
        ∃ Nprev : ℕ, 1 ≤ Nprev ∧
          ∃ lam : ℝ, lam < 0 ∧
            ∃ v : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
              v ≠ 0 ∧
              parityCompressedCanonical p L (Nprev + 1) v =
                (lam : ℂ) • v ∧
              (∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
                  0 ≤ Complex.re
                    (inner ℂ
                      ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x)) ∧
              (intrinsicParitySuccShell p Nprev).orthogonalProjectionOnto v ≠ 0 ∧
              Module.finrank ℂ (intrinsicParitySuccShell p Nprev) = 1 ∧
              ParityKKTResidual p L (Nprev + 1) lam v := by
  obtain ⟨L, hL, p, Nprev, hNprev, lam, hlam, v, hvne, hveig,
    hprev, hnotInherited, hshellAmbient⟩ :=
    exists_firstBadParity_negativeEigenmode_of_offLine_zero ρ₀ hoff
  have hshellProjection :=
    negative_eigenmode_intrinsicShell_projection_ne_zero
      p hL Nprev hprev hlam hvne hveig
  have hshellDim :=
    finrank_intrinsicParitySuccShell p Nprev hNprev
  have hkkt :=
    parityKKTResidual_of_eigenmode
      p L (Nprev + 1) lam v hveig
  exact ⟨L, hL, p, Nprev, hNprev, lam, hlam, v, hvne, hveig,
    hprev, hshellProjection, hshellDim, hkkt⟩

theorem exists_firstBadParity_shell_KKT_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ p : ReversalParity,
        ∃ Nprev : ℕ, 1 ≤ Nprev ∧
          ∃ lam : ℝ, lam < 0 ∧
            ∃ v : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
              v ≠ 0 ∧
              parityCompressedCanonical p L (Nprev + 1) v =
                (lam : ℂ) • v ∧
              (∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
                  0 ≤ Complex.re
                    (inner ℂ
                      ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x)) ∧
              (intrinsicParitySuccShell p Nprev).orthogonalProjectionOnto v ≠ 0 ∧
              Module.finrank ℂ (intrinsicParitySuccShell p Nprev) = 1 ∧
              ParityKKTResidual p L (Nprev + 1) lam v := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_firstBadParity_shell_KKT_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_firstBadParity_shell_KKT_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_firstBadParity_shell_KKT_of_exists_offLine_zero
