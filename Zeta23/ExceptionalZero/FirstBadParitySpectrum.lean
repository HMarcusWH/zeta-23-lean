import Zeta23.CCM.ConstrainedParitySpectrum
import Zeta23.ExceptionalZero.ParityFirstBadObstruction

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-SPECTRUM exceptional-zero endpoint

A hypothetical off-critical-line zero now forces a least bad fixed-parity
finite problem together with a genuine negative eigenmode of the compressed
canonical operator. The predecessor sector is nonnegative after exact
transport into the successor matrix, so that negative eigenmode cannot be an
inherited predecessor vector.

No uniqueness of the negative eigenline, Schur/Feshbach formula, KKT
equation, positivity theorem, or RH theorem is claimed here.
-/

theorem exists_firstBadParity_negativeEigenmode_of_offLine_zero
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
              (¬ ∃ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                x ∈ euclideanParityBoundaryFlatSubspace p Nprev ∧
                euclideanCenteredZeroExtend (Nat.le_succ Nprev) x =
                  (v : EuclideanSpace ℂ
                    (Fin (2 * (Nprev + 1) + 1)))) ∧
              Module.finrank ℂ (euclideanParitySuccShell p Nprev) = 1 := by
  obtain ⟨L, hL, p, Nprev, Nstar, hNprev, hstar, hbad,
    hmin, hprevRaw, hprevEuclid, htail, hshell⟩ :=
    exists_leastParityBad_oneDimShell_of_offLine_zero ρ₀ hoff
  subst Nstar
  obtain ⟨lam, hlam, v, hvne, hveig⟩ :=
    exists_negative_eigenmode_of_parityBad hbad
  have hnotInherited :=
    negative_eigenmode_not_centeredImage
      p hL Nprev hprevEuclid hlam hvne hveig
  exact ⟨L, hL, p, Nprev, hNprev, lam, hlam, v, hvne, hveig,
    hprevEuclid, hnotInherited, hshell⟩

theorem exists_firstBadParity_negativeEigenmode_of_exists_offLine_zero
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
              (¬ ∃ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                x ∈ euclideanParityBoundaryFlatSubspace p Nprev ∧
                euclideanCenteredZeroExtend (Nat.le_succ Nprev) x =
                  (v : EuclideanSpace ℂ
                    (Fin (2 * (Nprev + 1) + 1)))) ∧
              Module.finrank ℂ (euclideanParitySuccShell p Nprev) = 1 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_firstBadParity_negativeEigenmode_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_firstBadParity_negativeEigenmode_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_firstBadParity_negativeEigenmode_of_exists_offLine_zero
