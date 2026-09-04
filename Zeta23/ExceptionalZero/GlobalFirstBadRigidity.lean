import Zeta23.CCM.FirstBadIntrinsicBlock
import Zeta23.CCM.ParityNormalSpace
import Zeta23.CCM.ParityCubicFactorization
import Zeta23.ExceptionalZero.ConstrainedFiniteObstruction

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-D1 exceptional-zero endpoint

A hypothetical off-critical-line zero now forces a least globally bad finite
size: at its predecessor *both* reversal parity sectors are nonnegative.  One
parity at the successor carries a genuine negative compressed eigenmode, and
that eigenmode decomposes natively as predecessor plus a nonzero vector in an
intrinsic one-dimensional shell.  At the same finite size the #110 parity
defect has the exact cubic functional factorization.

No shell invariance, Schur/Feshbach equation, resonance exclusion, positivity
theorem, finite-to-infinite theorem, or RH theorem is claimed.
-/

/-- Hypothetical off-line zero -> global first-bad intrinsic-shell endpoint,
with both predecessor parities nonnegative and the exact cubic defect channel
available at the same successor size. -/
theorem exists_globalFirstBad_intrinsicShell_cubicFactorization_of_offLine_zero
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
              (∃ w : intrinsicParityPredecessorSubspace p Nprev,
                ∃ s : intrinsicParitySuccShell p Nprev,
                  s ≠ 0 ∧
                  (w : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) +
                    (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = v) ∧
              Module.finrank ℂ (intrinsicParitySuccShell p Nprev) = 1 ∧
              ParityKKTResidual p L (Nprev + 1) lam v ∧
              oddCubicCompressionVector (Nprev + 1) ≠ 0 ∧
              (∀ z : euclideanEvenBoundaryFlatSubspace (Nprev + 1),
                evenOddCompressedIntertwiningDefect L (Nprev + 1) z =
                  cubicDefectFunctional L (Nprev + 1) z •
                    oddCubicCompressionVector (Nprev + 1)) := by
  obtain ⟨L, hL, N0, hN0, u, hune, hmem, hneg⟩ :=
    exists_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  have hglobal0 : AnyParityBad L N0 :=
    anyParityBad_of_negative hmem hneg
  obtain ⟨Nstar, hNstar2, hglobalStar, hmin⟩ :=
    exists_least_anyParityBad_two_le L ⟨N0, hglobal0⟩
  let Nprev := Nstar - 1
  have hNprev : 1 ≤ Nprev := by
    dsimp [Nprev]
    omega
  have hsucc : Nstar = Nprev + 1 := by
    dsimp [Nprev]
    omega
  have hprevlt : Nprev < Nstar := by
    rw [hsucc]
    omega
  have hprevBoth :
      ∀ q : ReversalParity,
        ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
          x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
            0 ≤ Complex.re
              (inner ℂ
                ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x) := by
    intro q x hx
    exact euclideanParity_nonnegative_of_lt_least_anyParityBad
      L hmin q hprevlt x hx
  have hglobalSucc : AnyParityBad L (Nprev + 1) := by
    rw [← hsucc]
    exact hglobalStar
  have hminSucc :
      ∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N := by
    intro N hN
    apply hmin N
    rw [hsucc]
    exact hN
  have hNsucc2 : 2 ≤ Nprev + 1 := by
    rw [← hsucc]
    exact hNstar2
  have hcubicNe : oddCubicCompressionVector (Nprev + 1) ≠ 0 :=
    oddCubicCompressionVector_ne_zero (Nprev + 1) hNsucc2
  have hcubicFactor :
      ∀ z : euclideanEvenBoundaryFlatSubspace (Nprev + 1),
        evenOddCompressedIntertwiningDefect L (Nprev + 1) z =
          cubicDefectFunctional L (Nprev + 1) z •
            oddCubicCompressionVector (Nprev + 1) := by
    intro z
    exact evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL (Nprev + 1) hNsucc2 z
  rcases hglobalSucc with heven | hodd
  · obtain ⟨lam, hlam, v, hvne, hveig⟩ :=
      exists_negative_eigenmode_of_parityBad heven
    have hshell :=
      negative_eigenmode_exists_intrinsic_shell_component
        .even hL Nprev (hprevBoth .even) hlam hvne hveig
    have hshellDim := finrank_intrinsicParitySuccShell .even Nprev hNprev
    have hkkt := parityKKTResidual_of_eigenmode
      .even L (Nprev + 1) lam v hveig
    exact ⟨L, hL, Nprev, hNprev, .even, lam, hlam, v, hvne,
      hveig, Or.inl heven, hminSucc, hprevBoth, hshell, hshellDim, hkkt,
      hcubicNe, hcubicFactor⟩
  · obtain ⟨lam, hlam, v, hvne, hveig⟩ :=
      exists_negative_eigenmode_of_parityBad hodd
    have hshell :=
      negative_eigenmode_exists_intrinsic_shell_component
        .odd hL Nprev (hprevBoth .odd) hlam hvne hveig
    have hshellDim := finrank_intrinsicParitySuccShell .odd Nprev hNprev
    have hkkt := parityKKTResidual_of_eigenmode
      .odd L (Nprev + 1) lam v hveig
    exact ⟨L, hL, Nprev, hNprev, .odd, lam, hlam, v, hvne,
      hveig, Or.inr hodd, hminSucc, hprevBoth, hshell, hshellDim, hkkt,
      hcubicNe, hcubicFactor⟩

/-- Existential off-line-zero wrapper. -/
theorem exists_globalFirstBad_intrinsicShell_cubicFactorization_of_exists_offLine_zero
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
              (∃ w : intrinsicParityPredecessorSubspace p Nprev,
                ∃ s : intrinsicParitySuccShell p Nprev,
                  s ≠ 0 ∧
                  (w : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) +
                    (s : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = v) ∧
              Module.finrank ℂ (intrinsicParitySuccShell p Nprev) = 1 ∧
              ParityKKTResidual p L (Nprev + 1) lam v ∧
              oddCubicCompressionVector (Nprev + 1) ≠ 0 ∧
              (∀ z : euclideanEvenBoundaryFlatSubspace (Nprev + 1),
                evenOddCompressedIntertwiningDefect L (Nprev + 1) z =
                  cubicDefectFunctional L (Nprev + 1) z •
                    oddCubicCompressionVector (Nprev + 1)) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_intrinsicShell_cubicFactorization_of_offLine_zero
    ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_intrinsicShell_cubicFactorization_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_intrinsicShell_cubicFactorization_of_exists_offLine_zero
