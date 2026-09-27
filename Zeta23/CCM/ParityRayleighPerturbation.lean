import Mathlib.Algebra.Order.Group.MinMax
import Zeta23.CCM.GlobalParityBottomSpectrum

noncomputable section

namespace Zeta23.CCM

open Set

/-!
# Closure campaign A2: multiplicity-safe Rayleigh perturbation

This module avoids choosing a differentiable ground eigenvector.  A uniform
bound on the Rayleigh quotient perturbation controls the bottom directly.
Ground-state multiplicity is harmless because finite-dimensional attainment is
used only to test the opposite operator on one minimizing vector.
-/

/-- Rayleigh quotient of the exact canonical parity-compressed operator. -/
def parityRayleighQuotientAt
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  RCLike.re
      (inner ℂ
        (parityCompressedCanonical p L K x)
        x) /
    ‖x‖ ^ 2

/-- Uniform two-aperture perturbation bound on one parity carrier. -/
def ParityRayleighPerturbationBound
    (p : ReversalParity) (L₁ L₂ : ℝ) (K : ℕ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ x : euclideanParityBoundaryFlatSubspace p K, x ≠ 0 →
      |parityRayleighQuotientAt p L₁ K x -
        parityRayleighQuotientAt p L₂ K x| ≤ ε

private theorem parityRayleighQuotientAt_eq_bottom_of_eigen_succ
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p (N + 1))
    (hv : parityCompressedCanonical p L (N + 1) v =
      (parityRayleighBottom p L (N + 1) : ℂ) • v)
    (hv0 : v ≠ 0) :
    parityRayleighQuotientAt p L (N + 1) v =
      parityRayleighBottom p L (N + 1) := by
  unfold parityRayleighQuotientAt
  rw [hv]
  have hsmul :
      inner ℂ ((parityRayleighBottom p L (N + 1) : ℂ) • v) v =
        parityRayleighBottom p L (N + 1) • inner ℂ v v := by
    exact inner_smul_real_left (𝕜 := ℂ) v v
      (parityRayleighBottom p L (N + 1))
  rw [hsmul, RCLike.smul_re]
  have hnorm :
      Complex.re (inner ℂ v v) = ‖v‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [hnorm]
  have hnormne : ‖v‖ ^ 2 ≠ 0 := by
    positivity
  apply (div_eq_iff hnormne).2
  ring

/-- A uniform Rayleigh perturbation controls one directed difference of parity
bottoms.  No simplicity assumption is used. -/
theorem parityRayleighBottom_sub_le_of_perturbation_succ
    (p : ReversalParity)
    (L₁ L₂ ε : ℝ)
    (N : ℕ) (hN : 1 ≤ N)
    (hpert :
      ParityRayleighPerturbationBound p L₁ L₂ (N + 1) ε) :
    parityRayleighBottom p L₁ (N + 1) -
        parityRayleighBottom p L₂ (N + 1) ≤ ε := by
  obtain ⟨v, hv0, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ p L₂ N hN
  have hle :=
    parityRayleighBottom_le_rayleigh p L₁ (N + 1) v hv0
  have hle' :
      parityRayleighBottom p L₁ (N + 1) ≤
        parityRayleighQuotientAt p L₁ (N + 1) v := by
    simpa [parityRayleighQuotientAt] using hle
  have hq₂ :
      parityRayleighQuotientAt p L₂ (N + 1) v =
        parityRayleighBottom p L₂ (N + 1) :=
    parityRayleighQuotientAt_eq_bottom_of_eigen_succ
      p L₂ N v hveig hv0
  have habs := hpert.2 v hv0
  have hdir :
      parityRayleighQuotientAt p L₁ (N + 1) v -
          parityRayleighQuotientAt p L₂ (N + 1) v ≤ ε :=
    le_trans (le_abs_self _) habs
  rw [hq₂] at hdir
  linarith

/-- Multiplicity-safe Lipschitz control of the parity Rayleigh bottom. -/
theorem abs_parityRayleighBottom_sub_le_of_perturbation_succ
    (p : ReversalParity)
    (L₁ L₂ ε : ℝ)
    (N : ℕ) (hN : 1 ≤ N)
    (hpert :
      ParityRayleighPerturbationBound p L₁ L₂ (N + 1) ε) :
    |parityRayleighBottom p L₁ (N + 1) -
      parityRayleighBottom p L₂ (N + 1)| ≤ ε := by
  have h12 :=
    parityRayleighBottom_sub_le_of_perturbation_succ
      p L₁ L₂ ε N hN hpert
  have hswap :
      ParityRayleighPerturbationBound p L₂ L₁ (N + 1) ε := by
    refine ⟨hpert.1, ?_⟩
    intro x hx
    simpa [abs_sub_comm] using hpert.2 x hx
  have h21 :=
    parityRayleighBottom_sub_le_of_perturbation_succ
      p L₂ L₁ ε N hN hswap
  exact (abs_le).2 ⟨by linarith, h12⟩

/-- Independent multiplicity-safe perturbation bounds for the two parity
carriers control the actual legal successor ground, which is their minimum.
This reuses the existing `globalParitySuccessorBottom`; no new ground notion is
introduced. -/
theorem abs_globalParitySuccessorBottom_sub_le_of_parity_bounds
    (L₁ L₂ εeven εodd : ℝ)
    (N : ℕ) (hN : 1 ≤ N)
    (heven :
      ParityRayleighPerturbationBound
        .even L₁ L₂ (N + 1) εeven)
    (hodd :
      ParityRayleighPerturbationBound
        .odd L₁ L₂ (N + 1) εodd) :
    |globalParitySuccessorBottom L₁ N -
      globalParitySuccessorBottom L₂ N| ≤
        max εeven εodd := by
  have he :=
    abs_parityRayleighBottom_sub_le_of_perturbation_succ
      .even L₁ L₂ εeven N hN heven
  have ho :=
    abs_parityRayleighBottom_sub_le_of_perturbation_succ
      .odd L₁ L₂ εodd N hN hodd
  unfold globalParitySuccessorBottom
  exact
    (abs_min_sub_min_le_max
      (parityRayleighBottom .even L₁ (N + 1))
      (parityRayleighBottom .odd L₁ (N + 1))
      (parityRayleighBottom .even L₂ (N + 1))
      (parityRayleighBottom .odd L₂ (N + 1))).trans
        (max_le_max he ho)

end Zeta23.CCM

#print axioms Zeta23.CCM.parityRayleighBottom_sub_le_of_perturbation_succ
#print axioms Zeta23.CCM.abs_parityRayleighBottom_sub_le_of_perturbation_succ

#print axioms Zeta23.CCM.abs_globalParitySuccessorBottom_sub_le_of_parity_bounds
