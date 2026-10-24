import Zeta23.OPICAFollowup.ForcedEuler
open Set MeasureTheory Complex
open Zeta23.OPICAFollowup
-- (1) the force has sign +kappa, not -kappa
theorem bad_force_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : ℝ → ℂ) (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = -spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
      ∑' n : ℕ, φ (n + 1)) :=
  (zero_profile_forced_euler ρ hz h0 h1).1 φ hφ
-- (2) the equation is forced: the integer atoms cannot be dropped
theorem bad_no_atoms (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : ℝ → ℂ) (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = spectralKappa ρ * ∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x :=
  (zero_profile_forced_euler ρ hz h0 h1).1 φ hφ
-- (3) the atoms have weight kappa, not kappa/n^2
theorem bad_atom_weight (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : ℝ → ℂ) (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
      ∑' n : ℕ, φ (n + 1) / ((n : ℂ) + 1) ^ 2) :=
  (zero_profile_forced_euler ρ hz h0 h1).1 φ hφ
-- (4) the continuum part is h - 1, not h (no homogeneous L h = kappa h)
theorem bad_homogeneous_part (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : ℝ → ℂ) (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, zeroProfile ρ x * φ x) +
      ∑' n : ℕ, φ (n + 1)) :=
  (zero_profile_forced_euler ρ hz h0 h1).1 φ hφ
-- (5) between integers (x^2 h')' = kappa (1 - h), not kappa (h - 1)
theorem bad_ordinary_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (x : ℝ) (hx : 0 < x) (hn : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * deriv (zeroProfile ρ) y)
      (spectralKappa ρ * (zeroProfile ρ x - 1)) x :=
  (zero_profile_forced_euler ρ hz h0 h1).2.2.1 x hx hn
-- (6) the jump of x^2 h' is -kappa, not +kappa
theorem bad_jump_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∀ n : ℕ, 1 ≤ n → ContinuousAt (zeroProfile ρ) n ∧
      ∃ dR dL : ℂ, HasDerivWithinAt (zeroProfile ρ) dR (Ici (n : ℝ)) n ∧
        HasDerivWithinAt (zeroProfile ρ) dL (Iic (n : ℝ)) n ∧
        (n : ℂ) ^ 2 * (dR - dL) = spectralKappa ρ :=
  (zero_profile_forced_euler ρ hz h0 h1).2.2.2
-- (7) the Euler image is not an L2 function
theorem bad_l2_image (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioi 0)) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x :=
  (zero_profile_not_homogeneous_operator_vector ρ hz h0 h1).2.2.1
-- (8) no homogeneous eigenvalue equation -(x^2 h')' = kappa h
theorem bad_eigenvector (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = spectralKappa ρ * ∫ x in Ioi 0, zeroProfile ρ x * φ x :=
  (zero_profile_not_homogeneous_operator_vector ρ hz h0 h1).2.2.2.1 (spectralKappa ρ)
-- (9) the actual zero hypothesis is required by the root
theorem bad_no_zero (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : ℝ → ℂ)
    (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
      ∑' n : ℕ, φ (n + 1)) :=
  (zero_profile_forced_euler ρ h0 h1).1 φ hφ
