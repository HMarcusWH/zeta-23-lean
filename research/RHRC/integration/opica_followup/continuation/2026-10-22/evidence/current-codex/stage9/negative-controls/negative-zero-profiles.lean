import Zeta23.OPICAFollowup.ZeroProfiles
open Set MeasureTheory Complex
open scoped FourierTransform
open Zeta23.OPICAFollowup
-- (1) the tail coefficient is +kappa, not -kappa
theorem bad_kappa_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile ρ x + spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |x| ^ (-3 : ℝ) :=
  (zero_profile_tail_and_jumps ρ hz h0 h1).1
-- (2) the tail remainder is O(x^-3), not O(x^-4)
theorem bad_tail_exponent (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |x| ^ (-4 : ℝ) :=
  (zero_profile_tail_and_jumps ρ hz h0 h1).1
-- (3) the derivative jump is -kappa/n^2, not +kappa/n^2
theorem bad_jump_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∀ n : ℕ, ∃ dR dL : ℂ,
      HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      dR - dL = spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2 :=
  (zero_profile_tail_and_jumps ρ hz h0 h1).2.2.2.2.1
-- (4) h'(1-) = 0, not 1
theorem bad_left_derivative_one (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    HasDerivWithinAt (zeroProfile ρ) 1 (Iic (1 : ℝ)) 1 :=
  (zero_profile_tail_and_jumps ρ hz h0 h1).2.2.2.2.2.1
-- (5) the plateau is [-1, 1], not [-2, 2]
theorem bad_wide_plateau (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∀ x : ℝ, |x| ≤ 2 → zeroProfile ρ x = 1 :=
  (zero_profile_regular_selfdual ρ hz h0 h1).2.2.2.2.1
-- (6) self-dual, not anti-self-dual
theorem bad_anti_selfdual (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    𝓕 (zeroProfile ρ) = -zeroProfile ρ :=
  (zero_profile_regular_selfdual ρ hz h0 h1).2.2.2.2.2.1
-- (7) the half-line integral is 1/2, not 1
theorem bad_half_line (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∫ x in Ioi (0 : ℝ), zeroProfile ρ x = 1 :=
  (zero_profile_regular_selfdual ρ hz h0 h1).2.2.2.2.2.2.2.2.2
-- (8) the tail needs an actual zero
theorem bad_no_zero (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |x| ^ (-3 : ℝ) :=
  (zero_profile_tail_and_jumps ρ h0 h1).1
-- (9) the strip is not closed at Re rho = 1
theorem bad_closed_strip (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re ≤ 1) :
    Integrable (zeroProfile ρ) :=
  (zero_profile_regular_selfdual ρ hz h0 h1).2.2.1
