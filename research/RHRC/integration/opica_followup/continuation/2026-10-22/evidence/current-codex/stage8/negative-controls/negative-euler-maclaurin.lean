import Zeta23.OPICAFollowup.ProfileEulerMaclaurin
open Set Complex
open Zeta23.OPICAFollowup
-- (1) the right endpoint convention: B₁ at integers is -1/2, not +1/2
theorem bad_left_endpoint_value (n : ℕ) : bernoulliOneRight n = 1 / 2 :=
  (finite_sum_euler_maclaurin_uniform.2.1 n).1
-- (2) the finite sum on [n, n+1) includes n; it is not the left-closed sum over [1, n)
theorem bad_left_closed_sum (s : ℂ) (n : ℕ) (y : ℝ) (hy : y ∈ Ico (n : ℝ) (n + 1)) :
    rightPowerSum s y = ∑ k ∈ Finset.Ico 1 n, (k : ℂ) ^ (-s) :=
  finite_sum_euler_maclaurin_uniform.1 s n y hy
-- (3) the sign of the B₁ term is negative
theorem bad_B1_sign (s : ℂ) (h0 : 0 < s.re) (h1 : s ≠ 1) (x : ℝ) (hx : 1 ≤ x) :
    rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) +
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x :=
  finite_sum_euler_maclaurin_uniform.2.2.1 s h0 h1 x hx
-- (4) the B₂ coefficient is s/2, not s
theorem bad_B2_coefficient (s : ℂ) (h0 : 0 < s.re) (h1 : s ≠ 1) (x : ℝ) (hx : 1 ≤ x) :
    rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) + eulerMaclaurinRemainder s x :=
  finite_sum_euler_maclaurin_uniform.2.2.1 s h0 h1 x hx
-- (5) the remainder is O(x^(-Re s - 2)); the root does not claim x^(-Re s - 3)
theorem bad_remainder_exponent (s : ℂ) (h0 : 0 < s.re) (x : ℝ) (hx : 0 < x) :
    ‖eulerMaclaurinRemainder s x‖ ≤
      (‖s‖ * (‖s‖ + 1) / 6 + ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 12) * x ^ (-s.re - 3) :=
  finite_sum_euler_maclaurin_uniform.2.2.2.1 s h0 x hx
-- (6) the domain is not widened to Re s ≥ 0
theorem bad_closed_half_plane (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s ≠ 1) (x : ℝ) (hx : 1 ≤ x) :
    rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x :=
  finite_sum_euler_maclaurin_uniform.2.2.1 s h0 h1 x hx
-- (7) ζ(s) is the actual continued zeta function, not the (strip-divergent) Dirichlet tsum
theorem bad_dirichlet_series (s : ℂ) (h0 : 0 < s.re) (h1 : s ≠ 1) (x : ℝ) (hx : 1 ≤ x) :
    rightPowerSum s x = (∑' n : ℕ, 1 / (n : ℂ) ^ s) + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x :=
  finite_sum_euler_maclaurin_uniform.2.2.1 s h0 h1 x hx
-- (8) the cutoff must satisfy x ≥ 1
theorem bad_small_cutoff (s : ℂ) (h0 : 0 < s.re) (h1 : s ≠ 1) (x : ℝ) (hx : 0 < x) :
    rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x :=
  finite_sum_euler_maclaurin_uniform.2.2.1 s h0 h1 x hx
