import Zeta23.OPICAFollowup.SawtoothForce
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup
-- (1) the Mellin transform is -zeta(s)/s, not zeta(s)/s
theorem bad_mellin_sign (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = riemannZeta s / s :=
  ((sawtooth_actual_mellin_fourier).1 s h0 h1).2
-- (2) the log-Fourier denominator is 1/2 + i xi, not 1/2 - i xi
theorem bad_conjugate_denominator (ξ : ℝ) :
    logFourier sawtoothWeight ξ = -riemannZeta (1 / 2 + ξ * I) / (1 / 2 - ξ * I) :=
  (sawtooth_actual_mellin_fourier).2.1 ξ
-- (3) in the Mathlib convention the force transform is zeta(1/2 + 2 pi i eta), not zeta(1/2 + i eta)
theorem bad_force_convention (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 nativeLogForce) φ = ∫ η : ℝ, riemannZeta (1 / 2 + η * I) * φ η :=
  (sawtooth_actual_mellin_fourier).2.2.2 φ
-- (4) the continuum part enters with a minus sign
theorem bad_continuum_sign (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    nativeLogForce (hc.toSchwartzMap hφ) =
      ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) +
        ∫ t, (Real.exp (t / 2) : ℂ) * φ t :=
  (sawtooth_integrable_force_identity).2.2.2.2.2.1 φ hφ hc
-- (5) the atom weights are n^(-1/2), not n^(1/2)
theorem bad_atom_weight (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    nativeLogForce (hc.toSchwartzMap hφ) =
      ∑' n : ℕ, ((((n : ℝ) + 1) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
        ∫ t, (Real.exp (t / 2) : ℂ) * φ t :=
  (sawtooth_integrable_force_identity).2.2.2.2.2.1 φ hφ hc
-- (6) the left limit at log n is n^(-1/2), not 1
theorem bad_left_limit (n : ℕ) (hn : 1 ≤ n) :
    Tendsto sawtoothWeight (𝓝[<] (Real.log n)) (𝓝 1) :=
  ((sawtooth_integrable_force_identity).2.2.2.2.2.2 n hn).1
-- (7) the budget is log(2 pi) - gamma, not log(2 pi) + gamma
theorem bad_budget_sign :
    (∫ t, ‖sawtoothWeight t‖ ^ 2) = Real.log (2 * π) + Real.eulerMascheroniConstant :=
  (sawtooth_norm_weighted_zeta_moment).2.2.2.2.1
-- (8) the weighted moment carries the Plancherel factor 1/(2 pi)
theorem bad_moment_factor :
    ∫ ξ : ℝ, ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4) =
      Real.log (2 * π) - Real.eulerMascheroniConstant :=
  (sawtooth_norm_weighted_zeta_moment).2.2.2.2.2.2.1
-- (9) the closed form has -2(L-1) log L, not -2L log L
theorem bad_closed_form (L : ℕ) (hL : 1 ≤ L) :
    ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2 =
      2 * L - harmonic L - 2 * L * Real.log L + 2 * Real.log (Real.Gamma L) :=
  (sawtooth_norm_weighted_zeta_moment).2.2.1 L hL
-- (10) the H^-1 constant is the square root of the budget
theorem bad_hminus1_constant (φ : 𝓢(ℝ, ℂ)) :
    ‖nativeLogForce φ‖ ≤ (Real.log (2 * π) - Real.eulerMascheroniConstant) *
      ((∫ t, ‖deriv φ t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ) :=
  (sawtooth_norm_weighted_zeta_moment).2.2.2.2.2.2.2.2 φ
