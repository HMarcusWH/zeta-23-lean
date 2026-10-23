import Zeta23.OPICAFollowup.LogFourierSobolev
open Set MeasureTheory Complex
open scoped FourierTransform Real
open Zeta23.OPICAFollowup
-- (1) the boundary term is +1/4, not -1/4
theorem bad_form_sign (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    logForm h' = (∫ t, ‖logUnitaryDeriv h h' t‖ ^ 2) - 1 / 4 * ∫ x in Ioi 0, ‖h x‖ ^ 2 :=
  (log_unitary_form_identity h h' hD).2.2.2.2.1
-- (2) the unitary has the weight e^(t/2); without it the L² norms do not match
theorem bad_unitary_weight (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    (∫ t, ‖h (Real.exp t)‖ ^ 2) = ∫ x in Ioi 0, ‖h x‖ ^ 2 :=
  (log_unitary_form_identity h h' hD).2.1
-- (3) the log convention has no 2π in the phase: 𝓕_log f(ξ) = 𝓕 f(ξ/(2π)), not 𝓕 f(ξ)
theorem bad_convention (f : ℝ → ℂ) (ξ : ℝ) : logFourier f ξ = 𝓕 f ξ :=
  log_fourier_plancherel.2.1 f ξ
-- (4) Plancherel factor 1/(2π), not 1
theorem bad_plancherel_factor (f : ℝ → ℂ) (h1 : Integrable f) (h2 : MemLp f 2) :
    ∫ t, ‖f t‖ ^ 2 = ∫ ξ, ‖logFourier f ξ‖ ^ 2 :=
  (log_fourier_plancherel.2.2.1 f h1 h2).2
-- (5) differentiation multiplies by iξ, not by 2πiξ
theorem bad_derivative_factor (f : ℝ → ℂ) (h1 : Integrable f) (hd : Differentiable ℝ f)
    (h2 : Integrable (deriv f)) (ξ : ℝ) :
    logFourier (deriv f) ξ = 2 * π * (ξ : ℂ) * I * logFourier f ξ :=
  log_fourier_plancherel.2.2.2.1 f h1 hd h2 ξ
-- (6) the spectral weight is ξ² + 1/4, not ξ² + 1
theorem bad_weight (f : ℝ → ℂ) (h1 : Integrable f) (h2 : MemLp f 2) (hd : Differentiable ℝ f)
    (hd1 : Integrable (deriv f)) (hd2 : MemLp (deriv f) 2) :
    (∫ t, ‖deriv f t‖ ^ 2) + 1 / 4 * ∫ t, ‖f t‖ ^ 2 =
      1 / (2 * π) * ∫ ξ, (ξ ^ 2 + 1) * ‖logFourier f ξ‖ ^ 2 :=
  log_fourier_plancherel.2.2.2.2.1 f h1 h2 hd hd1 hd2
-- (7) the force pairing uses φ' - φ/2, not φ' + φ/2
theorem bad_force_shift (w φ φ' : ℝ → ℂ) (hw : MemLp w 2) (hφ : LogH1 φ φ') :
    ‖∫ t, w t * (φ' t + φ t / 2)‖ ≤
      (∫ t, ‖w t‖ ^ 2) ^ (1 / 2 : ℝ) * ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ) :=
  log_fourier_plancherel.2.2.2.2.2.2 w φ φ' hw hφ
-- (8) Plancherel needs L¹ ∩ L² (no L² hypothesis dropped)
theorem bad_plancherel_no_L2 (f : ℝ → ℂ) (h1 : Integrable f) :
    ∫ t, ‖f t‖ ^ 2 = 1 / (2 * π) * ∫ ξ, ‖logFourier f ξ‖ ^ 2 :=
  (log_fourier_plancherel.2.2.1 f h1).2
