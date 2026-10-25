import Zeta23.OPICAFollowup.WeightedSpectralMeasure
open Set MeasureTheory Filter Complex
open scoped Topology Real
open Zeta23.OPICAFollowup
-- (1) the weighted moment is log(2 pi) - gamma, not log(2 pi) + gamma
theorem bad_moment_sign :
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure =
      Real.log (2 * π) + Real.eulerMascheroniConstant :=
  arithmetic_stieltjes_holomorphic.2.2.2.2.1
-- (2) the density carries 1/(2 pi): the moment is not 2 pi (log(2 pi) - gamma)
theorem bad_moment_factor :
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure =
      2 * π * (Real.log (2 * π) - Real.eulerMascheroniConstant) :=
  arithmetic_stieltjes_holomorphic.2.2.2.2.1
-- (3) holomorphy is asserted only off the cut [1/4, oo), not on all of C
theorem bad_entire : DifferentiableOn ℂ arithmeticStieltjes univ :=
  arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.2.2
-- (4) the derivative is + int d omega/(a - kappa)^2, not its negative
theorem bad_derivative_sign {κ : ℂ} (hκ : κ ∈ spectralResolventSet) :
    HasDerivAt arithmeticStieltjes
      (-∫ ξ, (((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹ ∂arithmeticSpectralMeasure) κ :=
  arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.2.1 κ hκ
-- (5) absolute convergence needs the resolvent hypothesis (no cut points)
theorem bad_integrable_on_cut (κ : ℂ) :
    Integrable (fun ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹) arithmeticSpectralMeasure :=
  arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.1 κ
-- (6) Im M / Im kappa = + int d omega/|a - kappa|^2, not its negative
theorem bad_sign_identity {κ : ℂ} (hκ : κ.im ≠ 0) :
    (arithmeticStieltjes κ).im / κ.im =
      -∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure :=
  (arithmetic_stieltjes_sign_budget hκ).2.1
-- (7) the sign identity needs Im kappa != 0
theorem bad_sign_no_hypothesis (κ : ℂ) :
    0 < ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure :=
  (arithmetic_stieltjes_sign_budget (κ := κ)).2.2.1
-- (8) the budget bound carries the factor 1 + |kappa|/|Im kappa|, not |kappa|/|Im kappa|
theorem bad_budget_factor {κ : ℂ} (hκ : κ.im ≠ 0) :
    ‖arithmeticStieltjes κ‖ ≤ ‖κ‖ / |κ.im| * (Real.log (2 * π) - Real.eulerMascheroniConstant) :=
  (arithmetic_stieltjes_sign_budget hκ).2.2.2.1
