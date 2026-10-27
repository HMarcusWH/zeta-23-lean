import Zeta23.OPICARound2.RegionalCertificates

noncomputable section
open Set MeasureTheory Matrix
open scoped Topology BigOperators

namespace Zeta23.OPICARound2.Validation
open CCM.UniversalSinc

theorem expected_p21_small_factor (z : ℂ) (hz : ‖z‖≤1/2) :
    ‖sinc (Complex.I*z)-1‖≤‖z‖^2/3 := probeSinhc_small_difference z hz

theorem expected_p21_small_log_factor (z : ℂ) (hz : ‖z‖≤1/2) :
    -(2*‖z‖^2/3)≤Real.log ‖sinc (Complex.I*z)‖ := probeSinhc_small_log_lower z hz

theorem expected_p21_width_telescope (n : ℕ) :
    width probeSigma n^2 + probeSigma^2/(3*((n:ℝ)+1)^3*((n:ℝ)+2)^3) =
      probeSigma^2/(3*((n:ℝ)+1)^3)-probeSigma^2/(3*((n:ℝ)+2)^3) :=
  regional_width_square_telescope probeSigma n

theorem expected_p21_tail_square_budget (M K : ℕ) :
    ∑ n ∈ Finset.range K, width probeSigma (n+M)^2 ≤
      probeSigma^2/(3*((M:ℝ)+1)^3) := regional_tail_square_sum_sharp probeSigma M K

theorem expected_p21_head_factor {delta0 L : ℝ} (h0 : 0<delta0)
    (z : ℂ) (hz0 : delta0≤z.re) (hzL : ‖z‖≤L) (n : ℕ) :
    delta0/L≤‖sinc ((width probeSigma n:ℂ)*(Complex.I*z))‖ :=
  regional_native_factor_prefix_lower probeSigma_pos h0 z hz0 hzL n

theorem expected_p21_exact_prefix (L : ℝ) (hL0 : 0≤L) (z : ℂ) (hzL : ‖z‖≤L)
    (M : ℕ) (hcut : width probeSigma M*L≤1/2) :
    ‖∏ n ∈ Finset.range M, sinc ((width probeSigma n:ℂ)*(Complex.I*z))‖ *
      Real.exp (-(2*probeSigma^2*L^2/(9*((M:ℝ)+1)^3))) ≤
      ‖product probeSigma (Complex.I*z)‖ :=
  regional_product_prefix_lower probeSigma_pos.le hL0 z hzL M hcut

theorem expected_p21_M0_small_product (L : ℝ) (hL0 : 0≤L) (z : ℂ) (hzL : ‖z‖≤L)
    (hsmall : probeSigma*L≤1) :
    Real.exp (-(probeSigma^2*L^2/3))≤‖product probeSigma (Complex.I*z)‖ :=
  regional_product_small_lower probeSigma_pos.le hL0 z hzL hsmall

theorem expected_p21_split_product {delta0 L : ℝ} (h0 : 0<delta0)
    (z : ℂ) (hz0 : delta0≤z.re) (hzL : ‖z‖≤L) (M : ℕ) (hM : 1≤M)
    (hcut : probeSigma*L/(((M:ℝ)+1)*((M:ℝ)+2))≤1/2) :
    (delta0/L)^M*Real.exp (-(2*probeSigma^2*L^2/(9*(M:ℝ)^3)))≤
      ‖product probeSigma (Complex.I*z)‖ :=
  regional_product_split_lower probeSigma_pos h0 z hz0 hzL M hM hcut

theorem expected_p21_actual_target_transform {z : ℂ} (hz : 0<z.re) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*probeV t) =
      Complex.exp (-z*(probeSigma:ℂ))*((z-1/2)^3*(z+1/2)/(z+3/2))*
        product probeSigma (Complex.I*z) := regional_probeV_product_formula hz

theorem expected_p21_positive_threshold {delta0 delta1 L BQ : ℝ}
    (h0 : 0<delta0) (h01 : delta0≤delta1) (h1 : delta1<1/2)
    (hL : delta1≤L) (hBQ : 0<BQ) :
    0<Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
      ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*BQ := probeBoxMargin_pos h0 h01 h1 hL hBQ

theorem expected_p21_uniform_actual_target_margin {delta0 delta1 L BQ : ℝ}
    (h0 : 0<delta0) (h01 : delta0≤delta1) (h1 : delta1<1/2)
    (hL : delta1≤L) (hBQ0 : 0≤BQ) (z : ℂ)
    (hz : delta0≤z.re ∧ z.re≤delta1 ∧ ‖z‖≤L)
    (hBQ : BQ≤‖product probeSigma (Complex.I*z)‖) :
    Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
      ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*BQ ≤
        Real.sqrt (2*z.re)*‖∫ t : ℝ, Complex.exp (-z*(t:ℂ))*probeV t‖ :=
  regional_box_margin_lower h0 h01 h1 hL hBQ0 hz hBQ

theorem expected_p21_primary {delta0 delta1 L : ℝ}
    (h0 : 0<delta0) (h01 : delta0≤delta1) (h1 : delta1<1/2)
    (hL : delta1≤L) (M : ℕ)
    (hcut : (M=0 ∧ probeSigma*L≤1) ∨
      (1≤M ∧ probeSigma*L/(((M:ℝ)+1)*((M:ℝ)+2))≤1/2)) :
    let BQ : ℝ := if M=0 then Real.exp (-(probeSigma^2*L^2/3))
      else (delta0/L)^M*Real.exp (-(2*probeSigma^2*L^2/(9*(M:ℝ)^3)))
    0<BQ ∧
    0<Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
      ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*BQ ∧
    ∀ z : ℂ, (delta0≤z.re ∧ z.re≤delta1 ∧ ‖z‖≤L) →
      BQ≤‖product probeSigma (Complex.I*z)‖ ∧
      Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
        ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*BQ ≤
          Real.sqrt (2*z.re)*‖∫ t : ℝ, Complex.exp (-z*(t:ℂ))*probeV t‖ :=
  native_product_box_margin h0 h01 h1 hL M hcut

theorem expected_p21_delta0_boundary (delta1 L BQ : ℝ) :
    probeBoxMargin 0 delta1 L BQ=0 := probeBoxMargin_zero_lower delta1 L BQ

theorem expected_p21_delta1_boundary (delta0 L BQ : ℝ) :
    probeBoxMargin delta0 (1/2) L BQ=0 := probeBoxMargin_critical_upper delta0 L BQ

theorem expected_p21_split_zero_cut (delta0 L : ℝ) :
    probeBoxSplitProductLower delta0 L 0=1 := probeBoxSplitProductLower_zero_cut delta0 L

theorem expected_p22_zero_residual_lower {delta0 delta1 L : ℝ}
    (h0 : 0<delta0) (h01 : delta0≤delta1) (h1 : delta1<1/2)
    (hL : delta1≤L) (M : ℕ) (hcut : ProbeBoxCutValid L M)
    {N : ℕ} (x : Fin N → ℂ) (z : ℂ)
    (hz : delta0≤z.re ∧ z.re≤delta1 ∧ ‖z‖≤L)
    (hzero : riemannZeta (1/2+z)=0) :
    Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
      ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*probeBoxProductLower delta0 L M ≤
        ‖probeTarget-∑ i : Fin N, x i • probeColumn (i.val+1)‖ :=
  regional_zero_residual_lower h0 h01 h1 hL M hcut x hz hzero

theorem expected_p22_primary {delta0 delta1 L : ℝ}
    (h0 : 0<delta0) (h01 : delta0≤delta1) (h1 : delta1<1/2)
    (hL : delta1≤L) (M : ℕ) (hcut : ProbeBoxCutValid L M)
    {N : ℕ} (x : Fin N → ℂ) (U : ℝ)
    (hU : ‖probeTarget-∑ i : Fin N, x i • probeColumn (i.val+1)‖^2≤U)
    (hthreshold : U < (Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
      ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*probeBoxProductLower delta0 L M)^2) :
    ∀ z : ℂ, delta0≤z.re ∧ z.re≤delta1 ∧ ‖z‖≤L → riemannZeta (1/2+z)≠0 :=
  zero_region_of_finite_probe_certificate h0 h01 h1 hL M hcut x U hU hthreshold

theorem expected_p22_enclosed_euclidean_data {delta0 delta1 L : ℝ}
    (h0 : 0<delta0) (h01 : delta0≤delta1) (h1 : delta1<1/2)
    (hL : delta1≤L) (M : ℕ) (hcut : ProbeBoxCutValid L M)
    {N : ℕ} (x : Fin N → ℂ) (qhat : ℝ) (bhat : Fin N → ℂ)
    (Ghat : Matrix (Fin N) (Fin N) ℂ) (epsilonQ epsilonB epsilonG : ℝ)
    (hQ : |probeQ0-qhat|≤epsilonQ)
    (hB : ‖probeCoefficientVector (probeTargetColumn N)-probeCoefficientVector bhat‖≤epsilonB)
    (hG : ‖probeCertificateMatrix (probeGram N)-probeCertificateMatrix Ghat‖≤epsilonG)
    (hthreshold : probeNominalEnergy qhat bhat Ghat x+epsilonQ+
      2*epsilonB*‖probeCoefficientVector x‖+epsilonG*‖probeCoefficientVector x‖^2 <
      (Real.sqrt (2*delta0)*Real.exp (-probeSigma*delta1)*
        ((1/2-delta1)^3*(1/2+delta0)/(L+3/2))*probeBoxProductLower delta0 L M)^2) :
    ∀ z : ℂ, delta0≤z.re ∧ z.re≤delta1 ∧ ‖z‖≤L → riemannZeta (1/2+z)≠0 :=
  zero_region_of_enclosed_probe_data h0 h01 h1 hL M hcut x qhat bhat Ghat epsilonQ epsilonB epsilonG hQ hB hG hthreshold

#print axioms expected_p21_primary
#print axioms expected_p22_primary
#print axioms expected_p22_enclosed_euclidean_data

end Zeta23.OPICARound2.Validation
