import Zeta23.OPICAFollowup.FirstCellCost

/- Independent full-domain consumers for the two original first-cell roots.
These statements concern the literal finite-power-sum density. They do not
assert existence, selfduality or growth of the global co-Poisson measure. -/
noncomputable section
open Set MeasureTheory Complex
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICAStageOneExpected

theorem expected_first_cell_sign_full_domain (delta gamma : ℝ)
    (hheight : 3*Real.pi/(2*Real.log 2) < |gamma|) :
    (let u := 3*Real.pi/(2*|gamma|)
     0<u ∧ u<Real.log 2 ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)=
       -|gamma| *(1+1/(4*(delta^2+gamma^2)))*Real.exp (-u/2)*Real.cosh (delta*u) ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)<0) ∧
    (delta≠0 → 2*Real.pi/Real.log 2 < |gamma| → ∀ z : ℂ, z≠0 →
      ∃ x y : ℝ, x∈Ioo (1:ℝ) 2 ∧ y∈Ioo (1:ℝ) 2 ∧
        0<(z*coPoissonComplexDensity (coPoissonRho delta gamma) x).re ∧
        (z*coPoissonComplexDensity (coPoissonRho delta gamma) y).re<0) :=
  zero_measure_first_cell_sign delta gamma hheight

theorem expected_first_cell_mass_full_domain (delta gamma : ℝ)
    (hd : |delta|<1/2) (hg : 16≤|gamma|) :
    (∀ u∈Icc (4*Real.pi/(3*|gamma|)) (5*Real.pi/(3*|gamma|)),
      coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)≤
        -|gamma| *Real.exp (-u/2)/2) ∧
    Real.pi/6≤
      ∫ x in Real.exp (4*Real.pi/(3*|gamma|))..Real.exp (5*Real.pi/(3*|gamma|)),
        max (-coPoissonRealDensity (coPoissonRho delta gamma) x) 0 ∧
    8*Real.pi/(27*gamma^2)≤
      ∫ x in Real.exp (4*Real.pi/(3*|gamma|))..Real.exp (5*Real.pi/(3*|gamma|)),
        sincSquared x*max (-coPoissonRealDensity (coPoissonRho delta gamma) x) 0 := by
  simpa only [firstCellLowerLog,firstCellUpperLog,firstCellNegativeMass,
    firstCellNegativeSincMass,firstCellNegativePart] using
    first_cell_negative_mass_cost delta gamma hd hg

theorem expected_actual_zero_first_cell_cost (rho : ℂ)
    (hzero : IsNontrivialZero rho) (hg : 16≤|rho.im|) :
    (∀ u∈Icc (4*Real.pi/(3*|rho.im|)) (5*Real.pi/(3*|rho.im|)),
      coPoissonRealDensity rho (Real.exp u)≤-|rho.im| *Real.exp (-u/2)/2) ∧
    Real.pi/6≤
      ∫ x in Real.exp (4*Real.pi/(3*|rho.im|))..Real.exp (5*Real.pi/(3*|rho.im|)),
        max (-coPoissonRealDensity rho x) 0 ∧
    8*Real.pi/(27*rho.im^2)≤
      ∫ x in Real.exp (4*Real.pi/(3*|rho.im|))..Real.exp (5*Real.pi/(3*|rho.im|)),
        sincSquared x*max (-coPoissonRealDensity rho x) 0 := by
  have hd : |rho.re-1/2|<1/2 := abs_lt.mpr ⟨by linarith [hzero.2.1],by linarith [hzero.2.2]⟩
  have hrho : coPoissonRho (rho.re-1/2) rho.im=rho := by
    apply Complex.ext <;> simp [coPoissonRho]
  simpa only [hrho] using expected_first_cell_mass_full_domain (rho.re-1/2) rho.im hd hg

theorem expected_negative_ordinate_endpoint (delta : ℝ) (hd : |delta|<1/2) :
    Real.pi/6≤firstCellNegativeMass delta (-16) ∧
    8*Real.pi/(27*256)≤firstCellNegativeSincMass delta (-16) := by
  have h := first_cell_negative_mass_cost delta (-16) hd (by norm_num)
  norm_num only [neg_sq,show (16:ℝ)^2=256 by norm_num] at h
  simpa only [show (27:ℝ)*256=6912 by norm_num] using h.2

theorem expected_positive_ordinate_endpoint (delta : ℝ) (hd : |delta|<1/2) :
    Real.pi/6≤firstCellNegativeMass delta 16 ∧
    8*Real.pi/(27*256)≤firstCellNegativeSincMass delta 16 := by
  have h := first_cell_negative_mass_cost delta 16 hd (by norm_num)
  norm_num only [show (16:ℝ)^2=256 by norm_num] at h
  simpa only [show (27:ℝ)*256=6912 by norm_num] using h.2

theorem expected_online_cost_both_ordinates (gamma : ℝ) (hg : 16≤|gamma|) :
    Real.pi/6≤firstCellNegativeMass 0 gamma ∧
    8*Real.pi/(27*gamma^2)≤firstCellNegativeSincMass 0 gamma :=
  (first_cell_negative_mass_cost 0 gamma (by norm_num) hg).2

/-- This falsifies removal of the off-line condition from the phase clause:
on the critical line the imaginary scalar projection is identically zero
throughout the first open cell, even though the real density has a negative point. -/
theorem expected_online_imaginary_projection_zero (gamma x : ℝ)
    (hg : gamma≠0) (hx : x∈Ioo (1:ℝ) 2) :
    (I*coPoissonComplexDensity (coPoissonRho 0 gamma) x).re=0 := by
  have hxpos : 0<x := zero_lt_one.trans hx.1
  have h := coPoisson_phase_formula 0 gamma (Real.log x) I hg
    (Real.log_pos hx.1) (Real.log_lt_log hxpos hx.2)
  have hQ := (coPoisson_quotient_re_im 0 gamma hg).1
  dsimp only at h
  simp only [Complex.ofReal_zero,zero_add] at h hQ
  have hAi : (I*((1/4-((gamma:ℂ)*I)^2)/((gamma:ℂ)*I))).im=0 := by
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add]
    simpa only [zero_mul] using hQ
  rw [hAi] at h
  simpa only [Real.exp_log hxpos,zero_mul,Real.sinh_zero,mul_zero,sub_zero] using h

/-- Per-profile costs cannot be summed blindly over conjugate ordinates:
their real first-cell profiles agree, so opposite real coefficients cancel. -/
theorem expected_conjugate_pair_first_cell_cancellation (delta gamma u : ℝ)
    (hg : gamma≠0) (hu : 0<u) (hu1 : u<Real.log 2) :
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)-
      coPoissonRealDensity (coPoissonRho delta (-gamma)) (Real.exp u)=0 := by
  rw [coPoisson_first_cell_gamma_abs delta gamma u hg hu hu1,
    coPoisson_first_cell_gamma_abs delta (-gamma) u (neg_ne_zero.mpr hg) hu hu1,abs_neg]
  exact sub_self _

end OPICAStageOneExpected

#print axioms Zeta23.OPICAFollowup.zero_measure_first_cell_sign
#print axioms Zeta23.OPICAFollowup.first_cell_negative_mass_cost
#print axioms OPICAStageOneExpected.expected_actual_zero_first_cell_cost
#print axioms OPICAStageOneExpected.expected_online_imaginary_projection_zero
#print axioms OPICAStageOneExpected.expected_conjugate_pair_first_cell_cancellation
