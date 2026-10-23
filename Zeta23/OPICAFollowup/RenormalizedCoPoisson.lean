import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Zeta23.OPICAFollowup.DilatedComb
import Zeta23.ExceptionalZero.ZetaRealStripNonvanishing
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
The density below is the literal inclusive finite-power-sum density of the
frozen co-Poisson construction. Its first-cell sign identities use no positivity
assumption, synthetic zero or assumed measure with desired Fourier properties.
The distributional construction is the renormalized tempered family below. Section
`OrderZero` identifies its actual cutoffs with locally finite complex measures, proves
their local-total-variation convergence (origin atom included) to the order-zero limit
measure and identifies the family with that measure on every Schwartz test. The
Section `ZeroMeasure` builds the normalized actual zero measure (CP1.7)/b_ρ and proves
its exact properties at every actual nontrivial zero ρ ≠ 1/2.
-/

noncomputable section
open Set Finset Complex Filter MeasureTheory
open scoped Topology
namespace Zeta23.OPICAFollowup

/-- Inclusive right-integer endpoint convention. Zero is not an integer term. -/
def coPoissonPowerSums (rho : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^(-rho)*(∑ n ∈ Finset.Icc 1 (Nat.floor x), (n:ℂ)^(rho-1)) -
    (x:ℂ)^(rho-1)*(∑ n ∈ Finset.Icc 1 (Nat.floor x), (n:ℂ)^(-rho))

def coPoissonOriginNormalizer (rho : ℂ) : ℂ := 1/rho-1/(1-rho)

def coPoissonComplexDensity (rho : ℂ) (x : ℝ) : ℂ :=
  coPoissonPowerSums rho |x|/coPoissonOriginNormalizer rho

def coPoissonRealDensity (rho : ℂ) (x : ℝ) : ℝ :=
  (coPoissonComplexDensity rho x).re

def coPoissonRho (delta gamma : ℝ) : ℂ := (1/2:ℂ)+(delta:ℂ)+(gamma:ℂ)*I

def coPoissonKappa (rho : ℂ) : ℂ := rho*(1-rho)

lemma coPoisson_first_cell_sum (rho : ℂ) {x : ℝ} (hx : x∈Ioo (1:ℝ) 2) :
    coPoissonPowerSums rho x=(x:ℂ)^(-rho)-(x:ℂ)^(rho-1) := by
  have hx0 : (0:ℝ)≤x := zero_le_one.trans hx.1.le
  have hfloor : Nat.floor x=1 := (Nat.floor_eq_iff hx0).2
    (by norm_num; exact ⟨hx.1.le,hx.2⟩)
  simp [coPoissonPowerSums,hfloor]

lemma coPoisson_normalizer (rho : ℂ) (h0 : rho≠0) (h1 : rho≠1) :
    coPoissonOriginNormalizer rho=(1-2*rho)/(rho*(1-rho)) := by
  unfold coPoissonOriginNormalizer
  field_simp [h0,sub_ne_zero.mpr (Ne.symm h1)]
  ring

lemma coPoissonRho_ne_real_special (delta gamma : ℝ) (hg : gamma≠0) :
    coPoissonRho delta gamma≠0 ∧ coPoissonRho delta gamma≠1 ∧
      coPoissonRho delta gamma≠1/2 ∧ (delta:ℂ)+(gamma:ℂ)*I≠0 := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> apply hg
  all_goals
    have hi := congrArg Complex.im h
    norm_num [coPoissonRho,Complex.div_im] at hi
    exact hi

/-- Exact first-cell complex formula, derived from the actual finite sums. -/
lemma coPoisson_first_cell_exp (delta gamma u : ℝ) (hg : gamma≠0)
    (hu : 0<u) (hu1 : u<Real.log 2) :
    coPoissonComplexDensity (coPoissonRho delta gamma) (Real.exp u) =
      ((Real.exp (-u/2):ℝ):ℂ)*
      ((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I))*
      Complex.sinh (((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ)) := by
  let lam : ℂ := (delta:ℂ)+(gamma:ℂ)*I
  let rho := coPoissonRho delta gamma
  obtain ⟨h0,h1,hh,hL⟩ := coPoissonRho_ne_real_special delta gamma hg
  have hx : Real.exp u∈Ioo (1:ℝ) 2 := ⟨Real.one_lt_exp_iff.mpr hu,
    (Real.exp_lt_exp.mpr hu1).trans_eq (Real.exp_log (by norm_num))⟩
  have hpow (z : ℂ) : ((Real.exp u:ℝ):ℂ)^z=Complex.exp ((u:ℂ)*z) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero u)),
      ←Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp]
  have hb := coPoisson_normalizer rho h0 h1
  have hk : rho*(1-rho)=1/4-lam^2 := by dsimp [rho,coPoissonRho,lam]; ring
  have hnum : 1-2*rho=-2*lam := by dsimp [rho,coPoissonRho,lam]; ring
  have hsplit_neg : Complex.exp ((u:ℂ)*(-rho))=
      ((Real.exp (-u/2):ℝ):ℂ)*Complex.exp (-(lam*(u:ℂ))) := by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    dsimp [rho,coPoissonRho,lam]
    push_cast
    ring
  have hsplit_pos : Complex.exp ((u:ℂ)*(rho-1))=
      ((Real.exp (-u/2):ℝ):ℂ)*Complex.exp (lam*(u:ℂ)) := by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    dsimp [rho,coPoissonRho,lam]
    push_cast
    ring
  unfold coPoissonComplexDensity
  rw [abs_of_pos (Real.exp_pos u),coPoisson_first_cell_sum rho hx,hpow,hpow,
    hsplit_neg,hsplit_pos,hb,hk,hnum,Complex.sinh]
  change (((Real.exp (-u/2):ℝ):ℂ)*Complex.exp (-(lam*(u:ℂ))) -
      ((Real.exp (-u/2):ℝ):ℂ)*Complex.exp (lam*(u:ℂ))) /
      (-2*lam/(1/4-lam^2)) =
    ((Real.exp (-u/2):ℝ):ℂ)*((1/4-lam^2)/lam)*
      ((Complex.exp (lam*(u:ℂ))-Complex.exp (-(lam*(u:ℂ))))/2)
  have hlam : lam≠0 := hL
  field_simp [hlam]
  ring

lemma coPoisson_quotient_re_im (delta gamma : ℝ) (hg : gamma≠0) :
    ((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I)).re =
      delta*(1/(4*(delta^2+gamma^2))-1) ∧
    ((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I)).im =
      -gamma*(1+1/(4*(delta^2+gamma^2))) := by
  have hs : delta^2+gamma^2≠0 := ne_of_gt (by nlinarith [sq_pos_of_ne_zero hg])
  have hsplit : (1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I)=
      (1/4:ℂ)/((delta:ℂ)+(gamma:ℂ)*I)-((delta:ℂ)+(gamma:ℂ)*I) := by
    field_simp [(coPoissonRho_ne_real_special delta gamma hg).2.2.2]
  rw [hsplit]
  constructor <;> simp only [Complex.sub_re,Complex.sub_im,Complex.div_re,Complex.div_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_apply]
  all_goals norm_num
  all_goals field_simp [hs]
  all_goals ring

lemma coPoisson_sinh_re_im (a b : ℝ) :
    (Complex.sinh ((a:ℂ)+(b:ℂ)*I)).re=Real.sinh a*Real.cos b ∧
    (Complex.sinh ((a:ℂ)+(b:ℂ)*I)).im=Real.cosh a*Real.sin b := by
  rw [Complex.sinh_add,Complex.cosh_mul_I,Complex.sinh_mul_I]
  simp [Complex.mul_re,Complex.mul_im,Complex.sinh_ofReal_re,
    Complex.cos_ofReal_re,Complex.sin_ofReal_re]

lemma coPoisson_first_cell_real (delta gamma u : ℝ) (hg : gamma≠0)
    (hu : 0<u) (hu1 : u<Real.log 2) :
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u) =
      Real.exp (-u/2)*
       (delta*(1/(4*(delta^2+gamma^2))-1)*Real.sinh (delta*u)*Real.cos (gamma*u)+
        gamma*(1+1/(4*(delta^2+gamma^2)))*Real.cosh (delta*u)*Real.sin (gamma*u)) := by
  unfold coPoissonRealDensity
  rw [coPoisson_first_cell_exp delta gamma u hg hu hu1]
  obtain ⟨hre,him⟩ := coPoisson_quotient_re_im delta gamma hg
  have harg : ((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ)=((delta*u:ℝ):ℂ)+((gamma*u:ℝ):ℂ)*I := by
    push_cast
    ring
  obtain ⟨hsre,hsim⟩ := coPoisson_sinh_re_im (delta*u) (gamma*u)
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero]
  rw [harg,hsre,hsim,hre,him]
  ring

lemma coPoisson_first_cell_gamma_abs (delta gamma u : ℝ) (hg : gamma≠0)
    (hu : 0<u) (hu1 : u<Real.log 2) :
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u) =
      coPoissonRealDensity (coPoissonRho delta |gamma|) (Real.exp u) := by
  rw [coPoisson_first_cell_real delta gamma u hg hu hu1,
    coPoisson_first_cell_real delta |gamma| u (abs_ne_zero.mpr hg) hu hu1]
  rcases le_total 0 gamma with h | h
  · rw [abs_of_nonneg h]
  · simp [abs_of_nonpos h,neg_mul,Real.cos_neg,Real.sin_neg]

/-- A selected first-cell point has an exactly calculated negative density.
The height threshold is strict, so the point lies inside the open cell. -/
lemma coPoisson_first_cell_negative_value (delta gamma : ℝ)
    (hgamma : 3*Real.pi/(2*Real.log 2) < |gamma|) :
    let u := 3*Real.pi/(2*|gamma|)
    0<u ∧ u<Real.log 2 ∧
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)=
      -|gamma| *(1+1/(4*(delta^2+gamma^2)))*
        Real.exp (-u/2)*Real.cosh (delta*u) ∧
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)<0 := by
  have hg : 0< |gamma| := lt_trans (by positivity) hgamma
  have hgne : gamma≠0 := abs_pos.mp hg
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  dsimp only
  have hu : 0<3*Real.pi/(2*|gamma|) := by positivity
  have hu1 : 3*Real.pi/(2*|gamma|)<Real.log 2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have h := (div_lt_iff₀ (by positivity : 0<2*Real.log 2)).mp hgamma
    nlinarith
  have he := coPoisson_first_cell_real delta |gamma| (3*Real.pi/(2*|gamma|))
    hg.ne' hu hu1
  have hang : |gamma| *(3*Real.pi/(2*|gamma|))=Real.pi/2+Real.pi := by
    field_simp [hg.ne']; ring
  rw [hang,Real.cos_add_pi,Real.sin_add_pi,Real.cos_pi_div_two,Real.sin_pi_div_two] at he
  have hid : coPoissonRealDensity (coPoissonRho delta gamma)
      (Real.exp (3*Real.pi/(2*|gamma|))) =
      -|gamma| *(1+1/(4*(delta^2+gamma^2)))*
        Real.exp (-(3*Real.pi/(2*|gamma|))/2)*Real.cosh (delta*(3*Real.pi/(2*|gamma|))) := by
    rw [coPoisson_first_cell_gamma_abs delta gamma _ hgne hu hu1,he]
    simp only [sq_abs,neg_zero,mul_zero,mul_neg_one,zero_add]
    ring
  refine ⟨hu,hu1,hid,?_⟩
  rw [hid]
  have hc := Real.cosh_pos (delta*(3*Real.pi/(2*|gamma|)))
  have hb : 0<1+1/(4*(delta^2+gamma^2)) := by positivity
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hg) hb) (Real.exp_pos _)) hc

lemma coPoisson_phase_formula (delta gamma u : ℝ) (z : ℂ) (hg : gamma≠0)
    (hu : 0<u) (hu1 : u<Real.log 2) :
    (z*coPoissonComplexDensity (coPoissonRho delta gamma) (Real.exp u)).re =
      let A := z*((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I))
      Real.exp (-u/2)*(A.re*Real.sinh (delta*u)*Real.cos (gamma*u)-
        A.im*Real.cosh (delta*u)*Real.sin (gamma*u)) := by
  rw [coPoisson_first_cell_exp delta gamma u hg hu hu1]
  dsimp only
  let Q : ℂ := (1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I)
  have hmul : z*(((Real.exp (-u/2):ℝ):ℂ)*Q*
      Complex.sinh (((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ))) =
      ((Real.exp (-u/2):ℝ):ℂ)*((z*Q)*
        Complex.sinh (((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ))) := by ring
  change (z*(((Real.exp (-u/2):ℝ):ℂ)*Q*
      Complex.sinh (((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ)))).re = _
  rw [hmul]
  have harg : ((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ)=((delta*u:ℝ):ℂ)+((gamma*u:ℝ):ℂ)*I := by
    push_cast
    ring
  obtain ⟨hsre,hsim⟩ := coPoisson_sinh_re_im (delta*u) (gamma*u)
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [harg,hsre,hsim]
  dsimp [Q]
  ring

/-- Finite phase tuning cannot repair the sign of an off-line first-cell
profile. The four test points lie in (0,log 2) before their signs are used. -/
lemma coPoisson_phase_both_signs (delta gamma : ℝ) (hdelta : delta≠0)
    (hheight : 2*Real.pi/Real.log 2 < |gamma|) (z : ℂ) (hz : z≠0) :
    ∃ x y : ℝ, x∈Ioo (1:ℝ) 2 ∧ y∈Ioo (1:ℝ) 2 ∧
      0<(z*coPoissonComplexDensity (coPoissonRho delta gamma) x).re ∧
      (z*coPoissonComplexDensity (coPoissonRho delta gamma) y).re<0 := by
  have hg : 0< |gamma| := lt_trans (by positivity) hheight
  have hgne : gamma≠0 := abs_pos.mp hg
  let A := z*((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I))
  have hA : A≠0 := by
    apply mul_ne_zero hz
    apply div_ne_zero _ (coPoissonRho_ne_real_special delta gamma hgne).2.2.2
    intro h
    have hfac : (((delta:ℂ)+(gamma:ℂ)*I)-1/2)*
        (((delta:ℂ)+(gamma:ℂ)*I)+1/2)=0 := by linear_combination -h
    rcases mul_eq_zero.mp hfac with hm | hp
    · apply hgne
      have hi := congrArg Complex.im hm
      norm_num [Complex.div_im] at hi
      exact hi
    · apply hgne
      have hi := congrArg Complex.im hp
      norm_num [Complex.div_im] at hi
      exact hi
  have hpoint (a : ℝ) (ha : 0<a) (ha2 : a≤2*Real.pi) :
      0<a/|gamma| ∧ a/|gamma|<Real.log 2 ∧ Real.exp (a/|gamma|)∈Ioo (1:ℝ) 2 := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hu : 0<a/|gamma| := div_pos ha hg
    have hu1 : a/|gamma|<Real.log 2 := by
      apply (div_lt_iff₀ hg).mpr
      have h := (div_lt_iff₀ hlog).mp hheight
      nlinarith
    exact ⟨hu,hu1,Real.one_lt_exp_iff.mpr hu,
      (Real.exp_lt_exp.mpr hu1).trans_eq (Real.exp_log (by norm_num))⟩
  have htrig (a : ℝ) : gamma*(a/|gamma|) = if 0<gamma then a else -a := by
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · have hn : gamma<0 := lt_of_le_of_ne (le_of_not_gt h) hgne
      rw [abs_of_neg hn]; field_simp
  by_cases hAre : A.re=0
  · have hAi : A.im≠0 := by
      intro h
      apply hA
      exact Complex.ext hAre h
    obtain ⟨hu₀,hu₁,hx⟩ := hpoint (Real.pi/2) (by positivity) (by linarith [Real.pi_pos])
    obtain ⟨hv₀,hv₁,hy⟩ := hpoint (3*Real.pi/2) (by positivity) (by linarith [Real.pi_pos])
    have hxf := coPoisson_phase_formula delta gamma (Real.pi/(2*|gamma|)) z hgne
      (by simpa only [div_div] using hu₀) (by simpa only [div_div] using hu₁)
    have hyf := coPoisson_phase_formula delta gamma (3*Real.pi/(2*|gamma|)) z hgne
      (by simpa only [div_div] using hv₀) (by simpa only [div_div] using hv₁)
    have hxy : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (Real.pi/(2*|gamma|)))).re *
      (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (3*Real.pi/(2*|gamma|)))).re < 0 := by
      rw [hxf,hyf]
      change (Real.exp _*(A.re*Real.sinh _*Real.cos _ -
        A.im*Real.cosh _*Real.sin _)) * (Real.exp _*(A.re*Real.sinh _*Real.cos _ -
        A.im*Real.cosh _*Real.sin _)) < 0
      rw [hAre]
      have hhalf : gamma*(Real.pi/(2*|gamma|))=if 0<gamma then Real.pi/2 else -(Real.pi/2) := by
        simpa only [div_div] using htrig (Real.pi/2)
      have hthree : gamma*(3*Real.pi/(2*|gamma|))=if 0<gamma then Real.pi/2+Real.pi else -(Real.pi/2+Real.pi) := by
        calc
          _ = gamma*((Real.pi/2+Real.pi)/|gamma|) := by congr 1; ring
          _ = _ := htrig (Real.pi/2+Real.pi)
      rw [hhalf,hthree]
      split_ifs <;> simp only [Real.sin_pi_div_two,Real.sin_add_pi,Real.sin_neg,
        zero_mul,zero_sub,neg_neg,mul_neg_one,mul_one]
      all_goals
        have hpos : 0<Real.exp (-(Real.pi/(2*|gamma|))/2)*
            Real.exp (-(3*Real.pi/(2*|gamma|))/2)*A.im^2*
            Real.cosh (delta*(Real.pi/(2*|gamma|)))*
            Real.cosh (delta*(3*Real.pi/(2*|gamma|))) := by positivity
        convert (neg_lt_zero.mpr hpos) using 1
        ring
    have hx' : Real.exp (Real.pi/(2*|gamma|)) ∈ Ioo (1:ℝ) 2 := by
      simpa only [div_div] using hx
    have hy' : Real.exp (3*Real.pi/(2*|gamma|)) ∈ Ioo (1:ℝ) 2 := by
      simpa only [div_div] using hy
    by_cases hp : 0 < (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (Real.pi/(2*|gamma|)))).re
    · have hn : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
          (Real.exp (3*Real.pi/(2*|gamma|)))).re < 0 := by
        nlinarith
      exact ⟨_,_,hx',hy',hp,hn⟩
    · have hn : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
          (Real.exp (Real.pi/(2*|gamma|)))).re < 0 := by
        by_contra h
        have hz0 : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
            (Real.exp (Real.pi/(2*|gamma|)))).re = 0 := by linarith
        rw [hz0,zero_mul] at hxy
        exact (lt_irrefl _ hxy)
      have hp' : 0 < (z*coPoissonComplexDensity (coPoissonRho delta gamma)
          (Real.exp (3*Real.pi/(2*|gamma|)))).re := by nlinarith
      exact ⟨_,_,hy',hx',hp',hn⟩
  · obtain ⟨hu₀,hu₁,hx⟩ := hpoint Real.pi Real.pi_pos (by linarith [Real.pi_pos])
    obtain ⟨hv₀,hv₁,hy⟩ := hpoint (2*Real.pi) (by positivity) le_rfl
    have hxf := coPoisson_phase_formula delta gamma (Real.pi/|gamma|) z hgne hu₀ hu₁
    have hyf := coPoisson_phase_formula delta gamma (2*Real.pi/|gamma|) z hgne hv₀ hv₁
    have hsign : 0<Real.sinh (delta*(Real.pi/|gamma|))*
        Real.sinh (delta*(2*Real.pi/|gamma|)) := by
      rcases lt_or_gt_of_ne hdelta with hn | hp
      · exact mul_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr (mul_neg_of_neg_of_pos hn (by positivity)))
          (Real.sinh_neg_iff.mpr (mul_neg_of_neg_of_pos hn (by positivity)))
      · exact mul_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.sinh_pos_iff.mpr (by positivity))
    have hxy : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (Real.pi/|gamma|))).re *
      (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (2*Real.pi/|gamma|))).re < 0 := by
      rw [hxf,hyf]
      change (Real.exp _*(A.re*Real.sinh _*Real.cos _ -
        A.im*Real.cosh _*Real.sin _)) * (Real.exp _*(A.re*Real.sinh _*Real.cos _ -
        A.im*Real.cosh _*Real.sin _)) < 0
      rw [htrig Real.pi,htrig (2*Real.pi)]
      split_ifs <;> simp only [Real.cos_pi,Real.sin_pi,Real.cos_two_pi,Real.sin_two_pi,
        Real.cos_neg,Real.sin_neg,neg_zero,mul_zero,sub_zero,mul_one,mul_neg_one]
      all_goals
        have hpos : 0<Real.exp (-(Real.pi/|gamma|)/2)*
            Real.exp (-(2*Real.pi/|gamma|)/2)*A.re^2*
            (Real.sinh (delta*(Real.pi/|gamma|))*Real.sinh (delta*(2*Real.pi/|gamma|))) :=
          mul_pos (by positivity) hsign
        convert (neg_lt_zero.mpr hpos) using 1
        ring
    by_cases hp : 0 < (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (Real.pi/|gamma|))).re
    · have hn : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
          (Real.exp (2*Real.pi/|gamma|))).re < 0 := by nlinarith
      exact ⟨_,_,hx,hy,hp,hn⟩
    · have hn : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
          (Real.exp (Real.pi/|gamma|))).re < 0 := by
        by_contra h
        have hz0 : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
            (Real.exp (Real.pi/|gamma|))).re = 0 := by linarith
        rw [hz0,zero_mul] at hxy
        exact (lt_irrefl _ hxy)
      have hp' : 0 < (z*coPoissonComplexDensity (coPoissonRho delta gamma)
          (Real.exp (2*Real.pi/|gamma|))).re := by nlinarith
      exact ⟨_,_,hy,hx,hp',hn⟩

/-- Original sign root, with strict height conditions retained.  Its first
clause applies on AND off the critical line; the phase clause explicitly
requires nonzero off-line displacement. -/
theorem zero_measure_first_cell_sign (delta gamma : ℝ)
    (hheight : 3*Real.pi/(2*Real.log 2) < |gamma|) :
    (let u := 3*Real.pi/(2*|gamma|)
     0<u ∧ u<Real.log 2 ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)=
       -|gamma| *(1+1/(4*(delta^2+gamma^2)))*Real.exp (-u/2)*Real.cosh (delta*u) ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)<0) ∧
    (delta≠0 → 2*Real.pi/Real.log 2 < |gamma| → ∀ z : ℂ, z≠0 →
      ∃ x y : ℝ, x∈Ioo (1:ℝ) 2 ∧ y∈Ioo (1:ℝ) 2 ∧
        0<(z*coPoissonComplexDensity (coPoissonRho delta gamma) x).re ∧
        (z*coPoissonComplexDensity (coPoissonRho delta gamma) y).re<0) := by
  exact ⟨coPoisson_first_cell_negative_value delta gamma hheight,
    fun hd hh z hz => coPoisson_phase_both_signs delta gamma hd hh z hz⟩

/-! ### The renormalized co-Poisson tempered family (CP1.1-CP1.2) -/

section TemperedFamily
open scoped FourierTransform SchwartzMap

/-- A_t = D_t − e^(t/2) δ₀: the dilated comb with its origin atom removed. -/
def coPoissonA (t : ℝ) : TemperedDistribution ℝ ℂ :=
  dilatedCombDistribution t - ((Real.exp (t / 2) : ℝ) : ℂ) • TemperedDistribution.delta (0 : ℝ)

lemma coPoissonA_apply (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonA t φ = (Real.exp (t / 2) : ℂ) *
      ∑' n : ℤ, if n = 0 then 0 else φ (Real.exp t * n) := by
  have hs := dilatedComb_schwartz_summable t φ
  rw [coPoissonA, sub_apply, smul_apply,
    dilatedCombDistribution_apply, TemperedDistribution.delta_apply, hs.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, mul_zero, smul_eq_mul]
  ring

/-- The lattice constant Σ_(n ≠ 0) |n|^(-k) = 2ζ(k). -/
def latticeZetaConst (k : ℕ) : ℝ := ∑' n : ℤ, |(n : ℝ)| ^ (-(k : ℝ))

/-- |⟨A_t, φ⟩| ≤ (Σ_(n≠0) |n|^(-k)) p_k(φ) e^((1/2-k) t) for every real t and k ≥ 2. -/
lemma coPoissonA_norm_le (t : ℝ) (φ : 𝓢(ℝ, ℂ)) {k : ℕ} (hk : 2 ≤ k) :
    ‖coPoissonA t φ‖ ≤
      latticeZetaConst k * SchwartzMap.seminorm ℂ k 0 φ * Real.exp ((1 / 2 - k) * t) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  set S := SchwartzMap.seminorm ℂ k 0 φ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hterm (n : ℤ) : ‖(if n = 0 then (0 : ℂ) else φ (Real.exp t * n))‖ ≤
      S * Real.exp (-(k * t)) * |(n : ℝ)| ^ (-(k : ℝ)) := by
    by_cases hn : n = 0
    · subst hn
      simp only [if_true, norm_zero, Int.cast_zero, abs_zero]
      rw [Real.zero_rpow (ne_of_lt (by linarith : -(k : ℝ) < 0))]; simp
    · rw [if_neg hn]
      have hn' : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
      have hb := SchwartzMap.norm_pow_mul_le_seminorm ℂ φ k (Real.exp t * n)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos t), mul_pow] at hb
      have hpos : 0 < Real.exp t ^ k * |(n : ℝ)| ^ k := by positivity
      have hφ : ‖φ (Real.exp t * n)‖ ≤ S / (Real.exp t ^ k * |(n : ℝ)| ^ k) := by
        rw [le_div_iff₀ hpos]; linarith
      refine hφ.trans (le_of_eq ?_)
      rw [Real.rpow_neg hn'.le, Real.rpow_natCast, ← Real.exp_nat_mul, Real.exp_neg,
        div_eq_mul_inv, mul_inv]
      ring
  have hsum : Summable (fun n : ℤ => S * Real.exp (-(k * t)) * |(n : ℝ)| ^ (-(k : ℝ))) :=
    (Real.summable_abs_int_rpow hk1).mul_left _
  rw [coPoissonA_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have htsum := tsum_of_norm_bounded hsum.hasSum hterm
  rw [tsum_mul_left] at htsum
  calc Real.exp (t / 2) * ‖∑' n : ℤ, if n = 0 then (0 : ℂ) else φ (Real.exp t * n)‖
      ≤ Real.exp (t / 2) * (S * Real.exp (-(k * t)) * latticeZetaConst k) :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = latticeZetaConst k * S * Real.exp ((1 / 2 - k) * t) := by
        rw [show (1 / 2 - (k : ℝ)) * t = t / 2 + -(k * t) by ring, Real.exp_add]
        ring
lemma coPoissonA_term_continuous (φ : 𝓢(ℝ, ℂ)) (n : ℤ) :
    Continuous (fun t : ℝ => if n = 0 then (0 : ℂ) else φ (Real.exp t * n)) := by
  by_cases hn : n = 0
  · simp only [hn, if_true]; exact continuous_const
  · simp only [hn, if_false]
    exact φ.continuous.comp (Real.continuous_exp.mul continuous_const)

/-- t ↦ ⟨A_t, φ⟩ is continuous (locally uniform lattice convergence). -/
lemma coPoissonA_continuous (φ : 𝓢(ℝ, ℂ)) : Continuous (fun t : ℝ => coPoissonA t φ) := by
  have hS0 : 0 ≤ SchwartzMap.seminorm ℂ 2 0 φ := apply_nonneg _ _
  have hsum : Continuous (fun t : ℝ => ∑' n : ℤ,
      if n = 0 then (0 : ℂ) else φ (Real.exp t * n)) := by
    refine continuous_iff_continuousAt.mpr (fun t₀ => ?_)
    have hon : ContinuousOn (fun t : ℝ => ∑' n : ℤ,
        if n = 0 then (0 : ℂ) else φ (Real.exp t * n)) (Ioi (t₀ - 1)) := by
      refine continuousOn_tsum (fun n => (coPoissonA_term_continuous φ n).continuousOn)
        ((Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)).mul_left
          (SchwartzMap.seminorm ℂ 2 0 φ * Real.exp (-(2 * (t₀ - 1))))) (fun n t ht => ?_)
      by_cases hn : n = 0
      · subst hn; simp only [if_true, norm_zero, Int.cast_zero, abs_zero]
        rw [Real.zero_rpow (by norm_num)]; simp
      · rw [if_neg hn]
        have hn' : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
        have hb := SchwartzMap.norm_pow_mul_le_seminorm ℂ φ 2 (Real.exp t * n)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos t), mul_pow] at hb
        have hpos : 0 < Real.exp t ^ 2 * |(n : ℝ)| ^ 2 := by positivity
        have hφ : ‖φ (Real.exp t * n)‖ ≤ SchwartzMap.seminorm ℂ 2 0 φ /
            (Real.exp t ^ 2 * |(n : ℝ)| ^ 2) := by
          rw [le_div_iff₀ hpos]; linarith
        refine hφ.trans ?_
        rw [div_le_iff₀ hpos]
        have hexp : Real.exp (-(2 * (t₀ - 1))) * Real.exp t ^ 2 ≥ 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          exact Real.one_le_exp (by push_cast; nlinarith [show t₀ - 1 < t from ht])
        have hrp : |(n : ℝ)| ^ (-((2 : ℕ) : ℝ)) * |(n : ℝ)| ^ 2 = 1 := by
          rw [Real.rpow_neg hn'.le, Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
        calc SchwartzMap.seminorm ℂ 2 0 φ = SchwartzMap.seminorm ℂ 2 0 φ * 1 * 1 := by ring
          _ ≤ SchwartzMap.seminorm ℂ 2 0 φ * (Real.exp (-(2 * (t₀ - 1))) * Real.exp t ^ 2) *
              (|(n : ℝ)| ^ (-((2 : ℕ) : ℝ)) * |(n : ℝ)| ^ 2) := by
            rw [hrp]; gcongr
          _ = _ := by push_cast; ring
    exact hon.continuousAt (Ioi_mem_nhds (by linarith))
  have h : (fun t : ℝ => coPoissonA t φ) = fun t => (Real.exp (t / 2) : ℂ) *
      ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ (Real.exp t * n) := by
    funext t; exact coPoissonA_apply t φ
  rw [h]
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_id.div_const 2))).mul hsum

/-- The exponent choice making e^(-lamt) ⟨A_t, φ⟩ integrable at infinity. -/
def coPoissonOrder (lam : ℂ) : ℕ := 2 + Nat.ceil |lam.re|

lemma coPoissonOrder_two_le (lam : ℂ) : 2 ≤ coPoissonOrder lam := by
  unfold coPoissonOrder; omega

lemma coPoissonOrder_exponent_neg (lam : ℂ) :
    (1 / 2 - (coPoissonOrder lam : ℝ) - lam.re) < 0 := by
  unfold coPoissonOrder
  have h1 := Nat.le_ceil |lam.re|
  have h2 := neg_abs_le lam.re
  push_cast
  linarith

lemma norm_cexp_neg_mul_ofReal (lam : ℂ) (t : ℝ) :
    ‖cexp (-lam * t)‖ = Real.exp (-lam.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp

lemma coPoissonA_laplace_bound (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖cexp (-lam * t) * coPoissonA t φ‖ ≤
      latticeZetaConst (coPoissonOrder lam) * SchwartzMap.seminorm ℂ (coPoissonOrder lam) 0 φ *
        Real.exp ((1 / 2 - (coPoissonOrder lam : ℝ) - lam.re) * t) := by
  rw [norm_mul, norm_cexp_neg_mul_ofReal]
  have h := coPoissonA_norm_le t φ (coPoissonOrder_two_le lam)
  calc Real.exp (-lam.re * t) * ‖coPoissonA t φ‖
      ≤ Real.exp (-lam.re * t) * (latticeZetaConst (coPoissonOrder lam) *
          SchwartzMap.seminorm ℂ (coPoissonOrder lam) 0 φ *
          Real.exp ((1 / 2 - (coPoissonOrder lam : ℝ)) * t)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
        rw [show (1 / 2 - (coPoissonOrder lam : ℝ) - lam.re) * t =
          (1 / 2 - (coPoissonOrder lam : ℝ)) * t + -lam.re * t by ring, Real.exp_add]
        ring

lemma coPoissonA_laplace_integrable (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun t : ℝ => cexp (-lam * t) * coPoissonA t φ) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => latticeZetaConst (coPoissonOrder lam) *
      SchwartzMap.seminorm ℂ (coPoissonOrder lam) 0 φ *
        Real.exp ((1 / 2 - (coPoissonOrder lam : ℝ) - lam.re) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (coPoissonOrder_exponent_neg lam) 0).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall (fun t => coPoissonA_laplace_bound lam φ t))
  exact ((Complex.continuous_exp.comp ((continuous_const).mul
    Complex.continuous_ofReal)).mul (coPoissonA_continuous φ)).aestronglyMeasurable

/-- The Laplace pairing ∫_(0,∞) e^(-lam t) ⟨A_t, φ⟩ dt. -/
def coPoissonWfun (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * coPoissonA t φ

lemma coPoissonWfun_bound (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    ‖coPoissonWfun lam φ‖ ≤ (latticeZetaConst (coPoissonOrder lam) *
      ∫ t in Ioi 0, Real.exp ((1 / 2 - (coPoissonOrder lam : ℝ) - lam.re) * t)) *
        SchwartzMap.seminorm ℂ (coPoissonOrder lam) 0 φ := by
  have hg := (integrableOn_exp_mul_Ioi (coPoissonOrder_exponent_neg lam) 0).const_mul
    (latticeZetaConst (coPoissonOrder lam) * SchwartzMap.seminorm ℂ (coPoissonOrder lam) 0 φ)
  refine (norm_integral_le_of_norm_le hg
    (Eventually.of_forall (fun t => coPoissonA_laplace_bound lam φ t))).trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring

/-- W_lam as a genuine tempered distribution (continuity from the Schwartz seminorm bound). -/
def coPoissonW (lam : ℂ) : TemperedDistribution ℝ ℂ :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ <|
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (coPoissonWfun lam)
      (fun f g => by
        unfold coPoissonWfun
        simp_rw [map_add, mul_add]
        exact integral_add (coPoissonA_laplace_integrable lam f)
          (coPoissonA_laplace_integrable lam g))
      (fun a f => by
        unfold coPoissonWfun
        simp_rw [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext t; ring)
      ⟨{(coPoissonOrder lam, 0)}, latticeZetaConst (coPoissonOrder lam) *
        ∫ t in Ioi 0, Real.exp ((1 / 2 - (coPoissonOrder lam : ℝ) - lam.re) * t),
        by
          refine mul_nonneg ?_ (setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le))
          exact tsum_nonneg (fun n => Real.rpow_nonneg (abs_nonneg _) _),
        fun f => by
          rw [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
          exact coPoissonWfun_bound lam f⟩

lemma coPoissonW_apply (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonW lam φ = ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * coPoissonA t φ := rfl

/-- K_t = A_t + 𝓕 A_t. -/
def renormalizedCombKernel (t : ℝ) : TemperedDistribution ℝ ℂ := coPoissonA t + 𝓕 (coPoissonA t)

lemma renormalizedCombKernel_apply (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    renormalizedCombKernel t φ = coPoissonA t φ + coPoissonA t (𝓕 φ) := rfl

lemma schwartz_fourier_fourier_apply (φ : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (𝓕 φ) x = φ (-x) := by
  have h : 𝓕⁻ (𝓕 φ) = φ := FourierPair.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) φ
  rw [SchwartzMap.fourierInv_apply_eq] at h
  have h' := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ (-x)) h
  simpa using h'

lemma coPoissonA_fourier_fourier (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonA t (𝓕 (𝓕 φ)) = coPoissonA t φ := by
  have hD : dilatedCombDistribution t (𝓕 (𝓕 φ)) = dilatedCombDistribution t φ := by
    change (𝓕 (𝓕 (dilatedCombDistribution t))) φ = _
    rw [(dilated_comb_fourier t).2.2, (dilated_comb_fourier (-t)).2.2, neg_neg]
  rw [coPoissonA, sub_apply, sub_apply, smul_apply, smul_apply, hD,
    TemperedDistribution.delta_apply, TemperedDistribution.delta_apply,
    schwartz_fourier_fourier_apply, neg_zero]

/-- Every K_t is canonically Fourier self-dual. -/
theorem renormalizedCombKernel_fourier (t : ℝ) : 𝓕 (renormalizedCombKernel t) = renormalizedCombKernel t := by
  ext φ
  change renormalizedCombKernel t (𝓕 φ) = renormalizedCombKernel t φ
  rw [renormalizedCombKernel_apply, renormalizedCombKernel_apply, coPoissonA_fourier_fourier, add_comm]

lemma fourier_delta_zero_apply (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 (TemperedDistribution.delta (0 : ℝ))) φ = ∫ x, φ x := by
  change (𝓕 φ) 0 = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp

/-- The explicit cancellation form K_t = D_t + D_(-t) - e^(t/2)(δ₀ + dx). -/
theorem renormalizedCombKernel_eq (t : ℝ) : renormalizedCombKernel t = dilatedCombDistribution t +
    dilatedCombDistribution (-t) - ((Real.exp (t / 2) : ℝ) : ℂ) •
      (TemperedDistribution.delta (0 : ℝ) + 𝓕 (TemperedDistribution.delta (0 : ℝ))) := by
  ext φ
  have hD : dilatedCombDistribution t (𝓕 φ) = dilatedCombDistribution (-t) φ := by
    change (𝓕 (dilatedCombDistribution t)) φ = _
    rw [(dilated_comb_fourier t).2.2]
  rw [renormalizedCombKernel_apply, coPoissonA, sub_apply, sub_apply, smul_apply, smul_apply,
    hD, sub_apply, add_apply, smul_apply, add_apply]
  change _ = _ + _ - _ • (_ + (𝓕 φ) 0)
  rw [TemperedDistribution.delta_apply, TemperedDistribution.delta_apply]
  ring

/-- The renormalized co-Poisson family V_lam = ∫_0^∞ e^(-lam t) K_t dt. -/
def coPoissonFamily (lam : ℂ) : TemperedDistribution ℝ ℂ := coPoissonW lam + 𝓕 (coPoissonW lam)

lemma renormalizedCombKernel_laplace_integrable (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun t : ℝ => cexp (-lam * t) * renormalizedCombKernel t φ) (Ioi 0) := by
  have h := (coPoissonA_laplace_integrable lam φ).add (coPoissonA_laplace_integrable lam (𝓕 φ))
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, renormalizedCombKernel_apply]
  ring

theorem coPoissonFamily_apply (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily lam φ = ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * renormalizedCombKernel t φ := by
  rw [coPoissonFamily, add_apply]
  change coPoissonW lam φ + coPoissonW lam (𝓕 φ) = _
  rw [coPoissonW_apply, coPoissonW_apply, ← integral_add (coPoissonA_laplace_integrable lam φ)
    (coPoissonA_laplace_integrable lam (𝓕 φ))]
  congr 1
  funext t
  rw [renormalizedCombKernel_apply]
  ring

/-- V_lam is canonically Fourier self-dual for every lam. -/
theorem coPoissonFamily_fourier (lam : ℂ) : 𝓕 (coPoissonFamily lam) = coPoissonFamily lam := by
  ext φ
  change coPoissonFamily lam (𝓕 φ) = coPoissonFamily lam φ
  rw [coPoissonFamily_apply, coPoissonFamily_apply]
  congr 1
  funext t
  congr 1
  exact congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) (renormalizedCombKernel_fourier t)

/-- A Laplace transform over (0,∞) of a continuous function with all exponential decay
rates e^((1/2-k) t), k ≥ 2, is entire. -/
lemma laplace_entire {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ k : ℕ, 2 ≤ k → ∃ M : ℝ, ∀ t : ℝ, ‖f t‖ ≤ M * Real.exp ((1 / 2 - k) * t)) :
    Differentiable ℂ (fun lam : ℂ => ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * f t) := by
  intro lam0
  set N := coPoissonOrder lam0 with hN
  obtain ⟨M, hM⟩ := hb (N + 2) (by have := coPoissonOrder_two_le lam0; omega)
  have hneg := coPoissonOrder_exponent_neg lam0
  set c : ℝ := 1 / 2 - (N : ℝ) - lam0.re with hc
  have hcont (lam : ℂ) : Continuous (fun t : ℝ => cexp (-lam * t) * f t) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul hf
  have hF'cont : Continuous (fun t : ℝ => -(t : ℂ) * cexp (-lam0 * t) * f t) :=
    (Complex.continuous_ofReal.neg.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).mul hf
  have hbound_int : Integrable (fun t : ℝ => M * Real.exp (c * t)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul M
  have hMnn (t : ℝ) : 0 ≤ M * Real.exp ((1 / 2 - ((N + 2 : ℕ) : ℝ)) * t) :=
    (norm_nonneg _).trans (hM t)
  have hderiv_bound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))), ∀ lam ∈ Metric.ball lam0 1,
      ‖-(t : ℂ) * cexp (-lam * t) * f t‖ ≤ M * Real.exp (c * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht lam hlam
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hre : lam0.re - 1 ≤ lam.re := by
      have h1 : |lam.re - lam0.re| ≤ ‖lam - lam0‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : ‖lam - lam0‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hlam
      linarith [abs_le.mp h1]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
      norm_cexp_neg_mul_ofReal]
    have hte : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hexp : Real.exp (-lam.re * t) ≤ Real.exp ((1 - lam0.re) * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) ht0)
    calc t * Real.exp (-lam.re * t) * ‖f t‖
        ≤ Real.exp t * Real.exp ((1 - lam0.re) * t) *
            (M * Real.exp ((1 / 2 - ((N + 2 : ℕ) : ℝ)) * t)) :=
          mul_le_mul (mul_le_mul hte hexp (Real.exp_pos _).le (Real.exp_pos _).le) (hM t)
            (norm_nonneg _) (by positivity)
      _ = M * Real.exp (c * t) := by
          rw [← mul_assoc, mul_comm _ M, mul_assoc M, ← Real.exp_add, ← Real.exp_add]
          congr 2
          rw [hc]; push_cast; ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun lam t => cexp (-lam * t) * f t)
    (F' := fun lam t => -(t : ℂ) * cexp (-lam * t) * f t) (x₀ := lam0)
    (bound := fun t => M * Real.exp (c * t)) (Metric.ball_mem_nhds lam0 one_pos)
    (Eventually.of_forall (fun lam => (hcont lam).aestronglyMeasurable))
    (by
      refine hbound_int.mono' (hcont lam0).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have h := hderiv_bound
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      rw [norm_mul, norm_cexp_neg_mul_ofReal]
      calc Real.exp (-lam0.re * t) * ‖f t‖
          ≤ Real.exp (-lam0.re * t) * (M * Real.exp ((1 / 2 - ((N + 2 : ℕ) : ℝ)) * t)) :=
            mul_le_mul_of_nonneg_left (hM t) (Real.exp_pos _).le
        _ ≤ Real.exp (-lam0.re * t) * (M * Real.exp ((1 / 2 - ((N + 2 : ℕ) : ℝ)) * t)) *
              Real.exp (2 * t) := le_mul_of_one_le_right (by positivity [hMnn t])
                (Real.one_le_exp (by linarith))
        _ = M * Real.exp (c * t) := by
            rw [mul_comm (Real.exp _) (M * _), mul_assoc M, mul_assoc M, ← Real.exp_add,
              ← Real.exp_add]
            congr 2
            rw [hc]; push_cast; ring)
    hF'cont.aestronglyMeasurable hderiv_bound hbound_int
    (Eventually.of_forall (fun t lam _ => by
      have h1 : HasDerivAt (fun lam : ℂ => -lam * (t : ℂ)) (-(t : ℂ)) lam := by
        simpa using ((hasDerivAt_id lam).neg.mul_const (t : ℂ))
      have h2 := h1.cexp.mul_const (f t)
      exact h2.congr_deriv (by ring)))
  exact key.2.differentiableAt

lemma renormalizedCombKernel_continuous (φ : 𝓢(ℝ, ℂ)) : Continuous (fun t : ℝ => renormalizedCombKernel t φ) :=
  (coPoissonA_continuous φ).add (coPoissonA_continuous (𝓕 φ))

lemma renormalizedCombKernel_norm_le (t : ℝ) (φ : 𝓢(ℝ, ℂ)) {k : ℕ} (hk : 2 ≤ k) :
    ‖renormalizedCombKernel t φ‖ ≤ latticeZetaConst k *
      (SchwartzMap.seminorm ℂ k 0 φ + SchwartzMap.seminorm ℂ k 0 (𝓕 φ)) *
        Real.exp ((1 / 2 - k) * t) := by
  rw [renormalizedCombKernel_apply]
  refine (norm_add_le _ _).trans ?_
  have h1 := coPoissonA_norm_le t φ hk
  have h2 := coPoissonA_norm_le t (𝓕 φ) hk
  nlinarith [h1, h2]

/-- The renormalized family is entire in lam on every Schwartz test. -/
theorem coPoissonFamily_entire (φ : 𝓢(ℝ, ℂ)) : Differentiable ℂ (fun lam : ℂ => coPoissonFamily lam φ) := by
  have h := laplace_entire (renormalizedCombKernel_continuous φ) (fun k hk =>
    ⟨_, fun t => renormalizedCombKernel_norm_le t φ hk⟩)
  simpa only [coPoissonFamily_apply] using h

/-- Reflection x ↦ -x on Schwartz tests. -/
def schwartzReflect (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) φ

lemma schwartzReflect_apply (φ : 𝓢(ℝ, ℂ)) (x : ℝ) : schwartzReflect φ x = φ (-x) := rfl

lemma fourier_schwartzReflect (φ : 𝓢(ℝ, ℂ)) : 𝓕 (schwartzReflect φ) = schwartzReflect (𝓕 φ) := by
  have h : 𝓕⁻ φ = schwartzReflect (𝓕 φ) := SchwartzMap.fourierInv_apply_eq φ
  rw [← h]
  ext x
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_comp_neg]
  rfl

lemma coPoissonA_reflect (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonA t (schwartzReflect φ) = coPoissonA t φ := by
  rw [coPoissonA_apply, coPoissonA_apply]
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply, neg_eq_zero, schwartzReflect_apply, Int.cast_neg, mul_neg, neg_neg]

/-- Every K_t is even. -/
lemma renormalizedCombKernel_reflect (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    renormalizedCombKernel t (schwartzReflect φ) = renormalizedCombKernel t φ := by
  rw [renormalizedCombKernel_apply, renormalizedCombKernel_apply, fourier_schwartzReflect, coPoissonA_reflect,
    coPoissonA_reflect]

lemma coPoissonFamily_reflect (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily lam (schwartzReflect φ) = coPoissonFamily lam φ := by
  rw [coPoissonFamily_apply, coPoissonFamily_apply]
  simp_rw [renormalizedCombKernel_reflect]

lemma latticeZeta_nat_term {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    |((n : ℤ) : ℝ)| ^ (-(k : ℝ)) = 1 / (n : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    simp only [Nat.cast_zero, Int.cast_zero, abs_zero]
    rw [Real.zero_rpow (by linarith), zero_pow (by omega : k ≠ 0), div_zero]
  · rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _),
      Real.rpow_natCast, one_div]

lemma latticeZeta_neg_term (k : ℕ) (n : ℕ) :
    |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| ^ (-(k : ℝ)) = 1 / ((n : ℝ) + 1) ^ k := by
  have h : (((-((n : ℤ) + 1) : ℤ)) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
  rw [h, abs_neg, abs_of_pos (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
    one_div]

lemma summable_one_div_nat_pow' {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
  Real.summable_one_div_nat_pow.mpr (by omega)

/-- The lattice constant is 2ζ(k), as in the paper's estimate. -/
lemma latticeZetaConst_eq {k : ℕ} (hk : 2 ≤ k) :
    ((latticeZetaConst k : ℝ) : ℂ) = 2 * riemannZeta k := by
  have hs := summable_one_div_nat_pow' hk
  have hs1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ k) := by
    have := (summable_nat_add_iff 1).mpr hs
    simpa only [Nat.cast_add, Nat.cast_one] using this
  have hnat : Summable (fun n : ℕ => |((n : ℤ) : ℝ)| ^ (-(k : ℝ))) :=
    hs.congr (fun n => (latticeZeta_nat_term hk n).symm)
  have hneg : Summable (fun n : ℕ => |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| ^ (-(k : ℝ))) :=
    hs1.congr (fun n => (latticeZeta_neg_term k n).symm)
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun m : ℤ => |(m : ℝ)| ^ (-(k : ℝ))) hnat hneg
  have hshift : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k = ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
    rw [hs.tsum_eq_zero_add, Nat.cast_zero, zero_pow (by omega : k ≠ 0), div_zero, zero_add]
    simp only [Nat.cast_add, Nat.cast_one]
  have hz : ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) = riemannZeta k := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega), Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hL : latticeZetaConst k = 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
    unfold latticeZetaConst
    rw [hsplit, tsum_congr (latticeZeta_nat_term hk), tsum_congr (latticeZeta_neg_term k), hshift]
    ring
  rw [hL, Complex.ofReal_mul, hz]
  norm_num


/-- Original R1-CP1 root: the renormalized co-Poisson family. For t ≥ 0 the kernel
K_t = A_t + 𝓕 A_t with A_t = D_t - e^(t/2) δ₀ equals D_t + D_(-t) - e^(t/2)(δ₀ + dx), where
𝓕 δ₀ is the Lebesgue functional. The origin atom is cancelled before integration: ⟨A_t, φ⟩ is
the lattice sum without its n = 0 term and decays like 2ζ(k) p_k(φ) e^((1/2-k) t) for every
k ≥ 2. Hence V_lam = ∫_0^∞ e^(-lam t) K_t dt is an actual tempered distribution for every
complex lam, given by absolutely convergent Schwartz-test integrals, entire in lam on every
test, even and canonically Fourier self-dual, as is every K_t. -/
theorem renormalized_copoisson_tempered_family :
    (∀ t : ℝ, renormalizedCombKernel t = dilatedCombDistribution t +
      dilatedCombDistribution (-t) - ((Real.exp (t / 2) : ℝ) : ℂ) •
        (TemperedDistribution.delta (0 : ℝ) + 𝓕 (TemperedDistribution.delta (0 : ℝ)))) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 (TemperedDistribution.delta (0 : ℝ))) φ = ∫ x, φ x) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)), coPoissonA t φ = (Real.exp (t / 2) : ℂ) *
      ∑' n : ℤ, if n = 0 then 0 else φ (Real.exp t * n)) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ), 2 ≤ k → ‖coPoissonA t φ‖ ≤
      latticeZetaConst k * SchwartzMap.seminorm ℂ k 0 φ * Real.exp ((1 / 2 - k) * t)) ∧
    (∀ k : ℕ, 2 ≤ k → ((latticeZetaConst k : ℝ) : ℂ) = 2 * riemannZeta k) ∧
    (∀ t : ℝ, 𝓕 (renormalizedCombKernel t) = renormalizedCombKernel t) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)),
      renormalizedCombKernel t (schwartzReflect φ) = renormalizedCombKernel t φ) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)),
      IntegrableOn (fun t : ℝ => cexp (-lam * t) * renormalizedCombKernel t φ) (Set.Ioi 0)) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)), coPoissonFamily lam φ =
      ∫ t in Set.Ioi (0 : ℝ), cexp (-lam * t) * renormalizedCombKernel t φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), Differentiable ℂ (fun lam : ℂ => coPoissonFamily lam φ)) ∧
    (∀ lam : ℂ, 𝓕 (coPoissonFamily lam) = coPoissonFamily lam) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)),
      coPoissonFamily lam (schwartzReflect φ) = coPoissonFamily lam φ) :=
  ⟨renormalizedCombKernel_eq, fourier_delta_zero_apply, coPoissonA_apply,
    fun t φ _ hk => coPoissonA_norm_le t φ hk, fun _ hk => latticeZetaConst_eq hk,
    renormalizedCombKernel_fourier, renormalizedCombKernel_reflect,
    renormalizedCombKernel_laplace_integrable, coPoissonFamily_apply, coPoissonFamily_entire,
    coPoissonFamily_fourier, coPoissonFamily_reflect⟩

end TemperedFamily

section OrderZero
open scoped ENNReal NNReal SchwartzMap FourierTransform

/-- Finite power sums against the Euler–Maclaurin form of ζ (Re s > 0, s ≠ 1). -/
lemma partialZeta_eq {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) = riemannZeta s + (N : ℂ) ^ (1 - s) / (1 - s) +
      (N : ℂ) ^ (-s) / 2 - s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have h := Zeta0EqZeta (N := N) (by omega) hσ hs1
  rw [riemannZeta0] at h
  have hrange : ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_add_one_right_eq_Icc]
    simp only [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, zero_add]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.cpow_neg, one_div]
  rw [hrange] at h
  rw [← h]
  ring

lemma partialZeta_error_nat {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s‖ ≤
      (1 / 2 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  rw [partialZeta_eq hσ hs1 hN]
  have hint := ZetaBnd_aux1b N hN (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNs : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp
  calc ‖riemannZeta s + (N : ℂ) ^ (1 - s) / (1 - s) + (N : ℂ) ^ (-s) / 2 -
        s * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)) -
        (N : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s‖
      = ‖(N : ℂ) ^ (-s) / 2 - s * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1))‖ := by
        ring_nf
    _ ≤ ‖(N : ℂ) ^ (-s) / 2‖ + ‖s‖ * ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ (N : ℝ) ^ (-s.re) / 2 + ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := by
        rw [norm_div, hNs]
        gcongr
        simp
    _ = _ := by ring

/-- (CP1.6) for real X ≥ 1: Σ_(n≤X) n^(-s) = X^(1-s)/(1-s) + ζ(s) + O(⌊X⌋^(-Re s)). -/
lemma partialZeta_error {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n : ℂ) ^ (-s) - (X : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s‖ ≤
      (3 / 2 + ‖s‖ / s.re) * ((⌊X⌋₊ : ℕ) : ℝ) ^ (-s.re) := by
  set N := ⌊X⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hX)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hXN : X - N < 1 := by have := Nat.lt_floor_add_one X; linarith
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hmvt : ‖(X : ℂ) ^ (1 - s) / (1 - s) - (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤
      (N : ℝ) ^ (-s.re) := by
    have hderiv : ∀ u ∈ Icc (N : ℝ) X, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s))
        ((u : ℂ) ^ (-s)) (Icc (N : ℝ) X) u := by
      intro u hu
      have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hNpos hu.1)
      have h := (hasDerivAt_ofReal_cpow_const hu0 hs1').div_const (1 - s)
      have heq : (1 - s) * (u : ℂ) ^ (1 - s - 1) / (1 - s) = (u : ℂ) ^ (-s) := by
        rw [show (1 : ℂ) - s - 1 = -s by ring]; field_simp
      rw [heq] at h
      exact h.hasDerivWithinAt
    have hbound : ∀ u ∈ Ico (N : ℝ) X, ‖(u : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ (-s.re) := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hNpos hu.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.neg_re]
      exact Real.rpow_le_rpow_of_nonpos hNpos hu.1 (by linarith)
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound X ⟨hNX, le_rfl⟩
    refine h.trans ?_
    have hpos : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
    nlinarith
  have hnat := partialZeta_error_nat hσ hs1 hN
  calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (X : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s‖
      = ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s) -
          ((X : ℂ) ^ (1 - s) / (1 - s) - (N : ℂ) ^ (1 - s) / (1 - s))‖ := by ring_nf
    _ ≤ (1 / 2 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) + (N : ℝ) ^ (-s.re) :=
        (norm_sub_le _ _).trans (add_le_add hnat hmvt)
    _ = _ := by ring

/-- ⌊X⌋^(-σ) ≤ 2^σ X^(-σ) for X ≥ 1 and σ ≥ 0. -/
lemma floor_rpow_neg_le {X σ : ℝ} (hX : 1 ≤ X) (hσ : 0 ≤ σ) :
    ((⌊X⌋₊ : ℕ) : ℝ) ^ (-σ) ≤ 2 ^ σ * X ^ (-σ) := by
  have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
  have hNpos : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast hN
  have hhalf : X / 2 ≤ (⌊X⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one X
    have h2 : (1 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hN
    linarith
  calc ((⌊X⌋₊ : ℕ) : ℝ) ^ (-σ) ≤ (X / 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hhalf (by linarith)
    _ = 2 ^ σ * X ^ (-σ) := by
        rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        field_simp

/-! ### Complex measures from a locally integrable density and an origin atom -/

lemma isLocallyFinite_withDensity_ofReal {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    IsLocallyFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, hint⟩ := hf x
  refine ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
  rw [withDensity_apply _ isOpen_interior.measurableSet]
  refine lt_of_le_of_lt (lintegral_mono_set interior_subset) ?_
  refine lt_of_le_of_lt (lintegral_mono (fun y => ?_)) hint.2
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- Density part plus atom c at the origin, as a positive measure. -/
def densityAtomPart (f : ℝ → ℝ) (a : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x)) + ENNReal.ofReal a • Measure.dirac 0

lemma isLocallyFinite_densityAtomPart {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (a : ℝ) :
    IsLocallyFiniteMeasure (densityAtomPart f a) := by
  have := isLocallyFinite_withDensity_ofReal hf
  have : IsFiniteMeasure (ENNReal.ofReal a • Measure.dirac (0 : ℝ)) := ⟨by simp⟩
  unfold densityAtomPart
  infer_instance

lemma locallyIntegrable_complex_re {g : ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun x => (g x).re) volume := by
  intro x
  obtain ⟨U, hU, hint⟩ := hg x
  exact ⟨U, hU, hint.re⟩

lemma locallyIntegrable_complex_im {g : ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun x => (g x).im) volume := by
  intro x
  obtain ⟨U, hU, hint⟩ := hg x
  exact ⟨U, hU, hint.im⟩

/-- The genuine locally finite complex measure g dx + c δ₀, with canonical Jordan pairs. -/
def densityAtomMeasure (g : ℝ → ℂ) (c : ℂ) (hg : LocallyIntegrable g volume) :
    LocallyFiniteComplexMeasure :=
  haveI := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_re hg) c.re
  haveI := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_re hg).neg (-c.re)
  haveI := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_im hg) c.im
  haveI := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_im hg).neg (-c.im)
  ⟨localJordanDifference (densityAtomPart (fun x => (g x).re) c.re)
      (densityAtomPart (fun x => -(g x).re) (-c.re)),
    localJordanDifference (densityAtomPart (fun x => (g x).im) c.im)
      (densityAtomPart (fun x => -(g x).im) (-c.im))⟩

lemma lintegral_ofReal_lt_top_of_integrableOn {f : ℝ → ℝ} {A : Set ℝ}
    (hint : IntegrableOn f A volume) : ∫⁻ x in A, ENNReal.ofReal (f x) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hint.2
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

lemma densityAtomPart_toReal_sub {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (a : ℝ)
    {K A : Set ℝ} (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A ⊆ K) :
    (densityAtomPart f a A).toReal - (densityAtomPart (fun x => -f x) (-a) A).toReal =
      (∫ x in A, f x) + A.indicator (fun _ => a) 0 := by
  have hint : IntegrableOn f A volume := (hf.integrableOn_isCompact hK).mono_set hAK
  have h1 := lintegral_ofReal_lt_top_of_integrableOn hint
  have h2 : ∫⁻ x in A, ENNReal.ofReal (-f x) < ⊤ := lintegral_ofReal_lt_top_of_integrableOn hint.neg
  have hdirac (b : ℝ) : (ENNReal.ofReal b • Measure.dirac (0 : ℝ)) A =
      ENNReal.ofReal (A.indicator (fun _ => b) 0) := by
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    by_cases h0 : (0 : ℝ) ∈ A
    · simp [Set.indicator_of_mem h0]
    · simp [Set.indicator_of_notMem h0]
  unfold densityAtomPart
  beta_reduce
  rw [Measure.add_apply, Measure.add_apply, withDensity_apply _ hA, withDensity_apply _ hA,
    hdirac, hdirac, ENNReal.toReal_add h1.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_add h2.ne ENNReal.ofReal_ne_top,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  by_cases h0 : (0 : ℝ) ∈ A
  · simp only [Set.indicator_of_mem h0, ENNReal.toReal_ofReal']
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0)]; ring
    · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a)]; ring
  · simp only [Set.indicator_of_notMem h0, ENNReal.ofReal_zero, ENNReal.toReal_zero]
    ring

/-- The value of the compact restriction of g dx + c δ₀ on a measurable set. -/
lemma densityAtomMeasure_compactRestriction_apply (g : ℝ → ℂ) (c : ℂ)
    (hg : LocallyIntegrable g volume) {K : Set ℝ} (hK : IsCompact K) {E : Set ℝ}
    (hE : MeasurableSet E) :
    (densityAtomMeasure g c hg).compactRestriction K hK E =
      (∫ x in E ∩ K, g x) + (E ∩ K).indicator (fun _ => c) 0 := by
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_re hg) c.re
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_re hg).neg (-c.re)
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_im hg) c.im
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_im hg).neg (-c.im)
  have hEK : MeasurableSet (E ∩ K) := hE.inter hK.measurableSet
  have hgint : IntegrableOn g (E ∩ K) volume :=
    (hg.integrableOn_isCompact hK).mono_set inter_subset_right
  have hre := densityAtomPart_toReal_sub (locallyIntegrable_complex_re hg) c.re hK hEK
    inter_subset_right
  have him := densityAtomPart_toReal_sub (locallyIntegrable_complex_im hg) c.im hK hEK
    inter_subset_right
  apply Complex.ext
  · change (ComplexMeasure.re ((densityAtomMeasure g c hg).compactRestriction K hK)) E = _
    rw [LocallyFiniteComplexMeasure.compactRestriction_re]
    change localSignedCompactRestriction (localJordanDifference _ _) K hK E = _
    rw [localJordanDifference_compactRestriction]
    simp only [sub_apply, Measure.toSignedMeasure_apply_measurable hE]
    rw [Measure.real, Measure.real, Measure.restrict_apply hE, Measure.restrict_apply hE,
      hre, Complex.add_re]
    have hint_re : (∫ x in E ∩ K, g x).re = ∫ x in E ∩ K, (g x).re := by
      have := integral_re hgint
      simpa using this.symm
    rw [hint_re]
    by_cases h0 : (0 : ℝ) ∈ E ∩ K
    · simp [Set.indicator_of_mem h0]
    · simp [Set.indicator_of_notMem h0]
  · change (ComplexMeasure.im ((densityAtomMeasure g c hg).compactRestriction K hK)) E = _
    rw [LocallyFiniteComplexMeasure.compactRestriction_im]
    change localSignedCompactRestriction (localJordanDifference _ _) K hK E = _
    rw [localJordanDifference_compactRestriction]
    simp only [sub_apply, Measure.toSignedMeasure_apply_measurable hE]
    rw [Measure.real, Measure.real, Measure.restrict_apply hE, Measure.restrict_apply hE,
      him, Complex.add_im]
    have hint_im : (∫ x in E ∩ K, g x).im = ∫ x in E ∩ K, (g x).im := by
      have := integral_im hgint
      simpa using this.symm
    rw [hint_im]
    by_cases h0 : (0 : ℝ) ∈ E ∩ K
    · simp [Set.indicator_of_mem h0]
    · simp [Set.indicator_of_notMem h0]

/-- Local variation of a difference of two density-plus-atom measures on a compact window. -/
lemma densityAtom_variation_diff_le {g₁ g₂ : ℝ → ℂ} {c₁ c₂ : ℂ}
    (hg₁ : LocallyIntegrable g₁ volume) (hg₂ : LocallyIntegrable g₂ volume)
    {K : Set ℝ} (hK : IsCompact K) :
    ((densityAtomMeasure g₁ c₁ hg₁).compactRestriction K hK -
        (densityAtomMeasure g₂ c₂ hg₂).compactRestriction K hK).variation.real univ ≤
      (∫ x in K, ‖g₁ x - g₂ x‖) + ‖c₁ - c₂‖ := by
  have hi₁ : IntegrableOn g₁ K volume := hg₁.integrableOn_isCompact hK
  have hi₂ : IntegrableOn g₂ K volume := hg₂.integrableOn_isCompact hK
  have hid : IntegrableOn (fun x => g₁ x - g₂ x) K volume := hi₁.sub hi₂
  set m : Measure ℝ := (volume.restrict K).withDensity (fun x => ‖g₁ x - g₂ x‖ₑ) +
    ‖c₁ - c₂‖ₑ • Measure.dirac 0 with hm
  have hle : ((densityAtomMeasure g₁ c₁ hg₁).compactRestriction K hK -
      (densityAtomMeasure g₂ c₂ hg₂).compactRestriction K hK).variation ≤ m := by
    refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
    rw [sub_apply, densityAtomMeasure_compactRestriction_apply _ _ _ hK hE,
      densityAtomMeasure_compactRestriction_apply _ _ _ hK hE]
    have hEK : MeasurableSet (E ∩ K) := hE.inter hK.measurableSet
    have h1 : (∫ x in E ∩ K, g₁ x) + (E ∩ K).indicator (fun _ => c₁) 0 -
        ((∫ x in E ∩ K, g₂ x) + (E ∩ K).indicator (fun _ => c₂) 0) =
        (∫ x in E ∩ K, (g₁ x - g₂ x)) + (E ∩ K).indicator (fun _ => c₁ - c₂) 0 := by
      rw [integral_sub (hi₁.mono_set inter_subset_right) (hi₂.mono_set inter_subset_right)]
      by_cases h0 : (0 : ℝ) ∈ E ∩ K
      · simp only [Set.indicator_of_mem h0]; ring
      · simp only [Set.indicator_of_notMem h0]; ring
    rw [h1]
    refine (enorm_add_le _ _).trans ?_
    rw [hm, Measure.add_apply, withDensity_apply _ hE, Measure.restrict_restrict hE,
      Measure.smul_apply, Measure.dirac_apply' _ hE, smul_eq_mul]
    refine add_le_add (enorm_integral_le_lintegral_enorm _) ?_
    by_cases h0 : (0 : ℝ) ∈ E ∩ K
    · rw [Set.indicator_of_mem h0, Set.indicator_of_mem h0.1]; simp
    · rw [Set.indicator_of_notMem h0, enorm_zero]; exact zero_le
  have hmfin : m univ ≠ ⊤ := by
    rw [hm, Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    refine ENNReal.add_ne_top.mpr ⟨hid.2.ne, ?_⟩
    simp
  calc ((densityAtomMeasure g₁ c₁ hg₁).compactRestriction K hK -
        (densityAtomMeasure g₂ c₂ hg₂).compactRestriction K hK).variation.real univ
      ≤ (m univ).toReal := ENNReal.toReal_mono hmfin (hle univ)
    _ = (∫ x in K, ‖g₁ x - g₂ x‖) + ‖c₁ - c₂‖ := by
        rw [hm, Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          ENNReal.toReal_add hid.2.ne (by simp), integral_norm_eq_lintegral_enorm
            hid.aestronglyMeasurable]
        simp

/-! ### Cutoff and limit densities (CP1.3-CP1.5) -/

/-- S_ρ, the paper's finite-sum function (inclusive right integer endpoint). -/
abbrev finiteSumSrho (ρ : ℂ) (x : ℝ) : ℂ := coPoissonPowerSums ρ x

/-- Density of the T-cutoff of (CP1.2) at x (even in x): the two lattice-ray families
x^(-ρ) Σ_(x e^(-T) ≤ n ≤ x) n^(ρ-1) and x^(ρ-1) Σ_(x < n ≤ x e^T) n^(-ρ), minus the
integrated continuum (e^((1-ρ)T) - 1)/(1-ρ). -/
def coPoissonCutoffDensity (ρ : ℂ) (T : ℝ) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (-ρ) *
      ∑ n ∈ Finset.Icc (max 1 ⌈|x| * Real.exp (-T)⌉₊) ⌊|x|⌋₊, (n : ℂ) ^ (ρ - 1) +
    ((|x| : ℝ) : ℂ) ^ (ρ - 1) * ∑ n ∈ Finset.Ioc ⌊|x|⌋₊ ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) -
    (cexp ((1 - ρ) * T) - 1) / (1 - ρ)

/-- Origin atom of the T-cutoff: ∫_0^T e^(-ρ t) dt. -/
def coPoissonCutoffAtom (ρ : ℂ) (T : ℝ) : ℂ := (1 - cexp (-ρ * T)) / ρ

/-- The limit density S_ρ(|x|) + ζ(ρ)|x|^(ρ-1) + 1/(1-ρ) of (CP1.4). -/
def coPoissonLimitDensity (ρ : ℂ) (x : ℝ) : ℂ :=
  finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ)

lemma Icc_one_eq_Ioc_zero (a : ℕ) : Finset.Icc 1 a = Finset.Ioc 0 a := by
  ext n; simp; omega

/-- Near the origin both lattice families are empty. -/
lemma coPoissonCutoff_sub_limit_small {ρ : ℂ} {T x : ℝ} (hT : 0 ≤ T)
    (hx : |x| * Real.exp T < 1) :
    coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x =
      -(cexp ((1 - ρ) * T) / (1 - ρ)) - riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) := by
  have hx1 : |x| < 1 := by
    have : 1 ≤ Real.exp T := Real.one_le_exp hT
    nlinarith [abs_nonneg x]
  have hf0 : ⌊|x|⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
  have hf1 : ⌊|x| * Real.exp T⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  have hempty : Finset.Icc (max 1 ⌈|x| * Real.exp (-T)⌉₊) 0 = ∅ :=
    Finset.Icc_eq_empty (by omega)
  unfold coPoissonCutoffDensity coPoissonLimitDensity finiteSumSrho coPoissonPowerSums
  rw [hf0, hf1, hempty]
  simp only [Finset.sum_empty, Finset.Ioc_self, Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1)]
  field_simp
  ring

/-- Away from the origin the first family stabilizes and the second telescopes into the
finite power sum up to X = |x| e^T. -/
lemma coPoissonCutoff_sub_limit_main {ρ : ℂ} {T x : ℝ} (hT : 0 ≤ T) (hx0 : 0 < |x|)
    (hx2 : |x| * Real.exp (-T) ≤ 1) :
    coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x =
      ((|x| : ℝ) : ℂ) ^ (ρ - 1) *
        (∑ n ∈ Finset.Icc 1 ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) -
          (((|x| * Real.exp T : ℝ)) : ℂ) ^ (1 - ρ) / (1 - ρ) - riemannZeta ρ) := by
  have hceil : max 1 ⌈|x| * Real.exp (-T)⌉₊ = 1 :=
    max_eq_left (Nat.ceil_le.mpr (by simpa using hx2))
  have hle : ⌊|x|⌋₊ ≤ ⌊|x| * Real.exp T⌋₊ :=
    Nat.floor_le_floor (le_mul_of_one_le_right (abs_nonneg x) (Real.one_le_exp hT))
  have hsplit : ∑ n ∈ Finset.Ioc ⌊|x|⌋₊ ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Finset.Icc 1 ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) -
        ∑ n ∈ Finset.Icc 1 ⌊|x|⌋₊, (n : ℂ) ^ (-ρ) := by
    rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle]
    ring
  have hpow : ((|x| : ℝ) : ℂ) ^ (ρ - 1) * (((|x| * Real.exp T : ℝ)) : ℂ) ^ (1 - ρ) =
      cexp ((1 - ρ) * T) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg x) (Real.exp_pos T).le,
      ← mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast hx0.ne'),
      show ρ - 1 + (1 - ρ) = 0 by ring, Complex.cpow_zero, one_mul,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos T).ne'),
      ← Complex.ofReal_log (Real.exp_pos T).le, Real.log_exp]
    ring_nf
  unfold coPoissonCutoffDensity coPoissonLimitDensity finiteSumSrho coPoissonPowerSums
  have h1 : ((|x| : ℝ) : ℂ) ^ (ρ - 1) * ((((|x| * Real.exp T : ℝ)) : ℂ) ^ (1 - ρ) / (1 - ρ)) =
      cexp ((1 - ρ) * T) / (1 - ρ) := by rw [← mul_div_assoc, hpow]
  rw [hceil, hsplit]
  linear_combination h1

/-! ### Measurability and local integrability -/

lemma measurable_abs_cpow (c : ℂ) : Measurable (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ c) :=
  (Complex.measurable_ofReal.comp continuous_abs.measurable).pow_const c

lemma measurable_natPair_sum (F : ℕ × ℕ → ℂ) {a b : ℝ → ℝ} (ha : Measurable a)
    (hb : Measurable b) : Measurable (fun x => F (⌈a x⌉₊, ⌊b x⌋₊)) :=
  (measurable_of_countable F).comp ((Nat.measurable_ceil.comp ha).prodMk (Nat.measurable_floor.comp hb))

lemma measurable_natPair_sum' (F : ℕ × ℕ → ℂ) {a b : ℝ → ℝ} (ha : Measurable a)
    (hb : Measurable b) : Measurable (fun x => F (⌊a x⌋₊, ⌊b x⌋₊)) :=
  (measurable_of_countable F).comp ((Nat.measurable_floor.comp ha).prodMk (Nat.measurable_floor.comp hb))

lemma measurable_coPoissonCutoffDensity (ρ : ℂ) (T : ℝ) :
    Measurable (coPoissonCutoffDensity ρ T) := by
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have h1 := measurable_natPair_sum
    (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc (max 1 p.1) p.2, (n : ℂ) ^ (ρ - 1))
    (habs.mul_const (Real.exp (-T))) habs
  have h2 := measurable_natPair_sum'
    (fun p : ℕ × ℕ => ∑ n ∈ Finset.Ioc p.1 p.2, (n : ℂ) ^ (-ρ))
    habs (habs.mul_const (Real.exp T))
  exact (((measurable_abs_cpow _).mul h1).add ((measurable_abs_cpow _).mul h2)).sub_const _

lemma measurable_coPoissonLimitDensity (ρ : ℂ) : Measurable (coPoissonLimitDensity ρ) := by
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have h1 := measurable_natPair_sum'
    (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (n : ℂ) ^ (ρ - 1)) habs habs
  have h2 := measurable_natPair_sum'
    (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (n : ℂ) ^ (-ρ)) habs habs
  have hS : Measurable (fun x : ℝ => finiteSumSrho ρ |x|) :=
    ((measurable_abs_cpow _).mul h1).sub ((measurable_abs_cpow _).mul h2)
  exact (hS.add (measurable_const.mul (measurable_abs_cpow _))).add_const _

/-- |x|^c times a finite sum whose nonemptiness forces |x| ≥ a. -/
lemma norm_abs_cpow_mul_sum_le {c : ℂ} {y a R : ℝ} {S U : Finset ℕ} {f : ℕ → ℂ} (ha : 0 < a)
    (hy0 : 0 ≤ y) (hyR : y ≤ R) (hS : S ⊆ U) (hya : S.Nonempty → a ≤ y) :
    ‖((y : ℝ) : ℂ) ^ c * ∑ n ∈ S, f n‖ ≤ (a ^ c.re + R ^ c.re) * ∑ n ∈ U, ‖f n‖ := by
  have hU : 0 ≤ ∑ n ∈ U, ‖f n‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hR : 0 ≤ R := hy0.trans hyR
  have hpow : 0 ≤ a ^ c.re + R ^ c.re := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hR _)
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · rw [hS0, Finset.sum_empty, mul_zero, norm_zero]
    exact mul_nonneg hpow hU
  · have hay := hya hS0
    have hy : 0 < y := ha.trans_le hay
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    refine mul_le_mul ?_ ((norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun _ _ _ => norm_nonneg _))) (norm_nonneg _) hpow
    rcases le_total 0 c.re with hc | hc
    · exact (Real.rpow_le_rpow hy0 hyR hc).trans (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
    · exact (Real.rpow_le_rpow_of_nonpos ha hay hc).trans (le_add_of_nonneg_right (Real.rpow_nonneg hR _))

lemma locallyIntegrable_of_abs_le_bound {f : ℝ → ℂ} (hf : Measurable f)
    (hb : ∀ R : ℝ, 0 < R → ∃ M : ℝ, ∀ x : ℝ, |x| ≤ R → ‖f x‖ ≤ M) :
    LocallyIntegrable f volume := by
  refine locallyIntegrable_iff.mpr (fun K hK => ?_)
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  obtain ⟨M, hM⟩ := hb R hR0
  refine Measure.integrableOn_of_bounded (M := M) hK.measure_lt_top.ne hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall (fun x hx => hM x ?_))
  have := hR hx
  simpa [Metric.mem_closedBall, Real.dist_eq] using this

lemma coPoissonCutoffDensity_bound (ρ : ℂ) (T : ℝ) (R : ℝ) :
    ∃ M : ℝ, ∀ x : ℝ, |x| ≤ R → ‖coPoissonCutoffDensity ρ T x‖ ≤ M := by
  refine ⟨((1 : ℝ) ^ (-ρ).re + R ^ (-ρ).re) * ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, ‖(n : ℂ) ^ (ρ - 1)‖ +
    (Real.exp (-T) ^ (ρ - 1).re + R ^ (ρ - 1).re) *
      ∑ n ∈ Finset.Icc 1 ⌊R * Real.exp T⌋₊, ‖(n : ℂ) ^ (-ρ)‖ +
    ‖(cexp ((1 - ρ) * T) - 1) / (1 - ρ)‖, fun x hx => ?_⟩
  have hx0 : 0 ≤ |x| := abs_nonneg x
  unfold coPoissonCutoffDensity
  refine (norm_sub_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) _)
  · refine norm_abs_cpow_mul_sum_le one_pos hx0 hx (fun n hn => ?_) (fun ⟨n, hn⟩ => ?_)
    · rw [Finset.mem_Icc] at hn ⊢
      exact ⟨le_of_max_le_left hn.1, hn.2.trans (Nat.floor_le_floor hx)⟩
    · rw [Finset.mem_Icc] at hn
      have h1 : 1 ≤ ⌊|x|⌋₊ := (le_of_max_le_left hn.1).trans hn.2
      exact (Nat.one_le_floor_iff _).mp h1
  · refine norm_abs_cpow_mul_sum_le (Real.exp_pos _) hx0 hx (fun n hn => ?_) (fun ⟨n, hn⟩ => ?_)
    · rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      exact ⟨by omega, hn.2.trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hx
        (Real.exp_pos T).le))⟩
    · rw [Finset.mem_Ioc] at hn
      have h1 : 1 ≤ ⌊|x| * Real.exp T⌋₊ := by omega
      have h2 := (Nat.one_le_floor_iff _).mp h1
      rw [Real.exp_neg]
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos T)]
      linarith [mul_comm (|x|) (Real.exp T)]

lemma locallyIntegrable_coPoissonCutoffDensity (ρ : ℂ) (T : ℝ) :
    LocallyIntegrable (coPoissonCutoffDensity ρ T) volume :=
  locallyIntegrable_of_abs_le_bound (measurable_coPoissonCutoffDensity ρ T)
    (fun R _ => coPoissonCutoffDensity_bound ρ T R)

lemma integrableOn_abs_rpow_Icc {r : ℝ} (hr : -1 < r) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun x : ℝ => |x| ^ r) (Icc (-R) R) := by
  have h1 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 R := by
    refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) hr).congr (fun x hx => ?_)
    rw [Set.uIoc_of_le hR] at hx
    simp [abs_of_pos hx.1]
  have h2 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-R) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => |x| ^ r)).mp h1
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp (h2.trans h1)

/-- |x|^(ρ-1) is locally integrable for Re ρ > 0. -/
lemma locallyIntegrable_abs_cpow {ρ : ℂ} (h0 : 0 < ρ.re) :
    LocallyIntegrable (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (ρ - 1)) volume := by
  refine locallyIntegrable_iff.mpr (fun K hK => ?_)
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hsub : K ⊆ Icc (-R) R := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hint := (integrableOn_abs_rpow_Icc (r := (ρ - 1).re) (by simp; linarith) hR0.le).mono_set
    hsub
  refine hint.mono' (measurable_abs_cpow _).aestronglyMeasurable
    (Eventually.of_forall (fun x => ?_))
  refine (Complex.norm_cpow_le _ _).trans (le_of_eq ?_)
  rw [Complex.arg_ofReal_of_nonneg (abs_nonneg x), Complex.norm_real, Real.norm_eq_abs, abs_abs]
  simp

lemma finiteSumSrho_abs_bound (ρ : ℂ) (R : ℝ) :
    ∃ M : ℝ, ∀ x : ℝ, |x| ≤ R → ‖finiteSumSrho ρ |x|‖ ≤ M := by
  refine ⟨((1 : ℝ) ^ (-ρ).re + R ^ (-ρ).re) * ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, ‖(n : ℂ) ^ (ρ - 1)‖ +
    ((1 : ℝ) ^ (ρ - 1).re + R ^ (ρ - 1).re) * ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, ‖(n : ℂ) ^ (-ρ)‖,
    fun x hx => ?_⟩
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hsub : Finset.Icc 1 ⌊|x|⌋₊ ⊆ Finset.Icc 1 ⌊R⌋₊ := fun n hn => by
    rw [Finset.mem_Icc] at hn ⊢; exact ⟨hn.1, hn.2.trans (Nat.floor_le_floor hx)⟩
  have hne : (Finset.Icc 1 ⌊|x|⌋₊).Nonempty → 1 ≤ |x| := fun ⟨n, hn⟩ => by
    rw [Finset.mem_Icc] at hn; exact (Nat.one_le_floor_iff _).mp (hn.1.trans hn.2)
  unfold finiteSumSrho coPoissonPowerSums
  exact (norm_sub_le _ _).trans (add_le_add (norm_abs_cpow_mul_sum_le one_pos hx0 hx hsub hne)
    (norm_abs_cpow_mul_sum_le one_pos hx0 hx hsub hne))

lemma locallyIntegrable_coPoissonLimitDensity {ρ : ℂ} (h0 : 0 < ρ.re) :
    LocallyIntegrable (coPoissonLimitDensity ρ) volume := by
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have hS : LocallyIntegrable (fun x : ℝ => finiteSumSrho ρ |x|) volume := by
    refine locallyIntegrable_of_abs_le_bound ?_ (fun R _ => finiteSumSrho_abs_bound ρ R)
    have h1 := measurable_natPair_sum'
      (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (n : ℂ) ^ (ρ - 1)) habs habs
    have h2 := measurable_natPair_sum'
      (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (n : ℂ) ^ (-ρ)) habs habs
    exact ((measurable_abs_cpow _).mul h1).sub ((measurable_abs_cpow _).mul h2)
  have hZ : LocallyIntegrable (fun x : ℝ => riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1)) volume :=
    locallyIntegrable_iff.mpr (fun K hK =>
      (locallyIntegrable_iff.mp (locallyIntegrable_abs_cpow h0) K hK).const_mul (riemannZeta ρ))
  exact (hS.add hZ).add (locallyIntegrable_const _)

/-- The T-cutoff of (CP1.2) as a genuine locally finite complex measure
r_T(x) dx + ((1 - e^(-ρT))/ρ) δ₀. -/
def coPoissonCutoff (ρ : ℂ) (T : ℝ) : LocallyFiniteComplexMeasure :=
  densityAtomMeasure (coPoissonCutoffDensity ρ T) (coPoissonCutoffAtom ρ T)
    (locallyIntegrable_coPoissonCutoffDensity ρ T)

/-- The limit measure ρ⁻¹ δ₀ + [S_ρ(|x|) + ζ(ρ)|x|^(ρ-1) + (1-ρ)⁻¹] dx of (CP1.4). -/
def coPoissonLimitMeasure (ρ : ℂ) (h0 : 0 < ρ.re) : LocallyFiniteComplexMeasure :=
  densityAtomMeasure (coPoissonLimitDensity ρ) (1 / ρ) (locallyIntegrable_coPoissonLimitDensity h0)

/-! ### Pointwise cutoff error -/

/-- The uniform constant of the cutoff error. -/
def coPoissonErrorConst (ρ : ℂ) : ℝ :=
  1 / ‖1 - ρ‖ + ‖riemannZeta ρ‖ + (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re

lemma coPoissonCutoff_sub_limit_decay {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T x : ℝ}
    (hT : 0 ≤ T) (hx0 : x ≠ 0) (hxT : |x| ≤ Real.exp T) (hX : 1 ≤ |x| * Real.exp T) :
    ‖coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x‖ ≤
      (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re * (|x| ^ (ρ.re - 1) * (|x| * Real.exp T) ^ (-ρ.re)) := by
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hax : 0 < |x| := abs_pos.mpr hx0
  have hx2 : |x| * Real.exp (-T) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos T)]; exact hxT
  rw [coPoissonCutoff_sub_limit_main hT hax hx2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hax]
  have he := partialZeta_error h0 hρ1 hX
  have hf := floor_rpow_neg_le hX h0.le
  have hC : 0 ≤ 3 / 2 + ‖ρ‖ / ρ.re := by positivity
  simp only [Complex.sub_re, Complex.one_re]
  calc |x| ^ (ρ.re - 1) * ‖∑ n ∈ Finset.Icc 1 ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) -
        (((|x| * Real.exp T : ℝ)) : ℂ) ^ (1 - ρ) / (1 - ρ) - riemannZeta ρ‖
      ≤ |x| ^ (ρ.re - 1) * ((3 / 2 + ‖ρ‖ / ρ.re) * (2 ^ ρ.re * (|x| * Real.exp T) ^ (-ρ.re))) :=
        mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left hf hC))
          (Real.rpow_nonneg hax.le _)
    _ = _ := by ring

lemma coPoissonCutoff_sub_limit_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T x : ℝ}
    (hT : 0 ≤ T) (hx0 : x ≠ 0) (hxT : |x| ≤ Real.exp T) :
    ‖coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x‖ ≤
      coPoissonErrorConst ρ * |x| ^ (ρ.re - 1) := by
  have hax : 0 < |x| := abs_pos.mpr hx0
  have hpow : 0 ≤ |x| ^ (ρ.re - 1) := Real.rpow_nonneg hax.le _
  have hρ1 : (1 : ℂ) - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hC : 0 ≤ (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re := by positivity
  rcases lt_or_ge (|x| * Real.exp T) 1 with hX | hX
  · rw [coPoissonCutoff_sub_limit_small hT hX]
    have hexp : ‖cexp ((1 - ρ) * T)‖ ≤ |x| ^ (ρ.re - 1) := by
      rw [Complex.norm_exp]
      have hre : ((1 - ρ) * (T : ℂ)).re = (1 - ρ.re) * T := by simp
      rw [hre, mul_comm, Real.exp_mul]
      have hle : Real.exp T ≤ |x|⁻¹ := by
        rw [le_inv_comm₀ (Real.exp_pos T) hax]
        rw [← Real.exp_neg]
        have : |x| * Real.exp T * Real.exp (-T) = |x| := by
          rw [mul_assoc, ← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-T)]
      calc Real.exp T ^ (1 - ρ.re) ≤ |x|⁻¹ ^ (1 - ρ.re) :=
            Real.rpow_le_rpow (Real.exp_pos T).le hle (by linarith)
        _ = |x| ^ (ρ.re - 1) := by
            rw [Real.inv_rpow hax.le, ← Real.rpow_neg hax.le]; ring_nf
    have hz : ‖riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1)‖ = ‖riemannZeta ρ‖ * |x| ^ (ρ.re - 1) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hax]; simp
    calc ‖-(cexp ((1 - ρ) * T) / (1 - ρ)) - riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1)‖
        ≤ ‖cexp ((1 - ρ) * T)‖ / ‖1 - ρ‖ + ‖riemannZeta ρ‖ * |x| ^ (ρ.re - 1) := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_neg, norm_div, hz]
      _ ≤ |x| ^ (ρ.re - 1) / ‖1 - ρ‖ + ‖riemannZeta ρ‖ * |x| ^ (ρ.re - 1) := by
          gcongr
      _ ≤ coPoissonErrorConst ρ * |x| ^ (ρ.re - 1) := by
          have h3 : 0 ≤ (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re * |x| ^ (ρ.re - 1) := mul_nonneg hC hpow
          have h4 : coPoissonErrorConst ρ * |x| ^ (ρ.re - 1) = |x| ^ (ρ.re - 1) / ‖1 - ρ‖ +
              ‖riemannZeta ρ‖ * |x| ^ (ρ.re - 1) +
                (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re * |x| ^ (ρ.re - 1) := by
            unfold coPoissonErrorConst; ring
          linarith
  · refine (coPoissonCutoff_sub_limit_decay h0 h1 hT hx0 hxT hX).trans ?_
    have hle1 : (|x| * Real.exp T) ^ (-ρ.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)
    calc (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re * (|x| ^ (ρ.re - 1) * (|x| * Real.exp T) ^ (-ρ.re))
        ≤ (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re * (|x| ^ (ρ.re - 1) * 1) := by gcongr
      _ ≤ coPoissonErrorConst ρ * |x| ^ (ρ.re - 1) := by
          have h3 : 0 ≤ (1 / ‖1 - ρ‖ + ‖riemannZeta ρ‖) * |x| ^ (ρ.re - 1) :=
            mul_nonneg (by positivity) hpow
          have h4 : coPoissonErrorConst ρ * |x| ^ (ρ.re - 1) =
              (1 / ‖1 - ρ‖ + ‖riemannZeta ρ‖) * |x| ^ (ρ.re - 1) +
                (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re * (|x| ^ (ρ.re - 1) * 1) := by
            unfold coPoissonErrorConst; ring
          linarith

/-- Pointwise convergence of the cutoff density off the origin. -/
lemma coPoissonCutoff_tendsto_pointwise {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ}
    (hx0 : x ≠ 0) :
    Tendsto (fun T : ℝ => ‖coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x‖) atTop
      (𝓝 0) := by
  have hax : 0 < |x| := abs_pos.mpr hx0
  set C := (3 / 2 + ‖ρ‖ / ρ.re) * 2 ^ ρ.re with hC
  have hlim : Tendsto (fun T : ℝ => C * (|x| ^ (ρ.re - 1) * (|x| * Real.exp T) ^ (-ρ.re)))
      atTop (𝓝 0) := by
    have heq : (fun T : ℝ => C * (|x| ^ (ρ.re - 1) * (|x| * Real.exp T) ^ (-ρ.re))) =
        fun T => C * |x| ^ (ρ.re - 1) * |x| ^ (-ρ.re) * Real.exp (-(ρ.re * T)) := by
      funext T
      rw [Real.mul_rpow hax.le (Real.exp_pos T).le, ← Real.exp_mul]
      ring_nf
    rw [heq]
    have ht : Tendsto (fun T : ℝ => Real.exp (-(ρ.re * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h0)
    simpa using ht.const_mul (C * |x| ^ (ρ.re - 1) * |x| ^ (-ρ.re))
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (Real.log |x|),
    eventually_ge_atTop (-Real.log |x|)] with T hT hT1 hT2
  have hxT : |x| ≤ Real.exp T := by
    rw [← Real.exp_log hax]; exact Real.exp_le_exp.mpr hT1
  have hX : 1 ≤ |x| * Real.exp T := by
    rw [← Real.exp_log hax, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  exact coPoissonCutoff_sub_limit_decay h0 h1 hT hx0 hxT hX

/-! ### Local total-variation convergence (CP1.5) -/

lemma coPoissonCutoffAtom_sub_norm (ρ : ℂ) (T : ℝ) :
    ‖coPoissonCutoffAtom ρ T - 1 / ρ‖ = Real.exp (-(ρ.re * T)) / ‖ρ‖ := by
  unfold coPoissonCutoffAtom
  rw [show (1 - cexp (-ρ * T)) / ρ - 1 / ρ = -(cexp (-ρ * T) / ρ) by ring, norm_neg, norm_div,
    Complex.norm_exp]
  congr 2
  simp

lemma ae_ne_zero_real : ∀ᵐ x : ℝ ∂volume, x ≠ 0 :=
  compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))

/-- (CP1.5) On every compact window the actual cutoffs converge to the limit measure in the
genuine finite complex variation, origin atom included. -/
theorem coPoissonCutoff_localVariation_tendsto {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (K : Set ℝ) (hK : IsCompact K) :
    Tendsto (fun T : ℝ => ((coPoissonCutoff ρ T).compactRestriction K hK -
      (coPoissonLimitMeasure ρ h0).compactRestriction K hK).variation.real univ) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hsub : K ⊆ Icc (-R) R := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this
  have hbound (T : ℝ) : ((coPoissonCutoff ρ T).compactRestriction K hK -
      (coPoissonLimitMeasure ρ h0).compactRestriction K hK).variation.real univ ≤
      (∫ x in K, ‖coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x‖) +
        ‖coPoissonCutoffAtom ρ T - 1 / ρ‖ :=
    densityAtom_variation_diff_le _ _ hK
  have hae : ∀ᵐ x ∂(volume.restrict K), x ∈ K ∧ x ≠ 0 :=
    (ae_restrict_mem hK.measurableSet).and (ae_restrict_of_ae ae_ne_zero_real)
  have hint : Tendsto (fun T : ℝ => ∫ x in K,
      ‖coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x‖) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
      (l := atTop) (F := fun T x => ‖coPoissonCutoffDensity ρ T x - coPoissonLimitDensity ρ x‖)
      (f := fun _ => (0 : ℝ)) (fun x => coPoissonErrorConst ρ * |x| ^ (ρ.re - 1))
      (Eventually.of_forall (fun T => ((measurable_coPoissonCutoffDensity ρ T).sub
        (measurable_coPoissonLimitDensity ρ)).norm.aestronglyMeasurable))
      ?_ (((integrableOn_abs_rpow_Icc (r := ρ.re - 1) (by linarith) hR0.le).mono_set
        hsub).const_mul _) ?_
    · simpa using h
    · filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (Real.log R)] with T hT hTR
      filter_upwards [hae] with x hx
      have hxR : |x| ≤ R := abs_le.mpr (hsub hx.1)
      have hxT : |x| ≤ Real.exp T :=
        hxR.trans (by rw [← Real.exp_log hR0]; exact Real.exp_le_exp.mpr hTR)
      rw [norm_norm]
      exact coPoissonCutoff_sub_limit_le h0 h1 hT hx.2 hxT
    · filter_upwards [hae] with x hx
      exact coPoissonCutoff_tendsto_pointwise h0 h1 hx.2
  have hatom : Tendsto (fun T : ℝ => ‖coPoissonCutoffAtom ρ T - 1 / ρ‖) atTop (𝓝 0) := by
    simp_rw [coPoissonCutoffAtom_sub_norm]
    have ht : Tendsto (fun T : ℝ => Real.exp (-(ρ.re * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h0)
    simpa using ht.div_const ‖ρ‖
  exact squeeze_zero (fun T => measureReal_nonneg) hbound (by simpa using hint.add hatom)

/-- The same convergence in the parent's sequential notion `LocalVariationConvergence`. -/
theorem coPoissonCutoff_localVariationConvergence {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    LocalVariationConvergence (fun n : ℕ => coPoissonCutoff ρ n) (coPoissonLimitMeasure ρ h0) :=
  fun K hK => (coPoissonCutoff_localVariation_tendsto h0 h1 K hK).comp tendsto_natCast_atTop_atTop

/-! ### Pairing of a density-plus-atom measure with a test -/

lemma integral_densityAtomPart {h : ℝ → ℝ} (hm : Measurable h) (a : ℝ) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hf : Integrable (fun x => (h x : ℂ) * f x)) :
    Integrable f (densityAtomPart h a) ∧
      ∫ x, f x ∂(densityAtomPart h a) =
        (∫ x, ((max (h x) 0 : ℝ) : ℂ) * f x) + ((max a 0 : ℝ) : ℂ) * f 0 := by
  have hNN : Measurable (fun x => (h x).toNNReal) := hm.real_toNNReal
  have hsmul : (fun x => (h x).toNNReal • f x) = fun x => ((max (h x) 0 : ℝ) : ℂ) * f x := by
    funext x
    rw [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul]
  have hint : Integrable (fun x => ((max (h x) 0 : ℝ) : ℂ) * f x) := by
    refine hf.mono ((Complex.measurable_ofReal.comp (hm.max measurable_const)).aestronglyMeasurable.mul
      hfm) (Eventually.of_forall (fun x => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have h1 : Integrable f (volume.withDensity (fun x => ENNReal.ofReal (h x))) := by
    change Integrable f (volume.withDensity (fun x => ((h x).toNNReal : ℝ≥0∞)))
    rw [integrable_withDensity_iff_integrable_smul hNN, hsmul]
    exact hint
  have h2 : Integrable f (ENNReal.ofReal a • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  refine ⟨h1.add_measure h2, ?_⟩
  unfold densityAtomPart
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_dirac]
  change (∫ x, f x ∂(volume.withDensity (fun x => ((h x).toNNReal : ℝ≥0∞)))) + _ = _
  rw [integral_withDensity_eq_integral_smul hNN, hsmul, ENNReal.toReal_ofReal', Complex.real_smul]

/-- ⟨g dx + c δ₀, f⟩ = ∫ g f + c f(0) for the canonical Jordan pairs. -/
theorem densityAtomMeasure_integral {g : ℝ → ℂ} (c : ℂ) (hg : LocallyIntegrable g volume)
    (hgm : Measurable g) {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hgf : Integrable (fun x => g x * f x)) :
    (densityAtomMeasure g c hg).integral f = (∫ x, g x * f x) + c * f 0 := by
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_re hg) c.re
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_re hg).neg (-c.re)
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_im hg) c.im
  have := isLocallyFinite_densityAtomPart (locallyIntegrable_complex_im hg).neg (-c.im)
  have hre : Measurable (fun x => (g x).re) := Complex.measurable_re.comp hgm
  have him : Measurable (fun x => (g x).im) := Complex.measurable_im.comp hgm
  have hbound (u : ℝ → ℝ) (hu : ∀ x, |u x| ≤ ‖g x‖) (hum : Measurable u) :
      Integrable (fun x => (u x : ℂ) * f x) := by
    refine hgf.mono ((Complex.measurable_ofReal.comp hum).aestronglyMeasurable.mul hfm)
      (Eventually.of_forall (fun x => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
  have hr1 := integral_densityAtomPart hre c.re hfm (hbound _ (fun x => Complex.abs_re_le_norm _) hre)
  have hre' : Measurable (fun x => -(g x).re) := hre.neg
  have him' : Measurable (fun x => -(g x).im) := him.neg
  have hr2 := integral_densityAtomPart hre' (-c.re) hfm
    (hbound _ (fun x => by rw [abs_neg]; exact Complex.abs_re_le_norm _) hre')
  have hi1 := integral_densityAtomPart him c.im hfm (hbound _ (fun x => Complex.abs_im_le_norm _) him)
  have hi2 := integral_densityAtomPart him' (-c.im) hfm
    (hbound _ (fun x => by rw [abs_neg]; exact Complex.abs_im_le_norm _) him')
  unfold LocallyFiniteComplexMeasure.integral densityAtomMeasure
  dsimp only
  rw [localJordanDifference_integral _ _ f hr1.1 hr2.1, localJordanDifference_integral _ _ f hi1.1 hi2.1,
    hr1.2, hr2.2, hi1.2, hi2.2]
  have hpm (u : ℝ) : ((max u 0 : ℝ) : ℂ) - ((max (-u) 0 : ℝ) : ℂ) = (u : ℂ) := by
    rcases le_total 0 u with hu | hu
    · rw [max_eq_left hu, max_eq_right (by linarith : -u ≤ 0)]; simp
    · rw [max_eq_right hu, max_eq_left (by linarith : 0 ≤ -u)]; push_cast; ring
  have hint (u : ℝ → ℝ) (hum : Measurable u) (hu : ∀ x, |u x| ≤ ‖g x‖) :
      (∫ x, ((max (u x) 0 : ℝ) : ℂ) * f x) - (∫ x, ((max (-u x) 0 : ℝ) : ℂ) * f x) =
        ∫ x, (u x : ℂ) * f x := by
    have hip : Integrable (fun x => ((max (u x) 0 : ℝ) : ℂ) * f x) := by
      refine (hbound u hu hum).mono ((Complex.measurable_ofReal.comp
        (hum.max measurable_const)).aestronglyMeasurable.mul hfm) (Eventually.of_forall (fun x => ?_))
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (norm_nonneg _)
    have hin : Integrable (fun x => ((max (-u x) 0 : ℝ) : ℂ) * f x) := by
      have hum' : Measurable (fun x => -u x) := hum.neg
      refine (hbound u hu hum).mono ((Complex.measurable_ofReal.comp
        (hum'.max measurable_const)).aestronglyMeasurable.mul hfm) (Eventually.of_forall (fun x => ?_))
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _)) (norm_nonneg _)
    rw [← integral_sub hip hin]
    congr 1
    funext x
    rw [← sub_mul, hpm]
  rw [show ∀ (A B C D : ℂ), A + C - (B + D) = (A - B) + (C - D) from fun _ _ _ _ => by ring,
    show ∀ (A B C D : ℂ), A + C - (B + D) = (A - B) + (C - D) from fun _ _ _ _ => by ring,
    hint _ hre (fun x => Complex.abs_re_le_norm _), hint _ him (fun x => Complex.abs_im_le_norm _),
    ← sub_mul, ← sub_mul, hpm, hpm]
  have hgsplit : (∫ x, g x * f x) = (∫ x, ((g x).re : ℂ) * f x) + I * ∫ x, ((g x).im : ℂ) * f x := by
    rw [← integral_const_mul, ← integral_add (hbound _ (fun x => Complex.abs_re_le_norm _) hre)
      ((hbound _ (fun x => Complex.abs_im_le_norm _) him).const_mul I)]
    congr 1
    funext x
    conv_lhs => rw [← Complex.re_add_im (g x)]
    ring
  rw [hgsplit]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

/-! ### Lattice-ray change of variables -/

lemma ofReal_mul_exp_cpow {m : ℝ} (hm : 0 < m) (u : ℝ) (c : ℂ) :
    (((m * Real.exp u : ℝ)) : ℂ) ^ c = (m : ℂ) ^ c * cexp (c * u) := by
  have he : ((Real.exp u : ℝ) : ℂ) ^ c = cexp (c * u) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, mul_comm]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hm.le (Real.exp_pos u).le, he]

/-- Change of variables y = m e^u along one lattice ray. -/
lemma ray_change_of_variables (μ : ℂ) {m : ℝ} (hm : 0 < m) (a b : ℝ) {g : ℝ → ℂ}
    (hg : Continuous g) :
    ∫ u in a..b, cexp ((1 / 2 - μ) * u) * g (m * Real.exp u) =
      (m : ℂ) ^ (μ - 1 / 2) * ∫ y in m * Real.exp a..m * Real.exp b,
        (y : ℂ) ^ (-1 / 2 - μ) * g y := by
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt (fun u : ℝ => m * Real.exp u) (m * Real.exp u) u :=
    fun u _ => (Real.hasDerivAt_exp u).const_mul m
  have hcont' : ContinuousOn (fun u : ℝ => m * Real.exp u) (uIcc a b) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  have hG : ContinuousOn (fun y : ℝ => (m : ℂ) ^ (μ - 1 / 2) * ((y : ℂ) ^ (-1 / 2 - μ) * g y))
      ((fun u : ℝ => m * Real.exp u) '' uIcc a b) := by
    rintro _ ⟨u, -, rfl⟩
    have hpos : 0 < m * Real.exp u := mul_pos hm (Real.exp_pos u)
    refine (continuousAt_const.mul (ContinuousAt.mul ?_ hg.continuousAt)).continuousWithinAt
    exact (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hpos)).comp
      Complex.continuous_ofReal.continuousAt
  have h := intervalIntegral.integral_deriv_smul_comp' hderiv hcont' hG
  rw [intervalIntegral.integral_const_mul] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  simp only [Function.comp_apply, Complex.real_smul]
  rw [ofReal_mul_exp_cpow hm u]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow : (m : ℂ) * ((m : ℂ) ^ (μ - 1 / 2) * (m : ℂ) ^ (-1 / 2 - μ)) = 1 := by
    rw [← Complex.cpow_add _ _ hm0, show μ - 1 / 2 + (-1 / 2 - μ) = -1 by ring,
      Complex.cpow_neg_one, mul_inv_cancel₀ hm0]
  have hexp : ((Real.exp u : ℝ) : ℂ) * cexp ((-1 / 2 - μ) * u) = cexp ((1 / 2 - μ) * u) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; ring_nf
  rw [Complex.ofReal_mul]
  calc cexp ((1 / 2 - μ) * u) * g (m * Real.exp u)
      = ((m : ℂ) * ((m : ℂ) ^ (μ - 1 / 2) * (m : ℂ) ^ (-1 / 2 - μ))) *
          (((Real.exp u : ℝ) : ℂ) * cexp ((-1 / 2 - μ) * u)) * g (m * Real.exp u) := by
        rw [hpow, hexp, one_mul]
    _ = _ := by ring


/-- ‖φ(y)‖ ≤ p_k(φ) |y|^(-k) for y ≠ 0. -/
lemma schwartz_norm_le_rpow (φ : 𝓢(ℝ, ℂ)) (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    ‖φ y‖ ≤ SchwartzMap.seminorm ℂ k 0 φ * |y| ^ (-(k : ℝ)) := by
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℂ φ k y
  have hy' : 0 < |y| := abs_pos.mpr hy
  rw [Real.norm_eq_abs] at hb
  rw [Real.rpow_neg hy'.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [mul_comm (|y| ^ k) ‖φ y‖]

/-- y^c ≤ p^c + q^c on [p, q] ⊂ (0, ∞). -/
lemma rpow_le_endpoints {p q y c : ℝ} (hp : 0 < p) (hy : y ∈ Icc p q) :
    y ^ c ≤ p ^ c + q ^ c := by
  have hy0 : 0 ≤ y := hp.le.trans hy.1
  rcases le_total 0 c with hc | hc
  · exact (Real.rpow_le_rpow hy0 hy.2 hc).trans (le_add_of_nonneg_left (Real.rpow_nonneg hp.le _))
  · exact (Real.rpow_le_rpow_of_nonpos hp hy.1 hc).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hp.le.trans (hy.1.trans hy.2)) _))

lemma summable_nat_add_one_rpow_neg {r : ℝ} (hr : 1 < r) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-r)) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -r < -1))
  simpa using h

/-- The integral of a tsum of functions with summable L¹ norms is integrable. -/
lemma integrable_tsum_of_summable_norm {F : ℕ → ℝ → ℂ} {m : Measure ℝ}
    (hF : ∀ n, Integrable (F n) m) (hs : Summable (fun n => ∫ x, ‖F n x‖ ∂m))
    (hmeas : AEStronglyMeasurable (fun x => ∑' n, F n x) m) :
    Integrable (fun x => ∑' n, F n x) m := by
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖∑' n, F n x‖ₑ ∂m ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂m :=
        lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂m := lintegral_tsum (fun n => (hF n).aestronglyMeasurable.enorm)
    _ = ∑' n, ENNReal.ofReal (∫ x, ‖F n x‖ ∂m) := by
        congr 1; funext n; rw [ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun x => norm_nonneg _)) hs]
        exact ENNReal.ofReal_lt_top

/-- t-side: the lattice-ray series may be integrated term by term over a bounded window. -/
lemma tside_tsum_integral (μ : ℂ) {a b : ℝ} (hab : a ≤ b) (φ : 𝓢(ℝ, ℂ)) :
    ∫ u in a..b, cexp ((1 / 2 - μ) * u) * ∑' n : ℕ, φ (((n : ℝ) + 1) * Real.exp u) =
      ∑' n : ℕ, ∫ u in a..b, cexp ((1 / 2 - μ) * u) * φ (((n : ℝ) + 1) * Real.exp u) := by
  set F : ℕ → ℝ → ℂ := fun n u => cexp ((1 / 2 - μ) * u) * φ (((n : ℝ) + 1) * Real.exp u) with hF
  have hcont (n : ℕ) : Continuous (F n) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (φ.continuous.comp (continuous_const.mul Real.continuous_exp))
  set E : ℝ := Real.exp (|1 / 2 - μ.re| * (|a| + |b|)) with hE
  set P : ℝ := SchwartzMap.seminorm ℂ 2 0 φ with hP
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Ioc a b) :
      ‖F n u‖ ≤ E * P * Real.exp (-(2 * a)) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hy : ((n : ℝ) + 1) * Real.exp u ≠ 0 := (mul_pos hn (Real.exp_pos u)).ne'
    have h1 : ‖cexp ((1 / 2 - μ) * u)‖ ≤ E := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have : ((1 / 2 - μ) * (u : ℂ)).re = (1 / 2 - μ.re) * u := by simp
      rw [this]
      have hu' : |u| ≤ |a| + |b| := by
        rcases le_total 0 u with h | h
        · rw [abs_of_nonneg h]; linarith [hu.2, le_abs_self b, abs_nonneg a]
        · rw [abs_of_nonpos h]; linarith [hu.1, neg_abs_le a, abs_nonneg b]
      calc (1 / 2 - μ.re) * u ≤ |1 / 2 - μ.re| * |u| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ _ := mul_le_mul_of_nonneg_left hu' (abs_nonneg _)
    have h2 := schwartz_norm_le_rpow φ 2 hy
    rw [abs_of_pos (mul_pos hn (Real.exp_pos u)), Real.mul_rpow hn.le (Real.exp_pos u).le,
      ← Real.exp_mul] at h2
    have h3 : Real.exp (u * -((2 : ℕ) : ℝ)) ≤ Real.exp (-(2 * a)) := by
      refine Real.exp_le_exp.mpr ?_; push_cast; linarith [hu.1]
    calc ‖F n u‖ = ‖cexp ((1 / 2 - μ) * u)‖ * ‖φ (((n : ℝ) + 1) * Real.exp u)‖ := norm_mul _ _
      _ ≤ E * (P * (((n : ℝ) + 1) ^ (-((2 : ℕ) : ℝ)) * Real.exp (-(2 * a)))) := by
          refine mul_le_mul h1 (h2.trans ?_) (norm_nonneg _) (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
          exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hn.le _)
      _ = _ := by push_cast; ring
  have hint (n : ℕ) : Integrable (F n) (volume.restrict (Ioc a b)) :=
    ((hcont n).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsum : Summable (fun n => ∫ u in Ioc a b, ‖F n u‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => ?_) ((summable_nat_add_one_rpow_neg (by norm_num : (1 : ℝ) < 2)).mul_left
        ((b - a) * (E * P * Real.exp (-(2 * a)))))
    have h := norm_setIntegral_le_of_norm_le_const (f := fun u => ‖F n u‖) (μ := volume)
      (s := Ioc a b) (C := E * P * Real.exp (-(2 * a)) *
      ((n : ℝ) + 1) ^ (-(2 : ℝ))) measure_Ioc_lt_top
      (fun u hu => by rw [norm_norm]; exact hbound n u hu)
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), Measure.real,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at h
    linarith
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  funext u
  rw [← tsum_mul_left]

/-- The n-th lattice-ray term of the positive-axis density, on a ray window S n. -/
def rayTerm (μ : ℂ) (S : ℕ → Set ℝ) (φ : ℝ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  (S n).indicator (fun y => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2) * ((y : ℂ) ^ (-1 / 2 - μ) * φ y)) y

lemma continuousOn_cpow_mul_schwartz (c : ℂ) (φ : 𝓢(ℝ, ℂ)) {p q : ℝ} (hp : 0 < p) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ c * φ y) (Icc p q) := by
  intro y hy
  have hy0 : 0 < y := hp.trans_le hy.1
  refine (ContinuousAt.mul ?_ φ.continuous.continuousAt).continuousWithinAt
  exact (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hy0)).comp
    Complex.continuous_ofReal.continuousAt

/-- y-side: the lattice-ray terms are integrable with summable L¹ norms, and the bounded-window
lattice integral is the integral of their sum. -/
lemma yside_rays (μ : ℂ) {a b : ℝ} (hab : a ≤ b) (φ : 𝓢(ℝ, ℂ)) {S : ℕ → Set ℝ}
    (hSm : ∀ n, MeasurableSet (S n))
    (hSsub : ∀ n, S n ⊆ Icc (((n : ℝ) + 1) * Real.exp a) (((n : ℝ) + 1) * Real.exp b))
    (hSae : ∀ n, S n =ᵐ[volume] Ioc (((n : ℝ) + 1) * Real.exp a) (((n : ℝ) + 1) * Real.exp b)) :
    (∀ n, Integrable (rayTerm μ S φ n)) ∧ Summable (fun n => ∫ y, ‖rayTerm μ S φ n y‖) ∧
      ∫ u in a..b, cexp ((1 / 2 - μ) * u) * ∑' n : ℕ, φ (((n : ℝ) + 1) * Real.exp u) =
        ∫ y, ∑' n : ℕ, rayTerm μ S φ n y := by
  have hn (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp (n : ℕ) : 0 < ((n : ℝ) + 1) * Real.exp a := mul_pos (hn n) (Real.exp_pos a)
  have hpq (n : ℕ) : ((n : ℝ) + 1) * Real.exp a ≤ ((n : ℝ) + 1) * Real.exp b :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) (hn n).le
  have hon (n : ℕ) : IntegrableOn (fun y : ℝ => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2) *
      ((y : ℂ) ^ (-1 / 2 - μ) * φ y)) (S n) := by
    have hI : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-1 / 2 - μ) * φ y)
        (Icc (((n : ℝ) + 1) * Real.exp a) (((n : ℝ) + 1) * Real.exp b)) :=
      (continuousOn_cpow_mul_schwartz _ φ (hp n)).integrableOn_Icc
    exact IntegrableOn.mono_set (hI.const_mul _) (hSsub n)
  have hint (n : ℕ) : Integrable (rayTerm μ S φ n) := (integrable_indicator_iff (hSm n)).mpr (hon n)
  set P : ℝ := SchwartzMap.seminorm ℂ 3 0 φ with hP
  set e : ℝ := -7 / 2 - μ.re with he
  set K : ℝ := P * (Real.exp (a * e) + Real.exp (b * e)) * (Real.exp b - Real.exp a) with hK
  have hnorm (n : ℕ) : ∫ y, ‖rayTerm μ S φ n y‖ ≤ K * ((n : ℝ) + 1) ^ (-(3 : ℝ)) := by
    have hC : ∀ y ∈ S n, ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2) * ((y : ℂ) ^ (-1 / 2 - μ) * φ y)‖ ≤
        ((n : ℝ) + 1) ^ (μ.re - 1 / 2) * P * (((n : ℝ) + 1) ^ e *
          (Real.exp (a * e) + Real.exp (b * e))) := by
      intro y hy
      have hyI := hSsub n hy
      have hy0 : 0 < y := (hp n).trans_le hyI.1
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hn n),
        Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      have hφ := schwartz_norm_le_rpow φ 3 hy0.ne'
      rw [abs_of_pos hy0] at hφ
      have hye : y ^ (-1 / 2 - μ).re * (P * y ^ (-((3 : ℕ) : ℝ))) = P * y ^ e := by
        rw [mul_left_comm, ← Real.rpow_add hy0]; congr 2; simp [he]; ring
      have hend := rpow_le_endpoints (c := e) (hp n) hyI
      rw [Real.mul_rpow (hn n).le (Real.exp_pos a).le, Real.mul_rpow (hn n).le (Real.exp_pos b).le,
        ← Real.exp_mul, ← Real.exp_mul, ← mul_add] at hend
      have hsub : (μ - 1 / 2).re = μ.re - 1 / 2 := by simp
      rw [hsub, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hn n).le _)
      calc y ^ (-1 / 2 - μ).re * ‖φ y‖ ≤ y ^ (-1 / 2 - μ).re * (P * y ^ (-((3 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hφ (Real.rpow_nonneg hy0.le _)
        _ = P * y ^ e := hye
        _ ≤ _ := mul_le_mul_of_nonneg_left hend (apply_nonneg _ _)
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := S n)
      (f := fun y : ℝ => ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2) * ((y : ℂ) ^ (-1 / 2 - μ) * φ y)‖)
      ((measure_mono (hSsub n)).trans_lt measure_Icc_lt_top) (fun y hy => by
        rw [norm_norm]; exact hC y hy)
    have hvol : volume.real (S n) ≤ ((n : ℝ) + 1) * (Real.exp b - Real.exp a) := by
      rw [Measure.real]
      refine (ENNReal.toReal_mono measure_Icc_lt_top.ne (measure_mono (hSsub n))).trans ?_
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hpq n])]
      ring_nf; rfl
    have hrw : ∫ y, ‖rayTerm μ S φ n y‖ = ∫ y in S n,
        ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2) * ((y : ℂ) ^ (-1 / 2 - μ) * φ y)‖ := by
      unfold rayTerm
      simp_rw [norm_indicator_eq_indicator_norm]
      rw [integral_indicator (hSm n)]
    rw [hrw]
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at h
    have hCn : 0 ≤ ((n : ℝ) + 1) ^ (μ.re - 1 / 2) * P * (((n : ℝ) + 1) ^ e *
        (Real.exp (a * e) + Real.exp (b * e))) := by
      have := apply_nonneg (SchwartzMap.seminorm ℂ 3 0) φ
      positivity
    refine h.trans ((mul_le_mul_of_nonneg_left hvol hCn).trans (le_of_eq ?_))
    have hpow : ((n : ℝ) + 1) ^ (μ.re - 1 / 2) * ((n : ℝ) + 1) ^ e * ((n : ℝ) + 1) =
        ((n : ℝ) + 1) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add (hn n), ← Real.rpow_add_one (hn n).ne']
      congr 1; rw [he]; ring
    rw [hK, ← hpow]
    ring
  have hsum : Summable (fun n => ∫ y, ‖rayTerm μ S φ n y‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hnorm
      ((summable_nat_add_one_rpow_neg (by norm_num : (1 : ℝ) < 3)).mul_left K)
  refine ⟨hint, hsum, ?_⟩
  rw [tside_tsum_integral μ hab φ, ← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr (fun n => ?_)
  rw [ray_change_of_variables μ (hn n) a b φ.continuous, intervalIntegral.integral_of_le (hpq n),
    ← setIntegral_congr_set (hSae n), ← integral_const_mul]
  unfold rayTerm
  rw [integral_indicator (hSm n)]

/-- A_u φ through the positive lattice rays of the even part φ(y) + φ(-y). -/
lemma coPoissonA_eq_rays (u : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonA u φ = (Real.exp (u / 2) : ℂ) *
      ∑' n : ℕ, (φ + schwartzReflect φ) (((n : ℝ) + 1) * Real.exp u) := by
  have hs := dilatedComb_schwartz_summable u φ
  set g : ℤ → ℂ := fun n => φ (Real.exp u * (n : ℝ)) with hg
  have hpos : Summable (fun n : ℕ => g n) := hs.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) :=
    hs.comp_injective (fun a b h => by simpa using h)
  have hsplit := tsum_of_nat_of_neg_add_one hpos hneg
  have hzero := hpos.tsum_eq_zero_add
  have hpos' : Summable (fun n : ℕ => g ((n + 1 : ℕ) : ℤ)) :=
    (summable_nat_add_iff 1).mpr hpos
  rw [coPoissonA, sub_apply, smul_apply, dilatedCombDistribution_apply,
    TemperedDistribution.delta_apply, smul_eq_mul]
  change (Real.exp (u / 2) : ℂ) * ∑' n : ℤ, g n - _ = _
  rw [hsplit, hzero]
  have h0 : g ((0 : ℕ) : ℤ) = φ 0 := by simp [hg]
  rw [h0]
  have hsum : ∑' n : ℕ, (φ + schwartzReflect φ) (((n : ℝ) + 1) * Real.exp u) =
      ∑' n : ℕ, g ((n + 1 : ℕ) : ℤ) + ∑' n : ℕ, g (-((n : ℤ) + 1)) := by
    rw [← hpos'.tsum_add hneg]
    refine tsum_congr (fun n => ?_)
    simp only [hg, add_apply, schwartzReflect_apply]
    push_cast
    congr 1
    · ring_nf
    · ring_nf
  rw [hsum]
  push_cast
  ring

lemma tsum_rayIndicator_eq {S : ℕ → Set ℝ} {y : ℝ} {s : Finset ℕ} (h0 : 0 ∉ s)
    (hS : ∀ n, y ∈ S n ↔ n + 1 ∈ s) (c : ℕ → ℂ) :
    ∑' n : ℕ, (S n).indicator (fun _ => c (n + 1)) y = ∑ m ∈ s, c m := by
  classical
  set f : ℕ → ℂ := fun m => if m ∈ s then c m else 0 with hf
  have hfs : Summable f := summable_of_ne_finset_zero (s := s) (fun m hm => if_neg hm)
  have h1 : ∀ n, (S n).indicator (fun _ => c (n + 1)) y = f (n + 1) := by
    intro n
    by_cases h : y ∈ S n
    · rw [Set.indicator_of_mem h, hf]; simp only [(hS n).mp h, if_true]
    · rw [Set.indicator_of_notMem h, hf]
      simp only [show n + 1 ∉ s from fun h' => h ((hS n).mpr h'), if_false]
  simp_rw [h1]
  have h2 := hfs.tsum_eq_zero_add
  have hf0 : f 0 = 0 := if_neg h0
  rw [hf0, zero_add] at h2
  rw [← h2, tsum_eq_sum (s := s) (fun m hm => if_neg hm)]
  exact Finset.sum_congr rfl (fun m hm => if_pos hm)

/-- Pairing of one cutoff lattice family: ∫_a^b e^(-μu) A_u φ du = ∫ P(|x|) φ(x) dx, where P is the
explicit positive-axis density of the ray windows S n. -/
lemma family_pairing (μ : ℂ) {a b : ℝ} (hab : a ≤ b) (φ : 𝓢(ℝ, ℂ)) {S : ℕ → Set ℝ}
    (hSm : ∀ n, MeasurableSet (S n))
    (hSsub : ∀ n, S n ⊆ Icc (((n : ℝ) + 1) * Real.exp a) (((n : ℝ) + 1) * Real.exp b))
    (hSae : ∀ n, S n =ᵐ[volume] Ioc (((n : ℝ) + 1) * Real.exp a) (((n : ℝ) + 1) * Real.exp b))
    {P : ℝ → ℂ} (hPm : Measurable P) (hP0 : P 0 = 0)
    (hP : ∀ y : ℝ, 0 < y → (y : ℂ) ^ (-1 / 2 - μ) *
      ∑' n : ℕ, (S n).indicator (fun _ => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2)) y = P y) :
    Integrable (fun x => P |x| * φ x) ∧
      ∫ u in a..b, cexp (-μ * u) * coPoissonA u φ = ∫ x, P |x| * φ x := by
  have hpos (n : ℕ) (y : ℝ) (hy : y ∈ S n) : 0 < y :=
    (mul_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (Real.exp_pos a)).trans_le (hSsub n hy).1
  have hW (ψ : 𝓢(ℝ, ℂ)) (y : ℝ) :
      ∑' n : ℕ, rayTerm μ S ψ n y = (Ioi (0 : ℝ)).indicator (fun y => P y * ψ y) y := by
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), ← hP y hy]
      have h1 : ∀ n, rayTerm μ S ψ n y = (S n).indicator
          (fun _ => ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (μ - 1 / 2)) y * ((y : ℂ) ^ (-1 / 2 - μ) * ψ y) := by
        intro n
        unfold rayTerm
        by_cases h : y ∈ S n
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
      simp_rw [h1]
      rw [tsum_mul_right]
      ring
    · rw [Set.indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
      refine (tsum_congr (fun n => ?_)).trans tsum_zero
      unfold rayTerm
      exact Set.indicator_of_notMem (fun h => hy (hpos n y h)) _
  have hWm (ψ : 𝓢(ℝ, ℂ)) : Measurable (fun y => (Ioi (0 : ℝ)).indicator (fun y => P y * ψ y) y) :=
    (hPm.mul ψ.continuous.measurable).indicator measurableSet_Ioi
  have hWi (ψ : 𝓢(ℝ, ℂ)) : Integrable (fun y => (Ioi (0 : ℝ)).indicator (fun y => P y * ψ y) y) := by
    obtain ⟨hint, hsum, -⟩ := yside_rays μ hab ψ hSm hSsub hSae
    have h := integrable_tsum_of_summable_norm hint hsum
      (by simp_rw [hW ψ]; exact (hWm ψ).aestronglyMeasurable)
    simpa only [hW ψ] using h
  set φr := schwartzReflect φ with hφr
  have hpt : (fun x => P |x| * φ x) = fun x =>
      (Ioi (0 : ℝ)).indicator (fun y => P y * φ y) x +
        (Ioi (0 : ℝ)).indicator (fun y => P y * φr y) (-x) := by
    funext x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from fun h => lt_asymm hx h),
        Set.indicator_of_mem (show -x ∈ Ioi (0 : ℝ) from neg_pos.mpr hx), hφr,
        schwartzReflect_apply, neg_neg, abs_of_neg hx, zero_add]
    · simp [hP0]
    · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
        Set.indicator_of_notMem (show -x ∉ Ioi (0 : ℝ) from fun h => by
          simp only [Set.mem_Ioi] at h; linarith), abs_of_pos hx, add_zero]
  have hint : Integrable (fun x => P |x| * φ x) := by
    rw [hpt]; exact (hWi φ).add (hWi φr).comp_neg
  refine ⟨hint, ?_⟩
  have hexp (u : ℝ) : cexp (-μ * u) * coPoissonA u φ =
      cexp ((1 / 2 - μ) * u) * ∑' n : ℕ, (φ + φr) (((n : ℝ) + 1) * Real.exp u) := by
    rw [coPoissonA_eq_rays, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp_rw [hexp]
  obtain ⟨-, -, hrays⟩ := yside_rays μ hab (φ + φr) hSm hSsub hSae
  rw [hrays]
  simp_rw [hW (φ + φr)]
  have hadd : (fun y => (Ioi (0 : ℝ)).indicator (fun y => P y * (φ + φr) y) y) = fun y =>
      (Ioi (0 : ℝ)).indicator (fun y => P y * φ y) y +
        (Ioi (0 : ℝ)).indicator (fun y => P y * φr y) y := by
    funext y
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Set.indicator_of_mem hy, add_apply]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
        add_zero]
  rw [hadd, integral_add (hWi φ) (hWi φr), hpt, integral_add (hWi φ) (hWi φr).comp_neg,
    integral_neg_eq_self (fun y => (Ioi (0 : ℝ)).indicator (fun y => P y * φr y) y)]


/-! ### Identification of the actual cutoff -/

/-- K_t φ = A_t φ + A_(-t) φ + e^(-t/2) φ(0) - e^(t/2) ∫ φ. -/
lemma renormalizedCombKernel_apply_split (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    renormalizedCombKernel t φ = coPoissonA t φ + coPoissonA (-t) φ +
      (Real.exp (-t / 2) : ℂ) * φ 0 - (Real.exp (t / 2) : ℂ) * ∫ x, φ x := by
  rw [renormalizedCombKernel_eq]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, coPoissonA,
    TemperedDistribution.delta_apply, fourier_delta_zero_apply]
  rw [neg_div]
  ring

/-- Positive-axis density of the first cutoff family (rays x = (n+1) e^t, 0 ≤ t ≤ T). -/
def cutoffFamilyOne (ρ : ℂ) (T : ℝ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (-ρ) * ∑ n ∈ Finset.Icc (max 1 ⌈y * Real.exp (-T)⌉₊) ⌊y⌋₊, (n : ℂ) ^ (ρ - 1)

/-- Positive-axis density of the second cutoff family (rays x = (n+1) e^(-t), 0 ≤ t ≤ T). -/
def cutoffFamilyTwo (ρ : ℂ) (T : ℝ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (ρ - 1) * ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp T⌋₊, (n : ℂ) ^ (-ρ)

lemma cutoffFamily_density (ρ : ℂ) (T x : ℝ) :
    coPoissonCutoffDensity ρ T x = cutoffFamilyOne ρ T |x| + cutoffFamilyTwo ρ T |x| -
      (cexp ((1 - ρ) * T) - 1) / (1 - ρ) := rfl

lemma cutoffFamilyOne_pairing (ρ : ℂ) {T : ℝ} (hT : 0 ≤ T) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => cutoffFamilyOne ρ T |x| * φ x) ∧
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * coPoissonA t φ =
        ∫ x, cutoffFamilyOne ρ T |x| * φ x := by
  have hn (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine family_pairing (ρ - 1 / 2) hT φ
    (S := fun n => Icc (((n : ℝ) + 1) * Real.exp 0) (((n : ℝ) + 1) * Real.exp T))
    (fun n => measurableSet_Icc) (fun n => subset_rfl) (fun n => Ioc_ae_eq_Icc.symm) ?_ ?_ ?_
  · have habs : Measurable (fun y : ℝ => y) := measurable_id
    exact (Complex.measurable_ofReal.pow_const _).mul (measurable_natPair_sum
      (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc (max 1 p.1) p.2, (n : ℂ) ^ (ρ - 1))
      (habs.mul_const _) habs)
  · unfold cutoffFamilyOne
    rw [Nat.floor_zero, Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero]
  · intro y hy
    have hiff : ∀ n : ℕ, y ∈ Icc (((n : ℝ) + 1) * Real.exp 0) (((n : ℝ) + 1) * Real.exp T) ↔
        n + 1 ∈ Finset.Icc (max 1 ⌈y * Real.exp (-T)⌉₊) ⌊y⌋₊ := by
      intro n
      rw [Real.exp_zero, mul_one, Set.mem_Icc, Finset.mem_Icc, max_le_iff, Nat.ceil_le,
        Nat.le_floor_iff hy.le, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos T)]
      push_cast
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨trivial, h2⟩, h1⟩
      · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩
    have h0 : 0 ∉ Finset.Icc (max 1 ⌈y * Real.exp (-T)⌉₊) ⌊y⌋₊ := by
      rw [Finset.mem_Icc]; omega
    have h := tsum_rayIndicator_eq h0 hiff (fun m => (((m : ℕ) : ℝ) : ℂ) ^ (ρ - 1 / 2 - 1 / 2))
    simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_natCast] at h
    unfold cutoffFamilyOne
    rw [show -1 / 2 - (ρ - 1 / 2) = -ρ by ring, show ρ - 1 / 2 - 1 / 2 = ρ - 1 by ring] at *
    rw [← h]

lemma cutoffFamilyTwo_pairing (ρ : ℂ) {T : ℝ} (hT : 0 ≤ T) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => cutoffFamilyTwo ρ T |x| * φ x) ∧
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * coPoissonA (-t) φ =
        ∫ x, cutoffFamilyTwo ρ T |x| * φ x := by
  have hfam := family_pairing (1 / 2 - ρ) (a := -T) (b := 0) (by linarith) φ
    (S := fun n => Ico (((n : ℝ) + 1) * Real.exp (-T)) (((n : ℝ) + 1) * Real.exp 0))
    (fun n => measurableSet_Ico) (fun n => Ico_subset_Icc_self) (fun n => Ico_ae_eq_Ioc)
    (P := cutoffFamilyTwo ρ T) ?_ ?_ ?_
  · refine ⟨hfam.1, ?_⟩
    have key := intervalIntegral.integral_comp_neg (a := 0) (b := T)
      (fun u : ℝ => cexp (-(1 / 2 - ρ) * u) * coPoissonA u φ)
    rw [neg_zero] at key
    rw [← hfam.2, ← key]
    congr 1
    funext t
    congr 2
    push_cast
    ring
  · have habs : Measurable (fun y : ℝ => y) := measurable_id
    exact (Complex.measurable_ofReal.pow_const _).mul (measurable_natPair_sum'
      (fun p : ℕ × ℕ => ∑ n ∈ Finset.Ioc p.1 p.2, (n : ℂ) ^ (-ρ)) habs (habs.mul_const _))
  · unfold cutoffFamilyTwo
    simp
  · intro y hy
    have hiff : ∀ n : ℕ, y ∈ Ico (((n : ℝ) + 1) * Real.exp (-T)) (((n : ℝ) + 1) * Real.exp 0) ↔
        n + 1 ∈ Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp T⌋₊ := by
      intro n
      rw [Real.exp_zero, mul_one, Set.mem_Ico, Finset.mem_Ioc, Nat.floor_lt hy.le,
        Nat.le_floor_iff (mul_nonneg hy.le (Real.exp_pos T).le), Real.exp_neg, ← div_eq_mul_inv,
        div_le_iff₀ (Real.exp_pos T)]
      push_cast
      exact And.comm
    have h0 : 0 ∉ Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp T⌋₊ := by
      rw [Finset.mem_Ioc]; omega
    have h := tsum_rayIndicator_eq h0 hiff (fun m => (((m : ℕ) : ℝ) : ℂ) ^ (1 / 2 - ρ - 1 / 2))
    simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_natCast] at h
    unfold cutoffFamilyTwo
    rw [show -1 / 2 - (1 / 2 - ρ) = ρ - 1 by ring, show 1 / 2 - ρ - 1 / 2 = -ρ by ring] at *
    rw [← h]

/-- (CP1.2)-(CP1.3) The actual cutoff ∫_0^T e^(-(ρ-1/2)t) K_t dt on every Schwartz test is the
pairing with the density r_T and the origin atom (1 - e^(-ρT))/ρ. -/
theorem coPoissonCutoff_pairing {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) {T : ℝ} (hT : 0 ≤ T)
    (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => coPoissonCutoffDensity ρ T x * φ x) ∧
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * renormalizedCombKernel t φ =
        (∫ x, coPoissonCutoffDensity ρ T x * φ x) + coPoissonCutoffAtom ρ T * φ 0 := by
  obtain ⟨hi1, he1⟩ := cutoffFamilyOne_pairing ρ hT φ
  obtain ⟨hi2, he2⟩ := cutoffFamilyTwo_pairing ρ hT φ
  set c : ℂ := (cexp ((1 - ρ) * T) - 1) / (1 - ρ) with hc
  have hsplit : (fun x => coPoissonCutoffDensity ρ T x * φ x) = fun x =>
      cutoffFamilyOne ρ T |x| * φ x + cutoffFamilyTwo ρ T |x| * φ x - c * φ x := by
    funext x; rw [cutoffFamily_density]; ring
  have hint : Integrable (fun x => coPoissonCutoffDensity ρ T x * φ x) := by
    rw [hsplit]; exact (hi1.add hi2).sub (φ.integrable.const_mul c)
  refine ⟨hint, ?_⟩
  have hρ1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hpt (t : ℝ) : cexp (-(ρ - 1 / 2) * t) * renormalizedCombKernel t φ =
      cexp (-(ρ - 1 / 2) * t) * coPoissonA t φ + cexp (-(ρ - 1 / 2) * t) * coPoissonA (-t) φ +
        φ 0 * cexp (-ρ * t) - (∫ x, φ x) * cexp ((1 - ρ) * t) := by
    rw [renormalizedCombKernel_apply_split, Complex.ofReal_exp, Complex.ofReal_exp]
    have e1 : cexp (-(ρ - 1 / 2) * t) * cexp (((-t / 2 : ℝ)) : ℂ) = cexp (-ρ * t) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : cexp (-(ρ - 1 / 2) * t) * cexp (((t / 2 : ℝ)) : ℂ) = cexp ((1 - ρ) * t) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (φ 0) * e1 - (∫ x, φ x) * e2
  have hcexp (z : ℂ) : Continuous (fun t : ℝ => cexp (z * t)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hA : Continuous (fun t : ℝ => cexp (-(ρ - 1 / 2) * t) * coPoissonA t φ) :=
    (hcexp _).mul (coPoissonA_continuous φ)
  have hB : Continuous (fun t : ℝ => cexp (-(ρ - 1 / 2) * t) * coPoissonA (-t) φ) :=
    (hcexp _).mul ((coPoissonA_continuous φ).comp continuous_neg)
  have hC : Continuous (fun t : ℝ => φ 0 * cexp (-ρ * t)) := continuous_const.mul (hcexp _)
  have hD : Continuous (fun t : ℝ => (∫ x, φ x) * cexp ((1 - ρ) * t)) :=
    continuous_const.mul (hcexp _)
  have hi12 : Integrable (fun x => cutoffFamilyOne ρ T |x| * φ x + cutoffFamilyTwo ρ T |x| * φ x) :=
    hi1.add hi2
  have hAB : Continuous (fun t : ℝ => cexp (-(ρ - 1 / 2) * t) * coPoissonA t φ +
      cexp (-(ρ - 1 / 2) * t) * coPoissonA (-t) φ) := hA.add hB
  have hABC : Continuous (fun t : ℝ => cexp (-(ρ - 1 / 2) * t) * coPoissonA t φ +
      cexp (-(ρ - 1 / 2) * t) * coPoissonA (-t) φ + φ 0 * cexp (-ρ * t)) := hAB.add hC
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub (hABC.intervalIntegrable _ _) (hD.intervalIntegrable _ _),
    intervalIntegral.integral_add (hAB.intervalIntegrable _ _) (hC.intervalIntegrable _ _),
    intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
    he1, he2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (neg_ne_zero.mpr hρ0), integral_exp_mul_complex hρ1', hsplit,
    integral_sub hi12 (φ.integrable.const_mul c), integral_add hi1 hi2,
    integral_const_mul]
  unfold coPoissonCutoffAtom
  rw [hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  generalize cexp (-ρ * T) = E1
  generalize cexp ((1 - ρ) * T) = E2
  field_simp
  ring

/-- The cutoff measure is the actual cutoff distribution on Schwartz tests. -/
theorem coPoissonCutoff_integral {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) {T : ℝ} (hT : 0 ≤ T)
    (φ : 𝓢(ℝ, ℂ)) :
    (coPoissonCutoff ρ T).integral φ =
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * renormalizedCombKernel t φ := by
  obtain ⟨hint, heq⟩ := coPoissonCutoff_pairing hρ0 hρ1 hT φ
  rw [heq]
  exact densityAtomMeasure_integral _ _ (measurable_coPoissonCutoffDensity ρ T)
    φ.continuous.aestronglyMeasurable hint

/-! ### Identification of V_λ with the limit measure on Schwartz tests -/

lemma norm_sum_natCast_cpow_le_card {S : Finset ℕ} {z : ℂ} (hz : z.re ≤ 0) (h0 : 0 ∉ S) :
    ‖∑ n ∈ S, (n : ℂ) ^ z‖ ≤ S.card := by
  refine (norm_sum_le _ _).trans ?_
  have hle : ∀ n ∈ S, ‖(n : ℂ) ^ z‖ ≤ 1 := fun n hn => by
    have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hn))
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn0) hz
  calc ∑ n ∈ S, ‖(n : ℂ) ^ z‖ ≤ S.card • (1 : ℝ) := Finset.sum_le_card_nsmul _ _ _ hle
    _ = S.card := by simp

lemma rpow_mul_floor_le {y c : ℝ} (hy : 0 < y) (hc : c ≤ 0) : y ^ c * (⌊y⌋₊ : ℝ) ≤ y := by
  rcases Nat.eq_zero_or_pos ⌊y⌋₊ with h | h
  · rw [h, Nat.cast_zero, mul_zero]; exact hy.le
  · have h1 : (1 : ℝ) ≤ y := (Nat.one_le_floor_iff y).mp h
    calc y ^ c * (⌊y⌋₊ : ℝ) ≤ 1 * y :=
          mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos h1 hc) (Nat.floor_le hy.le)
            (Nat.cast_nonneg _) zero_le_one
      _ = y := one_mul y

lemma finiteSumSrho_norm_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {y : ℝ} (hy : 0 < y) :
    ‖finiteSumSrho ρ y‖ ≤ 2 * y := by
  have hS0 : 0 ∉ Finset.Icc 1 ⌊y⌋₊ := by rw [Finset.mem_Icc]; omega
  have hcard : ((Finset.Icc 1 ⌊y⌋₊).card : ℝ) = ⌊y⌋₊ := by rw [Nat.card_Icc]; simp
  have hA := norm_sum_natCast_cpow_le_card (S := Finset.Icc 1 ⌊y⌋₊) (z := ρ - 1)
    (by simp; linarith) hS0
  have hB := norm_sum_natCast_cpow_le_card (S := Finset.Icc 1 ⌊y⌋₊) (z := -ρ)
    (by simp; linarith) hS0
  rw [hcard] at hA hB
  unfold finiteSumSrho coPoissonPowerSums
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have h1 := rpow_mul_floor_le hy (c := (-ρ).re) (by simp; linarith)
  have h2 := rpow_mul_floor_le hy (c := (ρ - 1).re) (by simp; linarith)
  have h3 := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hy.le (-ρ).re)
  have h4 := mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hy.le (ρ - 1).re)
  linarith

lemma coPoissonLimitDensity_norm_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ}
    (hx : x ≠ 0) :
    ‖coPoissonLimitDensity ρ x‖ ≤ 2 * |x| + ‖riemannZeta ρ‖ * |x| ^ (ρ.re - 1) + 1 / ‖1 - ρ‖ := by
  have hax : 0 < |x| := abs_pos.mpr hx
  unfold coPoissonLimitDensity
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (finiteSumSrho_norm_le h0 h1 hax) (le_of_eq ?_))) (le_of_eq ?_))
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hax]; simp
  · rw [norm_div, norm_one]

lemma coPoissonCutoffDensity_far_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T x : ℝ}
    (hT : 0 ≤ T) (hx : Real.exp T < |x|) :
    ‖coPoissonCutoffDensity ρ T x‖ ≤ |x| + |x| ^ 2 + (|x| + 1) / ‖1 - ρ‖ := by
  set y := |x| with hydef
  have hy1 : 1 ≤ y := (Real.one_le_exp hT).trans hx.le
  have hy : 0 < y := lt_of_lt_of_le one_pos hy1
  rw [cutoffFamily_density]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · unfold cutoffFamilyOne
    have hS0 : 0 ∉ Finset.Icc (max 1 ⌈y * Real.exp (-T)⌉₊) ⌊y⌋₊ := by
      rw [Finset.mem_Icc]; omega
    have hA := norm_sum_natCast_cpow_le_card (z := ρ - 1) (by simp; linarith) hS0
    have hcard : ((Finset.Icc (max 1 ⌈y * Real.exp (-T)⌉₊) ⌊y⌋₊).card : ℝ) ≤ ⌊y⌋₊ := by
      rw [Nat.card_Icc]; exact_mod_cast (by omega)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    calc y ^ (-ρ).re * ‖∑ n ∈ Finset.Icc (max 1 ⌈y * Real.exp (-T)⌉₊) ⌊y⌋₊, (n : ℂ) ^ (ρ - 1)‖
        ≤ y ^ (-ρ).re * (⌊y⌋₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (hA.trans hcard) (Real.rpow_nonneg hy.le _)
      _ ≤ y := rpow_mul_floor_le hy (by simp; linarith)
  · unfold cutoffFamilyTwo
    have hS0 : 0 ∉ Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp T⌋₊ := by rw [Finset.mem_Ioc]; omega
    have hA := norm_sum_natCast_cpow_le_card (z := -ρ) (by simp; linarith) hS0
    have hcard : ((Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp T⌋₊).card : ℝ) ≤ y * y := by
      rw [Nat.card_Ioc]
      calc ((⌊y * Real.exp T⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) ≤ (⌊y * Real.exp T⌋₊ : ℝ) := by
            exact_mod_cast Nat.sub_le _ _
        _ ≤ y * Real.exp T := Nat.floor_le (by positivity)
        _ ≤ y * y := mul_le_mul_of_nonneg_left hx.le hy.le
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hpow : y ^ (ρ - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by simp; linarith)
    calc y ^ (ρ - 1).re * ‖∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp T⌋₊, (n : ℂ) ^ (-ρ)‖
        ≤ 1 * (y * y) := mul_le_mul hpow (hA.trans hcard) (norm_nonneg _) zero_le_one
      _ = y ^ 2 := by ring
  · rw [norm_div]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, norm_one]
    have hre : ((1 - ρ) * (T : ℂ)).re = (1 - ρ.re) * T := by simp
    rw [hre]
    have : Real.exp ((1 - ρ.re) * T) ≤ y :=
      (Real.exp_le_exp.mpr (by nlinarith)).trans hx.le
    linarith

/-- The uniform majorant of the cutoff densities. -/
def coPoissonMajorant (ρ : ℂ) (x : ℝ) : ℝ :=
  (coPoissonErrorConst ρ + ‖riemannZeta ρ‖) * |x| ^ (ρ.re - 1) +
    (3 + 2 / ‖1 - ρ‖) * (1 + |x| + |x| ^ 2)

lemma coPoissonCutoffDensity_le_majorant {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T x : ℝ}
    (hT : 0 ≤ T) (hx : x ≠ 0) :
    ‖coPoissonCutoffDensity ρ T x‖ ≤ coPoissonMajorant ρ x := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have hp : 0 ≤ |x| ^ (ρ.re - 1) := Real.rpow_nonneg hax.le _
  have hM : 0 ≤ coPoissonErrorConst ρ := by unfold coPoissonErrorConst; positivity
  have hq : 0 ≤ 1 / ‖1 - ρ‖ := by positivity
  unfold coPoissonMajorant
  rcases le_or_gt |x| (Real.exp T) with hxT | hxT
  · have hd := coPoissonCutoff_sub_limit_le h0 h1 hT hx hxT
    have hR := coPoissonLimitDensity_norm_le h0 h1 hx
    have htri := norm_le_norm_add_norm_sub' (coPoissonCutoffDensity ρ T x)
      (coPoissonLimitDensity ρ x)
    have h2 : 2 / ‖1 - ρ‖ = 2 * (1 / ‖1 - ρ‖) := by ring
    rw [h2]
    nlinarith [sq_nonneg |x|, abs_nonneg x]
  · have hf := coPoissonCutoffDensity_far_le h0 h1 hT hxT
    have h2 : (|x| + 1) / ‖1 - ρ‖ = (|x| + 1) * (1 / ‖1 - ρ‖) := by ring
    rw [h2] at hf
    have h3 : 2 / ‖1 - ρ‖ = 2 * (1 / ‖1 - ρ‖) := by ring
    rw [h3]
    have hz : 0 ≤ (coPoissonErrorConst ρ + ‖riemannZeta ρ‖) * |x| ^ (ρ.re - 1) :=
      mul_nonneg (by positivity) hp
    nlinarith [sq_nonneg |x|, abs_nonneg x]

lemma integrable_abs_rpow_mul_schwartz {r : ℝ} (hr1 : -1 < r) (hr0 : r ≤ 0) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => |x| ^ r * ‖φ x‖) := by
  set C := SchwartzMap.seminorm ℂ 0 0 φ with hC
  have hg : Integrable (fun x : ℝ => (Icc (-1 : ℝ) 1).indicator (fun x => |x| ^ r * C) x + ‖φ x‖) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr
      ((integrableOn_abs_rpow_Icc hr1 zero_le_one).mul_const C)).add φ.integrable.norm
  refine hg.mono' ((continuous_abs.measurable.pow_const r).mul
    φ.continuous.norm.measurable).aestronglyMeasurable (Eventually.of_forall (fun x => ?_))
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (norm_nonneg _))]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have := mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ φ x)
      (Real.rpow_nonneg (abs_nonneg x) r)
    linarith [norm_nonneg (φ x)]
  · rw [Set.indicator_of_notMem hx, zero_add]
    have h1 : 1 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have := Real.rpow_le_one_of_one_le_of_nonpos h1.le hr0
    nlinarith [norm_nonneg (φ x)]

lemma integrable_majorant_mul_schwartz {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => coPoissonMajorant ρ x * ‖φ x‖) := by
  have hk (k : ℕ) : Integrable (fun x : ℝ => |x| ^ k * ‖φ x‖) := by
    simpa [Real.norm_eq_abs] using SchwartzMap.integrable_pow_mul volume φ k
  have ha := (integrable_abs_rpow_mul_schwartz (r := ρ.re - 1) (by linarith) (by linarith) φ).const_mul
    (coPoissonErrorConst ρ + ‖riemannZeta ρ‖)
  have hb := (((hk 0).add (hk 1)).add (hk 2)).const_mul (3 + 2 / ‖1 - ρ‖)
  refine (ha.add hb).congr (Eventually.of_forall (fun x => ?_))
  simp only [Pi.add_apply, coPoissonMajorant, pow_zero, pow_one, one_mul]
  ring

lemma integrable_coPoissonLimitDensity_mul {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) : Integrable (fun x => coPoissonLimitDensity ρ x * φ x) := by
  refine (integrable_majorant_mul_schwartz h0 h1 φ).mono'
    ((measurable_coPoissonLimitDensity ρ).mul φ.continuous.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_real] with x hx
  have hax : 0 < |x| := abs_pos.mpr hx
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ((coPoissonLimitDensity_norm_le h0 h1 hx).trans ?_)
    (norm_nonneg _)
  have hM : 0 ≤ coPoissonErrorConst ρ := by unfold coPoissonErrorConst; positivity
  have hp : 0 ≤ |x| ^ (ρ.re - 1) := Real.rpow_nonneg hax.le _
  have hq : 0 ≤ 1 / ‖1 - ρ‖ := by positivity
  unfold coPoissonMajorant
  have h3 : 2 / ‖1 - ρ‖ = 2 * (1 / ‖1 - ρ‖) := by ring
  rw [h3]
  nlinarith [sq_nonneg |x|, abs_nonneg x]

/-- (CP1.4) On every Schwartz test the entire family is the pairing with the limit measure:
V_(ρ-1/2)(φ) = ρ⁻¹ φ(0) + ∫ [S_ρ(|x|) + ζ(ρ)|x|^(ρ-1) + (1-ρ)⁻¹] φ(x) dx. -/
theorem coPoissonFamily_eq_limit {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily (ρ - 1 / 2) φ = (∫ x, coPoissonLimitDensity ρ x * φ x) + 1 / ρ * φ 0 := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hV : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) *
      renormalizedCombKernel t φ) atTop (𝓝 (coPoissonFamily (ρ - 1 / 2) φ)) := by
    rw [coPoissonFamily_apply]
    exact intervalIntegral_tendsto_integral_Ioi 0
      (renormalizedCombKernel_laplace_integrable _ φ) tendsto_id
  have hdens : Tendsto (fun T : ℝ => ∫ x, coPoissonCutoffDensity ρ T x * φ x) atTop
      (𝓝 (∫ x, coPoissonLimitDensity ρ x * φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => coPoissonMajorant ρ x * ‖φ x‖)
      (Eventually.of_forall (fun T => ((measurable_coPoissonCutoffDensity ρ T).mul
        φ.continuous.measurable).aestronglyMeasurable)) ?_
      (integrable_majorant_mul_schwartz h0 h1 φ) ?_
    · filter_upwards [eventually_ge_atTop 0] with T hT
      filter_upwards [ae_ne_zero_real] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (coPoissonCutoffDensity_le_majorant h0 h1 hT hx)
        (norm_nonneg _)
    · filter_upwards [ae_ne_zero_real] with x hx
      have h := coPoissonCutoff_tendsto_pointwise h0 h1 hx
      have h' : Tendsto (fun T : ℝ => coPoissonCutoffDensity ρ T x) atTop
          (𝓝 (coPoissonLimitDensity ρ x)) := tendsto_iff_norm_sub_tendsto_zero.mpr h
      exact h'.mul_const (φ x)
  have hatom : Tendsto (fun T : ℝ => coPoissonCutoffAtom ρ T) atTop (𝓝 (1 / ρ)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    simp_rw [coPoissonCutoffAtom_sub_norm]
    have ht : Tendsto (fun T : ℝ => Real.exp (-(ρ.re * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h0)
    simpa using ht.div_const ‖ρ‖
  have hcut : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) *
      renormalizedCombKernel t φ) atTop
      (𝓝 ((∫ x, coPoissonLimitDensity ρ x * φ x) + 1 / ρ * φ 0)) := by
    refine Tendsto.congr' ?_ (hdens.add (hatom.mul_const (φ 0)))
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact ((coPoissonCutoff_pairing hρ0 hρ1 hT φ).2).symm
  exact tendsto_nhds_unique hV hcut

/-- The same identification through the measure object. -/
theorem coPoissonFamily_eq_limitMeasure {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily (ρ - 1 / 2) φ = (coPoissonLimitMeasure ρ h0).integral φ := by
  rw [coPoissonFamily_eq_limit h0 h1 φ]
  exact (densityAtomMeasure_integral _ _ (measurable_coPoissonLimitDensity ρ)
    φ.continuous.aestronglyMeasurable (integrable_coPoissonLimitDensity_mul h0 h1 φ)).symm


/-- R1-CP1 order zero. On the open strip 0 < Re ρ < 1 the actual cutoffs
∫_0^T e^(-(ρ-1/2)t) K_t dt are the locally finite complex measures r_T dx + ((1-e^(-ρT))/ρ) δ₀,
they converge in local total variation (origin atom included) to
ρ⁻¹ δ₀ + [S_ρ(|x|) + ζ(ρ)|x|^(ρ-1) + (1-ρ)⁻¹] dx, and the entire family V_(ρ-1/2) is that
measure on every Schwartz test. -/
theorem renormalized_copoisson_order_zero (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (∀ T : ℝ, 0 ≤ T → ∀ φ : 𝓢(ℝ, ℂ), (coPoissonCutoff ρ T).integral φ =
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * renormalizedCombKernel t φ) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ φ : 𝓢(ℝ, ℂ), (coPoissonCutoff ρ T).integral φ =
      (∫ x, coPoissonCutoffDensity ρ T x * φ x) + (1 - cexp (-ρ * T)) / ρ * φ 0) ∧
    (∀ (T : ℝ) (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ), MeasurableSet E →
      (coPoissonCutoff ρ T).compactRestriction K hK E =
        (∫ x in E ∩ K, coPoissonCutoffDensity ρ T x) +
          (E ∩ K).indicator (fun _ => (1 - cexp (-ρ * T)) / ρ) 0) ∧
    (∀ (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ), MeasurableSet E →
      (coPoissonLimitMeasure ρ h0).compactRestriction K hK E =
        (∫ x in E ∩ K, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) +
          1 / (1 - ρ))) + (E ∩ K).indicator (fun _ => 1 / ρ) 0) ∧
    (∀ (K : Set ℝ) (hK : IsCompact K), Tendsto (fun T : ℝ =>
      ((coPoissonCutoff ρ T).compactRestriction K hK -
        (coPoissonLimitMeasure ρ h0).compactRestriction K hK).variation.real univ) atTop (𝓝 0)) ∧
    LocalVariationConvergence (fun n : ℕ => coPoissonCutoff ρ n) (coPoissonLimitMeasure ρ h0) ∧
    (∀ φ : 𝓢(ℝ, ℂ), coPoissonFamily (ρ - 1 / 2) φ = (coPoissonLimitMeasure ρ h0).integral φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), coPoissonFamily (ρ - 1 / 2) φ =
      (∫ x, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ)) * φ x) +
        1 / ρ * φ 0) := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  refine ⟨fun T hT φ => coPoissonCutoff_integral hρ0 hρ1 hT φ, fun T hT φ => ?_,
    fun T K hK E hE => densityAtomMeasure_compactRestriction_apply _ _ _ hK hE,
    fun K hK E hE => densityAtomMeasure_compactRestriction_apply _ _ _ hK hE,
    fun K hK => coPoissonCutoff_localVariation_tendsto h0 h1 K hK,
    coPoissonCutoff_localVariationConvergence h0 h1,
    fun φ => coPoissonFamily_eq_limitMeasure h0 h1 φ,
    fun φ => coPoissonFamily_eq_limit h0 h1 φ⟩
  rw [coPoissonCutoff_integral hρ0 hρ1 hT φ]
  exact (coPoissonCutoff_pairing hρ0 hρ1 hT φ).2

end OrderZero

section ZeroMeasure
open scoped ENNReal NNReal SchwartzMap FourierTransform

/-! ### The normalization constant and the punctured integer lattice -/

/-- b_ρ = (1 - 2ρ)/(ρ(1 - ρ)). -/
def normalizationBrho (ρ : ℂ) : ℂ := (1 - 2 * ρ) / (ρ * (1 - ρ))

lemma coPoissonOriginNormalizer_eq_brho {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    coPoissonOriginNormalizer ρ = normalizationBrho ρ := coPoisson_normalizer ρ h0 h1

lemma normalizationBrho_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hh : ρ ≠ 1 / 2) :
    normalizationBrho ρ ≠ 0 := by
  unfold normalizationBrho
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  refine div_ne_zero ?_ (mul_ne_zero h0 h1')
  intro h
  apply hh
  linear_combination -(1 / 2 : ℂ) * h

/-- The punctured integer lattice Σ_(n≠0) δ_n, the comb D_0 with its origin atom removed. -/
def puncturedLattice : Measure ℝ := (dilatedCombMeasure 0).restrict {0}ᶜ

instance puncturedLattice_locallyFinite : IsLocallyFiniteMeasure puncturedLattice := by
  unfold puncturedLattice
  infer_instance

lemma count_neg_preimage (A : Set ℤ) :
    Measure.count ((fun n : ℤ => -n) ⁻¹' A) = Measure.count A := by
  rw [Measure.count_apply (MeasurableSet.of_discrete), Measure.count_apply (MeasurableSet.of_discrete)]
  have h : (fun n : ℤ => -n) ⁻¹' A = (fun n : ℤ => -n) '' A := by
    rw [Set.image_neg_eq_neg]; rfl
  rw [h, neg_injective.encard_image]

lemma dilatedCombMeasure_map_neg (t : ℝ) :
    Measure.map (fun x : ℝ => -x) (dilatedCombMeasure t) = dilatedCombMeasure t := by
  unfold dilatedCombMeasure scaledLatticeMeasure
  rw [Measure.map_smul]
  congr 1
  ext s hs
  rw [Measure.map_apply measurable_neg hs,
    Measure.map_apply (scaledLatticePoint_measurable t) (measurable_neg hs),
    Measure.map_apply (scaledLatticePoint_measurable t) hs]
  have hpre : scaledLatticePoint t ⁻¹' ((fun x : ℝ => -x) ⁻¹' s) =
      (fun n : ℤ => -n) ⁻¹' (scaledLatticePoint t ⁻¹' s) := by
    ext n; simp [scaledLatticePoint]
  rw [hpre, count_neg_preimage]

lemma puncturedLattice_map_neg :
    Measure.map (fun x : ℝ => -x) puncturedLattice = puncturedLattice := by
  have hs : MeasurableSet ({0}ᶜ : Set ℝ) := (measurableSet_singleton 0).compl
  have hpre : (fun x : ℝ => -x) ⁻¹' ({0}ᶜ : Set ℝ) = {0}ᶜ := by ext x; simp
  unfold puncturedLattice
  conv_lhs => rw [← hpre]
  rw [← Measure.restrict_map measurable_neg hs, dilatedCombMeasure_map_neg]

lemma puncturedLattice_gap : puncturedLattice (Ioo (-1) 1) = 0 := by
  unfold puncturedLattice
  rw [Measure.restrict_apply measurableSet_Ioo, ← Set.sdiff_eq]
  have h := dilatedCombMeasure_punctured_gap 0
  rwa [Real.exp_zero] at h

lemma puncturedLattice_one : puncturedLattice {1} = 1 := by
  unfold puncturedLattice
  rw [Measure.restrict_apply (measurableSet_singleton 1)]
  have h1 : ({1} : Set ℝ) ∩ {0}ᶜ = {scaledLatticePoint 0 1} := by
    ext x; simp [scaledLatticePoint]
  rw [h1, dilatedCombMeasure_atom]
  simp

lemma puncturedLattice_linearGrowth : Zeta23.OPICA.LinearMassGrowth puncturedLattice :=
  (dilatedCombMeasure_linearGrowth 0).mono Measure.restrict_le_self

lemma integerRange_null : volume (Set.range (fun n : ℤ => (n : ℝ))) = 0 :=
  (Set.countable_range _).measure_zero volume

lemma puncturedLattice_support : puncturedLattice (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0 := by
  have hD : dilatedCombMeasure 0 (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0 := by
    unfold dilatedCombMeasure scaledLatticeMeasure
    rw [Measure.smul_apply, Measure.map_apply (scaledLatticePoint_measurable 0)
      (Set.countable_range _).measurableSet.compl]
    have hpre : scaledLatticePoint 0 ⁻¹' (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = ∅ := by
      ext n; simp [scaledLatticePoint]
    rw [hpre]; simp
  exact le_antisymm ((Measure.restrict_le_self (μ := dilatedCombMeasure 0) (s := {0}ᶜ) _).trans
    hD.le) zero_le

/-! ### The normalized density -/

lemma measurable_finiteSumSrho_abs (ρ : ℂ) : Measurable (fun x : ℝ => finiteSumSrho ρ |x|) := by
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have h1 := measurable_natPair_sum'
    (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (n : ℂ) ^ (ρ - 1)) habs habs
  have h2 := measurable_natPair_sum'
    (fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (n : ℂ) ^ (-ρ)) habs habs
  exact ((measurable_abs_cpow _).mul h1).sub ((measurable_abs_cpow _).mul h2)

/-- One power-sum term: y^c Σ_(n ≤ ⌊y⌋) n^(-s) is bounded on y ≥ 1 when c = s - 1. -/
lemma rpow_mul_partialZeta_le {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1) (hs1 : s ≠ 1) {y : ℝ}
    (hN : 1 ≤ ⌊y⌋₊) :
    ‖((y : ℝ) : ℂ) ^ (s - 1) * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℂ) ^ (-s)‖ ≤
      1 / ‖1 - s‖ + ‖riemannZeta s‖ + (1 / 2 + ‖s‖ / s.re) := by
  set N := ⌊y⌋₊ with hNdef
  have hy1 : (1 : ℝ) ≤ y := (Nat.one_le_floor_iff y).mp hN
  have hy : 0 < y := lt_of_lt_of_le one_pos hy1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy.le
  have he := partialZeta_error_nat hσ hs1 hN
  have hNs : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ = (N : ℝ) ^ (1 - s.re) / ‖1 - s‖ := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]; simp
  have hsum : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤
      (N : ℝ) ^ (1 - s.re) / ‖1 - s‖ + ‖riemannZeta s‖ + (1 / 2 + ‖s‖ / s.re) := by
    have hle : (N : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
    have hC : 0 ≤ 1 / 2 + ‖s‖ / s.re := by positivity
    have h3 : (1 / 2 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) ≤ 1 / 2 + ‖s‖ / s.re := by
      nlinarith [Real.rpow_nonneg hNpos.le (-s.re)]
    calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
        ≤ ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s‖ +
            ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ + ‖riemannZeta s‖ := by
          have h3' : ‖(∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) -
              riemannZeta s) + (N : ℂ) ^ (1 - s) / (1 - s) + riemannZeta s‖ ≤
              ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) - riemannZeta s‖ +
                ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ + ‖riemannZeta s‖ := norm_add₃_le
          have hid : (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) - (N : ℂ) ^ (1 - s) / (1 - s) -
              riemannZeta s) + (N : ℂ) ^ (1 - s) / (1 - s) + riemannZeta s =
              ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by ring
          rw [hid] at h3'
          exact h3'
      _ ≤ _ := by rw [hNs]; linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (s - 1).re = s.re - 1 := by simp
  rw [hre]
  have hp1 : y ^ (s.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have hp2 : y ^ (s.re - 1) * (N : ℝ) ^ (1 - s.re) ≤ 1 := by
    have h := Real.rpow_le_rpow hNpos.le hNy (by linarith : 0 ≤ 1 - s.re)
    have h' : y ^ (s.re - 1) * y ^ (1 - s.re) = 1 := by
      rw [← Real.rpow_add hy]; simp
    calc y ^ (s.re - 1) * (N : ℝ) ^ (1 - s.re) ≤ y ^ (s.re - 1) * y ^ (1 - s.re) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hy.le _)
      _ = 1 := h'
  have hq : 0 ≤ ‖riemannZeta s‖ + (1 / 2 + ‖s‖ / s.re) := by positivity
  have hp0 : 0 ≤ y ^ (s.re - 1) := Real.rpow_nonneg hy.le _
  calc y ^ (s.re - 1) * ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖
      ≤ y ^ (s.re - 1) * ((N : ℝ) ^ (1 - s.re) / ‖1 - s‖ + ‖riemannZeta s‖ +
          (1 / 2 + ‖s‖ / s.re)) := mul_le_mul_of_nonneg_left hsum hp0
    _ = y ^ (s.re - 1) * (N : ℝ) ^ (1 - s.re) * (1 / ‖1 - s‖) +
          y ^ (s.re - 1) * (‖riemannZeta s‖ + (1 / 2 + ‖s‖ / s.re)) := by ring
    _ ≤ 1 * (1 / ‖1 - s‖) + 1 * (‖riemannZeta s‖ + (1 / 2 + ‖s‖ / s.re)) := by
        gcongr
    _ = _ := by ring

/-- S_ρ is bounded on [0, ∞) (paper: S_ρ(x) = O_ρ(1) for x ≥ 1, S_ρ = 0 on [0, 1)). -/
def finiteSumSrhoBound (ρ : ℂ) : ℝ :=
  (1 / ‖1 - (1 - ρ)‖ + ‖riemannZeta (1 - ρ)‖ + (1 / 2 + ‖1 - ρ‖ / (1 - ρ).re)) +
    (1 / ‖1 - ρ‖ + ‖riemannZeta ρ‖ + (1 / 2 + ‖ρ‖ / ρ.re))

lemma finiteSumSrho_norm_le_bound {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (y : ℝ) :
    ‖finiteSumSrho ρ y‖ ≤ finiteSumSrhoBound ρ := by
  have hB : 0 ≤ finiteSumSrhoBound ρ := by
    unfold finiteSumSrhoBound
    have : 0 < (1 - ρ).re := by simp; linarith
    positivity
  rcases Nat.eq_zero_or_pos ⌊y⌋₊ with hN | hN
  · unfold finiteSumSrho coPoissonPowerSums
    rw [hN]; simpa using hB
  · have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
    have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
    have hA := rpow_mul_partialZeta_le (s := 1 - ρ) (by simp; linarith) (by simp; linarith)
      (fun h => hρ0 (by linear_combination -h)) hN
    have hC := rpow_mul_partialZeta_le (s := ρ) h0 h1 hρ1 hN
    rw [show (1 - ρ) - 1 = -ρ by ring, show -(1 - ρ) = ρ - 1 by ring] at hA
    unfold finiteSumSrho coPoissonPowerSums finiteSumSrhoBound
    exact (norm_sub_le _ _).trans (add_le_add hA hC)

lemma measurable_coPoissonComplexDensity (ρ : ℂ) : Measurable (coPoissonComplexDensity ρ) :=
  (measurable_finiteSumSrho_abs ρ).div_const _

lemma coPoissonComplexDensity_small (ρ : ℂ) {x : ℝ} (hx : |x| < 1) :
    coPoissonComplexDensity ρ x = 0 := by
  have hf : ⌊|x|⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [coPoissonComplexDensity, coPoissonPowerSums, hf]

lemma coPoissonComplexDensity_neg (ρ : ℂ) (x : ℝ) :
    coPoissonComplexDensity ρ (-x) = coPoissonComplexDensity ρ x := by
  simp [coPoissonComplexDensity]

lemma locallyIntegrable_coPoissonComplexDensity (ρ : ℂ) :
    LocallyIntegrable (coPoissonComplexDensity ρ) volume := by
  refine locallyIntegrable_of_abs_le_bound (measurable_coPoissonComplexDensity ρ) (fun R _ => ?_)
  obtain ⟨M, hM⟩ := finiteSumSrho_abs_bound ρ R
  refine ⟨M / ‖coPoissonOriginNormalizer ρ‖, fun x hx => ?_⟩
  unfold coPoissonComplexDensity
  rw [norm_div]
  exact div_le_div_of_nonneg_right (hM x hx) (norm_nonneg _)

lemma coPoissonComplexDensity_norm_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (x : ℝ) :
    ‖coPoissonComplexDensity ρ x‖ ≤ finiteSumSrhoBound ρ / ‖coPoissonOriginNormalizer ρ‖ := by
  unfold coPoissonComplexDensity
  rw [norm_div]
  exact div_le_div_of_nonneg_right (finiteSumSrho_norm_le_bound h0 h1 _) (norm_nonneg _)

lemma volume_mutuallySingular_puncturedLattice : volume ⟂ₘ puncturedLattice :=
  ⟨Set.range (fun n : ℤ => (n : ℝ)), (Set.countable_range _).measurableSet, integerRange_null,
    puncturedLattice_support⟩

/-- The normalized actual zero measure (CP1.7)/b_ρ = (S_ρ(|x|)/b_ρ) dx - Σ_(n≠0) δ_n, with its
canonical Jordan pairs. -/
def zeroMeasure (ρ : ℂ) : LocallyFiniteComplexMeasure where
  rePart :=
    { positive := volume.withDensity (fun x => ENNReal.ofReal (coPoissonRealDensity ρ x))
      negative := volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) +
        puncturedLattice
      positive_locallyFinite :=
        isLocallyFinite_withDensity_ofReal (locallyIntegrable_complex_re
          (locallyIntegrable_coPoissonComplexDensity ρ))
      negative_locallyFinite := by
        have hneg : LocallyIntegrable (fun x => -coPoissonRealDensity ρ x) volume :=
          (locallyIntegrable_complex_re (locallyIntegrable_coPoissonComplexDensity ρ)).neg
        have := isLocallyFinite_withDensity_ofReal hneg
        exact locallyFiniteMeasure_add _ _
      mutuallySingular :=
        (withDensity_ofReal_mutuallySingular (Complex.measurable_re.comp
          (measurable_coPoissonComplexDensity ρ))).add_right
          (volume_mutuallySingular_puncturedLattice.mono_ac
            (withDensity_absolutelyContinuous _ _) Measure.AbsolutelyContinuous.rfl) }
  imPart :=
    { positive := volume.withDensity (fun x => ENNReal.ofReal (coPoissonComplexDensity ρ x).im)
      negative := volume.withDensity (fun x => ENNReal.ofReal (-(coPoissonComplexDensity ρ x).im))
      positive_locallyFinite :=
        isLocallyFinite_withDensity_ofReal (locallyIntegrable_complex_im
          (locallyIntegrable_coPoissonComplexDensity ρ))
      negative_locallyFinite := by
        have hneg : LocallyIntegrable (fun x => -(coPoissonComplexDensity ρ x).im) volume :=
          (locallyIntegrable_complex_im (locallyIntegrable_coPoissonComplexDensity ρ)).neg
        exact isLocallyFinite_withDensity_ofReal hneg
      mutuallySingular := withDensity_ofReal_mutuallySingular (Complex.measurable_im.comp
          (measurable_coPoissonComplexDensity ρ)) }

/-! ### Gap, origin, atoms, evenness and growth of the zero measure -/

lemma withDensity_ofReal_gap {u : ℝ → ℝ} (hu : ∀ x, |x| < 1 → u x = 0) :
    volume.withDensity (fun x => ENNReal.ofReal (u x)) (Ioo (-1) 1) = 0 := by
  rw [withDensity_apply _ measurableSet_Ioo]
  refine (setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)).trans (lintegral_zero)
  show ENNReal.ofReal (u x) = 0
  rw [hu x (abs_lt.mpr hx), ENNReal.ofReal_zero]

lemma withDensity_singleton_zero (u : ℝ → ℝ≥0∞) (a : ℝ) : volume.withDensity u {a} = 0 := by
  rw [withDensity_apply _ (measurableSet_singleton a)]
  exact setLIntegral_measure_zero _ _ (measure_singleton a)

lemma map_neg_withDensity_even {u : ℝ → ℝ≥0∞} (hu : Measurable u) (heven : ∀ x, u (-x) = u x) :
    Measure.map (fun x : ℝ => -x) (volume.withDensity u) = volume.withDensity u := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage hs hu
  simp only [heven] at h
  exact h

lemma zeroMeasure_density_gap (ρ : ℂ) {x : ℝ} (hx : |x| < 1) :
    coPoissonRealDensity ρ x = 0 ∧ (coPoissonComplexDensity ρ x).im = 0 := by
  unfold coPoissonRealDensity; rw [coPoissonComplexDensity_small ρ hx]; simp

/-- Exact open unit gap: all four Jordan parts vanish on (-1, 1). -/
theorem zeroMeasure_gap (ρ : ℂ) : (zeroMeasure ρ).variationControl (Ioo (-1) 1) = 0 := by
  have h1 := withDensity_ofReal_gap (u := fun x => coPoissonRealDensity ρ x)
    (fun x hx => (zeroMeasure_density_gap ρ hx).1)
  have h2 := withDensity_ofReal_gap (u := fun x => -coPoissonRealDensity ρ x)
    (fun x hx => by rw [(zeroMeasure_density_gap ρ hx).1, neg_zero])
  have h3 := withDensity_ofReal_gap (u := fun x => (coPoissonComplexDensity ρ x).im)
    (fun x hx => (zeroMeasure_density_gap ρ hx).2)
  have h4 := withDensity_ofReal_gap (u := fun x => -(coPoissonComplexDensity ρ x).im)
    (fun x hx => by rw [(zeroMeasure_density_gap ρ hx).2, neg_zero])
  change ((zeroMeasure ρ).rePart.positive + (zeroMeasure ρ).rePart.negative +
    ((zeroMeasure ρ).imPart.positive + (zeroMeasure ρ).imPart.negative)) (Ioo (-1) 1) = 0
  simp only [Measure.add_apply, zeroMeasure]
  rw [h1, h2, h3, h4, puncturedLattice_gap]
  simp

theorem zeroMeasure_origin (ρ : ℂ) : (zeroMeasure ρ).variationControl {0} = 0 :=
  measure_mono_null (fun x hx => by
    simp only [mem_singleton_iff] at hx; subst hx; norm_num) (zeroMeasure_gap ρ)

/-- The atom at 1 is -1: the real negative part carries mass 1 there and nothing else does. -/
theorem zeroMeasure_atom_one (ρ : ℂ) :
    (zeroMeasure ρ).rePart.positive {1} = 0 ∧ (zeroMeasure ρ).rePart.negative {1} = 1 ∧
      (zeroMeasure ρ).imPart.positive {1} = 0 ∧ (zeroMeasure ρ).imPart.negative {1} = 0 := by
  refine ⟨withDensity_singleton_zero _ 1, ?_, withDensity_singleton_zero _ 1,
    withDensity_singleton_zero _ 1⟩
  change (volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) +
    puncturedLattice) {1} = 1
  rw [Measure.add_apply, withDensity_singleton_zero, puncturedLattice_one, zero_add]

/-- Evenness of all four canonical Jordan parts. -/
theorem zeroMeasure_even (ρ : ℂ) :
    Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.positive = (zeroMeasure ρ).rePart.positive ∧
    Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.negative = (zeroMeasure ρ).rePart.negative ∧
    Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.positive = (zeroMeasure ρ).imPart.positive ∧
    Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.negative =
      (zeroMeasure ρ).imPart.negative := by
  have hm := measurable_coPoissonComplexDensity ρ
  have hre : Measurable (fun x => coPoissonRealDensity ρ x) := Complex.measurable_re.comp hm
  have him : Measurable (fun x => (coPoissonComplexDensity ρ x).im) := Complex.measurable_im.comp hm
  have hev (x : ℝ) : coPoissonRealDensity ρ (-x) = coPoissonRealDensity ρ x := by
    unfold coPoissonRealDensity; rw [coPoissonComplexDensity_neg]
  have hevi (x : ℝ) : (coPoissonComplexDensity ρ (-x)).im = (coPoissonComplexDensity ρ x).im := by
    rw [coPoissonComplexDensity_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact map_neg_withDensity_even (ENNReal.measurable_ofReal.comp hre) (fun x => by simp only [hev])
  · change Measure.map (fun x : ℝ => -x) (volume.withDensity
      (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) + puncturedLattice) = _
    have hw := map_neg_withDensity_even (u := fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x))
      (ENNReal.measurable_ofReal.comp hre.neg) (fun x => by simp only [hev])
    rw [Measure.map_add _ _ measurable_neg, puncturedLattice_map_neg]
    erw [hw]
    rfl
  · exact map_neg_withDensity_even (ENNReal.measurable_ofReal.comp him) (fun x => by simp only [hevi])
  · exact map_neg_withDensity_even (u := fun x => ENNReal.ofReal (-(coPoissonComplexDensity ρ x).im))
      (ENNReal.measurable_ofReal.comp him.neg) (fun x => by simp only [hevi])

lemma linearMassGrowth_add {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hμ : Zeta23.OPICA.LinearMassGrowth μ) (hν : Zeta23.OPICA.LinearMassGrowth ν) :
    Zeta23.OPICA.LinearMassGrowth (μ + ν) := by
  obtain ⟨C, hC, hb⟩ := hμ
  obtain ⟨D, hD, hd⟩ := hν
  refine ⟨C + D, add_nonneg hC hD, fun R hR => ?_⟩
  rw [measureReal_add_apply isCompact_Icc.measure_lt_top.ne isCompact_Icc.measure_lt_top.ne]
  linarith [hb R hR, hd R hR]

lemma linearMassGrowth_smul_volume (c : ℝ≥0) :
    Zeta23.OPICA.LinearMassGrowth ((c : ℝ≥0∞) • (volume : Measure ℝ)) := by
  refine ⟨2 * c, by positivity, fun R hR => ?_⟩
  rw [Measure.real, Measure.smul_apply, Real.volume_Icc, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (by linarith)]
  nlinarith [c.coe_nonneg]

/-- Linear total-variation growth (the paper: S_ρ = O_ρ(1), lattice mass O(R)). -/
theorem zeroMeasure_hasLinearGrowth {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (zeroMeasure ρ).HasLinearGrowth := by
  set B : ℝ := finiteSumSrhoBound ρ / ‖coPoissonOriginNormalizer ρ‖ with hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (coPoissonComplexDensity_norm_le h0 h1 0)
  set c : ℝ≥0 := B.toNNReal with hc
  have hdom (u : ℝ → ℝ) (hu : ∀ x, u x ≤ B) :
      volume.withDensity (fun x => ENNReal.ofReal (u x)) ≤ (c : ℝ≥0∞) • volume := by
    rw [← withDensity_const]
    refine withDensity_mono (Eventually.of_forall (fun x => ?_))
    change ENNReal.ofReal (u x) ≤ ENNReal.ofReal B
    exact ENNReal.ofReal_le_ofReal (hu x)
  have hg (x : ℝ) := coPoissonComplexDensity_norm_le h0 h1 x
  have hle : (zeroMeasure ρ).variationControl ≤
      (((c : ℝ≥0∞) • volume + ((c : ℝ≥0∞) • volume + puncturedLattice)) +
        ((c : ℝ≥0∞) • volume + (c : ℝ≥0∞) • volume)) := by
    change (zeroMeasure ρ).rePart.positive + (zeroMeasure ρ).rePart.negative +
      ((zeroMeasure ρ).imPart.positive + (zeroMeasure ρ).imPart.negative) ≤ _
    refine add_le_add (add_le_add ?_ (add_le_add ?_ le_rfl)) (add_le_add ?_ ?_)
    · exact hdom _ (fun x => (Complex.re_le_norm _).trans (hg x))
    · exact hdom _ (fun x => (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hg x)))
    · exact hdom _ (fun x => (Complex.im_le_norm _).trans (hg x))
    · exact hdom _ (fun x => (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (hg x)))
  have : IsFiniteMeasureOnCompacts ((c : ℝ≥0∞) • (volume : Measure ℝ)) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.coe_ne_top
  have hv := linearMassGrowth_smul_volume c
  have hL := puncturedLattice_linearGrowth
  have hgrowth := linearMassGrowth_add (linearMassGrowth_add hv (linearMassGrowth_add hv hL))
    (linearMassGrowth_add hv hv)
  exact hgrowth.mono hle

/-! ### Pairing of the zero measure and its identification with (CP1.7) -/

lemma integral_withDensity_ofReal {h : ℝ → ℝ} (hm : Measurable h) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hf : Integrable (fun x => (h x : ℂ) * f x)) :
    Integrable f (volume.withDensity fun x => ENNReal.ofReal (h x)) ∧
      ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (h x)) =
        ∫ x, ((max (h x) 0 : ℝ) : ℂ) * f x := by
  have he : densityAtomPart h 0 = volume.withDensity fun x => ENNReal.ofReal (h x) := by
    simp [densityAtomPart]
  have hd := integral_densityAtomPart hm 0 hfm hf
  rw [he] at hd
  refine ⟨hd.1, hd.2.trans ?_⟩
  simp

lemma integral_max_sub_max {u : ℝ → ℝ} (hum : Measurable u) {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hu : Integrable (fun x => (u x : ℂ) * f x)) :
    (∫ x, ((max (u x) 0 : ℝ) : ℂ) * f x) - (∫ x, ((max (-u x) 0 : ℝ) : ℂ) * f x) =
      ∫ x, (u x : ℂ) * f x := by
  have hum' : Measurable (fun x => -u x) := hum.neg
  have hb (v : ℝ → ℝ) (hv : Measurable v) (hle : ∀ x, |v x| ≤ |u x|) :
      Integrable (fun x => (v x : ℂ) * f x) := by
    refine hu.mono ((Complex.measurable_ofReal.comp hv).aestronglyMeasurable.mul hfm)
      (Eventually.of_forall (fun x => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle x) (norm_nonneg _)
  have hip := hb (fun x => max (u x) 0) (hum.max measurable_const) (fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _))
  have hin := hb (fun x => max (-u x) 0) (hum'.max measurable_const) (fun x => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (neg_le_abs _) (abs_nonneg _))
  rw [← integral_sub hip hin]
  congr 1
  funext x
  rw [← sub_mul]
  congr 1
  rcases le_total 0 (u x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -u x ≤ 0)]; simp
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -u x)]; push_cast; ring

lemma integral_dilatedCombMeasure_zero (φ : 𝓢(ℝ, ℂ)) :
    ∫ x, φ x ∂dilatedCombMeasure 0 = dilatedCombDistribution 0 φ := by
  rw [dilatedCombDistribution, Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
  simp only [dilatedCombJordan, localJordanDifference, Measure.sub_zero, Measure.zero_sub,
    integral_zero_measure, sub_zero]

lemma integral_puncturedLattice (φ : 𝓢(ℝ, ℂ)) :
    Integrable φ puncturedLattice ∧
      ∫ x, φ x ∂puncturedLattice = ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n := by
  have hD : Integrable φ (dilatedCombMeasure 0) :=
    (scaledLatticeMeasure_integrable_schwartz 0 φ).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hD.restrict, ?_⟩
  have hsplit := integral_add_compl (measurableSet_singleton (0 : ℝ)) hD
  rw [integral_singleton, measureReal_def, dilatedCombMeasure_origin] at hsplit
  simp only [zero_div, Real.exp_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] at hsplit
  have hA := coPoissonA_apply 0 φ
  rw [coPoissonA, sub_apply, smul_apply, TemperedDistribution.delta_apply] at hA
  simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_smul, one_mul] at hA
  unfold puncturedLattice
  rw [integral_dilatedCombMeasure_zero] at hsplit
  rw [← hA]
  linear_combination hsplit

/-- Pairing of the zero measure on Schwartz tests: ∫ (S_ρ(|x|)/b_ρ) φ - Σ_(n≠0) φ(n). -/
theorem zeroMeasure_integral {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    (zeroMeasure ρ).integral φ =
      (∫ x, coPoissonComplexDensity ρ x * φ x) - ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n := by
  set g := coPoissonComplexDensity ρ with hgdef
  have hgm : Measurable g := measurable_coPoissonComplexDensity ρ
  have hfm : AEStronglyMeasurable (fun x => φ x) volume := φ.continuous.aestronglyMeasurable
  have hgφ : Integrable (fun x => g x * φ x) := by
    refine (φ.integrable.norm.const_mul (finiteSumSrhoBound ρ / ‖coPoissonOriginNormalizer ρ‖)).mono'
      (hgm.aestronglyMeasurable.mul hfm) (Eventually.of_forall (fun x => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (coPoissonComplexDensity_norm_le h0 h1 x) (norm_nonneg _)
  have hb (v : ℝ → ℝ) (hv : Measurable v) (hle : ∀ x, |v x| ≤ ‖g x‖) :
      Integrable (fun x => (v x : ℂ) * φ x) := by
    refine hgφ.mono ((Complex.measurable_ofReal.comp hv).aestronglyMeasurable.mul hfm)
      (Eventually.of_forall (fun x => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle x) (norm_nonneg _)
  have hre : Measurable (fun x => (g x).re) := Complex.measurable_re.comp hgm
  have him : Measurable (fun x => (g x).im) := Complex.measurable_im.comp hgm
  have hire := hb _ hre (fun x => Complex.abs_re_le_norm _)
  have hiim := hb _ him (fun x => Complex.abs_im_le_norm _)
  have hr1 := integral_withDensity_ofReal hre hfm hire
  have hre' : Measurable (fun x => -(g x).re) := hre.neg
  have him' : Measurable (fun x => -(g x).im) := him.neg
  have hr2 := integral_withDensity_ofReal hre' hfm (hb _ hre' (fun x => by
    rw [abs_neg]; exact Complex.abs_re_le_norm _))
  have hi1 := integral_withDensity_ofReal him hfm hiim
  have hi2 := integral_withDensity_ofReal him' hfm (hb _ him' (fun x => by
    rw [abs_neg]; exact Complex.abs_im_le_norm _))
  obtain ⟨hL, hLint⟩ := integral_puncturedLattice φ
  unfold LocallyFiniteComplexMeasure.integral
  change ((∫ x, φ x ∂volume.withDensity fun x => ENNReal.ofReal (g x).re) -
      (∫ x, φ x ∂(volume.withDensity (fun x => ENNReal.ofReal (-(g x).re)) + puncturedLattice))) +
    I * ((∫ x, φ x ∂volume.withDensity fun x => ENNReal.ofReal (g x).im) -
      (∫ x, φ x ∂volume.withDensity fun x => ENNReal.ofReal (-(g x).im))) = _
  rw [integral_add_measure hr2.1 hL, hr1.2, hr2.2, hi1.2, hi2.2, hLint]
  have hre_split := integral_max_sub_max hre hfm hire
  have him_split := integral_max_sub_max him hfm hiim
  have hgsplit : (∫ x, g x * φ x) = (∫ x, ((g x).re : ℂ) * φ x) + I * ∫ x, ((g x).im : ℂ) * φ x := by
    rw [← integral_const_mul, ← integral_add hire (hiim.const_mul I)]
    congr 1
    funext x
    conv_lhs => rw [← Complex.re_add_im (g x)]
    ring
  rw [hgsplit, ← hre_split, ← him_split]
  ring

/-- (CP1.7) divided by b_ρ: at an actual zero the normalized measure is
b_ρ⁻¹ (V_(ρ-1/2) - c_ρ(δ₀ + dx) - b_ρ D_0) on every Schwartz test. -/
theorem zeroMeasure_eq_construction {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) (φ : 𝓢(ℝ, ℂ)) :
    (zeroMeasure ρ).integral φ =
      (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
        normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  have hbeq := coPoissonOriginNormalizer_eq_brho hρ0 hρ1
  have hS : Integrable (fun x => finiteSumSrho ρ |x| * φ x) := by
    refine (φ.integrable.norm.const_mul (finiteSumSrhoBound ρ)).mono'
      ((measurable_finiteSumSrho_abs ρ).aestronglyMeasurable.mul
        φ.continuous.aestronglyMeasurable) (Eventually.of_forall (fun x => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (finiteSumSrho_norm_le_bound h0 h1 _) (norm_nonneg _)
  have hV := coPoissonFamily_eq_limit h0 h1 φ
  have hR : (∫ x, coPoissonLimitDensity ρ x * φ x) =
      (∫ x, finiteSumSrho ρ |x| * φ x) + 1 / (1 - ρ) * ∫ x, φ x := by
    rw [← integral_const_mul, ← integral_add hS (φ.integrable.const_mul _)]
    congr 1
    funext x
    unfold coPoissonLimitDensity
    rw [hz]
    ring
  have hg : (∫ x, coPoissonComplexDensity ρ x * φ x) =
      (∫ x, finiteSumSrho ρ |x| * φ x) / normalizationBrho ρ := by
    rw [← integral_div]
    congr 1
    funext x
    unfold coPoissonComplexDensity
    rw [hbeq]
    ring
  obtain ⟨-, hLint⟩ := integral_puncturedLattice φ
  have hD : dilatedCombDistribution 0 φ = φ 0 + ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n := by
    have hA := coPoissonA_apply 0 φ
    rw [coPoissonA, sub_apply, smul_apply, TemperedDistribution.delta_apply] at hA
    simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_smul, one_mul] at hA
    rw [← hA]; ring
  have hb' : normalizationBrho ρ = 1 / ρ - 1 / (1 - ρ) := by rw [← hbeq]; rfl
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  rw [zeroMeasure_integral h0 h1, hV, hR, hg, hD]
  rw [eq_div_iff hb]
  have key : (∫ x, finiteSumSrho ρ |x| * φ x) / normalizationBrho ρ * normalizationBrho ρ =
      ∫ x, finiteSumSrho ρ |x| * φ x := div_mul_cancel₀ _ hb
  linear_combination key + φ 0 * hb'

/-! ### Fourier self-duality of the zero measure and of its real part -/

lemma complexSchwartzConj_apply (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    complexSchwartzConj φ x = starRingEnd ℂ (φ x) := rfl

/-- conj(𝓕φ) = 𝓕(conj φ ∘ (-·)). -/
lemma complexSchwartzConj_fourier (φ : 𝓢(ℝ, ℂ)) :
    complexSchwartzConj (𝓕 φ) = 𝓕 (schwartzReflect (complexSchwartzConj φ)) := by
  ext ξ
  rw [complexSchwartzConj_apply, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  rw [← integral_neg_eq_self (fun v : ℝ => cexp (((-2 * Real.pi * v * ξ : ℝ)) * I) •
    (schwartzReflect (complexSchwartzConj φ)) v)]
  congr 1
  funext v
  rw [schwartzReflect_apply, complexSchwartzConj_apply, neg_neg, smul_eq_mul, smul_eq_mul,
    map_mul, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- A complex measure that is Fourier self-dual and even on Schwartz tests has a Fourier
self-dual real part (conjugation commutes with 𝓕 on even distributions). -/
theorem rePart_fourierSelfdual_of_complex (μ : LocallyFiniteComplexMeasure) (h : μ.HasLinearGrowth)
    (hself : ∀ φ : 𝓢(ℝ, ℂ), μ.integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = μ.integral φ)
    (heven : ∀ φ : 𝓢(ℝ, ℂ), μ.integral (schwartzReflect φ) = μ.integral φ) :
    𝓕 (μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h)) =
      μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h) := by
  set η := μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h) with hηdef
  set ξ := μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h) with hξdef
  have hsplit (ψ : 𝓢(ℝ, ℂ)) : μ.integral ψ = η ψ + I * ξ ψ := rfl
  have hreal (ψ : 𝓢(ℝ, ℂ)) :
      η ψ = (μ.integral ψ + starRingEnd ℂ (μ.integral (complexSchwartzConj ψ))) / 2 := by
    rw [hsplit, hsplit, hηdef, hξdef, realJordan_distribution_conj, realJordan_distribution_conj]
    simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_I]
    ring
  ext φ
  change η (𝓕 φ) = η φ
  rw [hreal, hreal, hself, complexSchwartzConj_fourier, hself, heven]

lemma dilatedCombDistribution_zero_fourier (φ : 𝓢(ℝ, ℂ)) :
    dilatedCombDistribution 0 (𝓕 φ) = dilatedCombDistribution 0 φ := by
  change (𝓕 (dilatedCombDistribution 0)) φ = _
  rw [(dilated_comb_fourier 0).2.2, neg_zero]

lemma schwartz_integral_fourier (φ : 𝓢(ℝ, ℂ)) : ∫ x, (𝓕 φ) x = φ 0 := by
  rw [← fourier_delta_zero_apply]
  change (𝓕 (𝓕 φ)) 0 = _
  rw [schwartz_fourier_fourier_apply, neg_zero]

lemma schwartz_fourier_zero (φ : 𝓢(ℝ, ℂ)) : (𝓕 φ) 0 = ∫ x, φ x := by
  rw [← fourier_delta_zero_apply]; rfl

theorem zeroMeasure_integral_fourier {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) (φ : 𝓢(ℝ, ℂ)) :
    (zeroMeasure ρ).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = (zeroMeasure ρ).integral φ := by
  rw [zeroMeasure_eq_construction hz h0 h1 hh, zeroMeasure_eq_construction hz h0 h1 hh,
    dilatedCombDistribution_zero_fourier, schwartz_integral_fourier, schwartz_fourier_zero]
  have hV : coPoissonFamily (ρ - 1 / 2) (𝓕 φ) = coPoissonFamily (ρ - 1 / 2) φ :=
    congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) (coPoissonFamily_fourier (ρ - 1 / 2))
  rw [hV]
  ring

theorem zeroMeasure_integral_reflect {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    (zeroMeasure ρ).integral (schwartzReflect φ) = (zeroMeasure ρ).integral φ := by
  rw [zeroMeasure_integral h0 h1, zeroMeasure_integral h0 h1]
  congr 1
  · rw [← integral_neg_eq_self (fun x => coPoissonComplexDensity ρ x * φ x)]
    congr 1
    funext x
    rw [schwartzReflect_apply, coPoissonComplexDensity_neg]
  · rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => if n = 0 then (0 : ℂ) else φ n)]
    refine tsum_congr (fun n => ?_)
    simp only [Equiv.neg_apply, neg_eq_zero, schwartzReflect_apply, Int.cast_neg]

/-- Fourier self-duality of the normalized zero measure as a tempered distribution. -/
theorem zeroMeasure_fourierSelfdual {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    𝓕 ((zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) =
      (zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1) := by
  ext φ
  exact zeroMeasure_integral_fourier hz h0 h1 hh φ

theorem zeroMeasure_rePart_fourierSelfdual {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    𝓕 ((zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1))) =
      (zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) :=
  rePart_fourierSelfdual_of_complex (zeroMeasure ρ) (zeroMeasure_hasLinearGrowth h0 h1)
    (zeroMeasure_integral_fourier hz h0 h1 hh)
    (zeroMeasure_integral_reflect h0 h1)

/-- R1-CP1 zero-measure properties. For an actual nontrivial zero ρ ≠ 1/2 of ζ in the open strip,
the normalized complex measure (CP1.7)/b_ρ = (S_ρ(|x|)/b_ρ) dx - Σ_(n≠0) δ_n has linear
variation growth, canonical Fourier self-duality, even Jordan parts, the exact open unit gap,
zero origin atom and atom -1 at 1; its real part η_ρ = f_ρ dx - Σ_(n≠0) δ_n has the
corresponding real properties. -/
theorem zero_measure_exact_properties (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    normalizationBrho ρ = (1 - 2 * ρ) / coPoissonKappa ρ ∧
    normalizationBrho ρ = 1 / ρ - 1 / (1 - ρ) ∧ normalizationBrho ρ ≠ 0 ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
        normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (∫ x, coPoissonComplexDensity ρ x * φ x) - ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n) ∧
    (zeroMeasure ρ).HasLinearGrowth ∧
    𝓕 ((zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) =
      (zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1) ∧
    (Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.positive = (zeroMeasure ρ).rePart.positive ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.negative = (zeroMeasure ρ).rePart.negative ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.positive = (zeroMeasure ρ).imPart.positive ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.negative =
        (zeroMeasure ρ).imPart.negative) ∧
    (zeroMeasure ρ).variationControl (Ioo (-1) 1) = 0 ∧
    (zeroMeasure ρ).variationControl {0} = 0 ∧
    ((zeroMeasure ρ).rePart.positive {1} = 0 ∧ (zeroMeasure ρ).rePart.negative {1} = 1 ∧
      (zeroMeasure ρ).imPart.positive {1} = 0 ∧ (zeroMeasure ρ).imPart.negative {1} = 0) ∧
    ((zeroMeasure ρ).rePart.positive =
        volume.withDensity (fun x => ENNReal.ofReal (coPoissonRealDensity ρ x)) ∧
      (zeroMeasure ρ).rePart.negative =
        volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) + puncturedLattice) ∧
    (zeroMeasure ρ).rePart.HasLinearGrowth ∧
    𝓕 ((zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1))) =
      (zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) ∧
    ((zeroMeasure ρ).rePart.positive (Ioo (-1) 1) = 0 ∧
      (zeroMeasure ρ).rePart.negative (Ioo (-1) 1) = 0) ∧
    ((zeroMeasure ρ).rePart.positive {0} = 0 ∧ (zeroMeasure ρ).rePart.negative {0} = 0) ∧
    ((zeroMeasure ρ).rePart.positive.real {1} = 0 ∧ (zeroMeasure ρ).rePart.negative.real {1} = 1) ∧
    (zeroMeasure ρ).rePart.negative ≠ 0 := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hgap := zeroMeasure_gap ρ
  have horigin := zeroMeasure_origin ρ
  change ((zeroMeasure ρ).rePart.positive + (zeroMeasure ρ).rePart.negative +
    ((zeroMeasure ρ).imPart.positive + (zeroMeasure ρ).imPart.negative)) _ = 0 at hgap horigin
  simp only [Measure.add_apply, add_eq_zero] at hgap horigin
  obtain ⟨ha1, ha2, ha3, ha4⟩ := zeroMeasure_atom_one ρ
  refine ⟨rfl, (coPoissonOriginNormalizer_eq_brho hρ0 hρ1).symm,
    normalizationBrho_ne_zero hρ0 hρ1 hh, zeroMeasure_eq_construction hz h0 h1 hh,
    zeroMeasure_integral h0 h1, zeroMeasure_hasLinearGrowth h0 h1,
    zeroMeasure_fourierSelfdual hz h0 h1 hh, zeroMeasure_even ρ, zeroMeasure_gap ρ,
    zeroMeasure_origin ρ, ⟨ha1, ha2, ha3, ha4⟩, ⟨rfl, rfl⟩,
    (zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1),
    zeroMeasure_rePart_fourierSelfdual hz h0 h1 hh, ⟨hgap.1.1, hgap.1.2⟩,
    ⟨horigin.1.1, horigin.1.2⟩, ⟨by rw [measureReal_def, ha1]; rfl,
      by rw [measureReal_def, ha2]; rfl⟩, fun h => ?_⟩
  rw [h] at ha2
  simp at ha2

end ZeroMeasure

end Zeta23.OPICAFollowup

#print axioms Zeta23.OPICAFollowup.zero_measure_first_cell_sign
#print axioms Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family
#print axioms Zeta23.OPICAFollowup.renormalized_copoisson_order_zero
#print axioms Zeta23.OPICAFollowup.zero_measure_exact_properties
