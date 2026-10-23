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
The distributional construction is the renormalized tempered family below. The
local-total-variation identification and the complete zero-measure property roots
remain OPEN and are separate obligations.
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

end Zeta23.OPICAFollowup

#print axioms Zeta23.OPICAFollowup.zero_measure_first_cell_sign
#print axioms Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family
