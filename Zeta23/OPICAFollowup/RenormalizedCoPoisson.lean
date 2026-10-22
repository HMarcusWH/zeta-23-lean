import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Zeta23.ExceptionalZero.ZetaRealStripNonvanishing
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
UNCHECKED continuation at 9b6a9a3.  The density below is the literal finite
power-sum density of the frozen co-Poisson construction.  The first-cell sign
root is attempted without assuming positivity, a synthetic zero, or existence
of a measure with desired Fourier properties.  The distributional construction,
local-total-variation identification and complete zero-measure property roots
remain OPEN; this file does not hide them inside a structure field.
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
  have hfloor : Nat.floor x=1 := Nat.floor_eq_iff (by linarith : 0≤x) |>.2
    ⟨hx.1.le,hx.2⟩
  simp [coPoissonPowerSums,hfloor]

lemma coPoisson_normalizer (rho : ℂ) (h0 : rho≠0) (h1 : rho≠1) :
    coPoissonOriginNormalizer rho=(1-2*rho)/(rho*(1-rho)) := by
  unfold coPoissonOriginNormalizer
  field_simp [h0,sub_ne_zero.mpr (Ne.symm h1)]
  ring

lemma coPoissonRho_ne_real_special (delta gamma : ℝ) (hg : gamma≠0) :
    coPoissonRho delta gamma≠0 ∧ coPoissonRho delta gamma≠1 ∧
      coPoissonRho delta gamma≠1/2 ∧ (delta:ℂ)+(gamma:ℂ)*I≠0 := by
  have hi : (coPoissonRho delta gamma).im=gamma := by simp [coPoissonRho]
  refine ⟨?_,?_,?_,?_⟩ <;> intro h <;>
    have hh := congrArg Complex.im h <;> simp_all [coPoissonRho]

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
  have hsplit₋ : Complex.exp ((u:ℂ)*(-rho))=
      ((Real.exp (-u/2):ℝ):ℂ)*Complex.exp (-(lam*(u:ℂ))) := by
    rw [←Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    dsimp [rho,coPoissonRho,lam]
    push_cast
    ring
  have hsplit₊ : Complex.exp ((u:ℂ)*(rho-1))=
      ((Real.exp (-u/2):ℝ):ℂ)*Complex.exp (lam*(u:ℂ)) := by
    rw [←Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    dsimp [rho,coPoissonRho,lam]
    push_cast
    ring
  unfold coPoissonComplexDensity
  rw [abs_of_pos (Real.exp_pos u),coPoisson_first_cell_sum rho hx,hpow,hpow,
    hsplit₋,hsplit₊,hb,hk,hnum,Complex.sinh_eq]
  field_simp [hL]
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
    ring
  rw [hsplit]
  constructor <;> simp only [Complex.sub_re,Complex.sub_im,Complex.div_re,Complex.div_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_apply] <;>
    norm_num <;> field_simp [hs] <;> ring

lemma coPoisson_first_cell_real (delta gamma u : ℝ) (hg : gamma≠0)
    (hu : 0<u) (hu1 : u<Real.log 2) :
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u) =
      Real.exp (-u/2)*
       (delta*(1/(4*(delta^2+gamma^2))-1)*Real.sinh (delta*u)*Real.cos (gamma*u)+
        gamma*(1+1/(4*(delta^2+gamma^2)))*Real.cosh (delta*u)*Real.sin (gamma*u)) := by
  unfold coPoissonRealDensity
  rw [coPoisson_first_cell_exp delta gamma u hg hu hu1]
  obtain ⟨hre,him⟩ := coPoisson_quotient_re_im delta gamma hg
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.sinh_re,Complex.sinh_im,Complex.add_re,Complex.add_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add]
  rw [hre,him]
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
    (hgamma : 3*Real.pi/(2*Real.log 2)<|gamma|) :
    let u := 3*Real.pi/(2*|gamma|)
    0<u ∧ u<Real.log 2 ∧
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)=
      -|gamma|*(1+1/(4*(delta^2+gamma^2)))*
        Real.exp (-u/2)*Real.cosh (delta*u) ∧
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)<0 := by
  have hg : 0<|gamma| := lt_trans (by positivity) hgamma
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
  have hang : |gamma|*(3*Real.pi/(2*|gamma|))=Real.pi+Real.pi/2 := by
    field_simp [hg.ne']; ring
  rw [hang,Real.cos_add_pi,Real.sin_add_pi,Real.cos_pi_div_two,Real.sin_pi_div_two] at he
  have hid : coPoissonRealDensity (coPoissonRho delta gamma)
      (Real.exp (3*Real.pi/(2*|gamma|))) =
      -|gamma|*(1+1/(4*(delta^2+gamma^2)))*
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
  rw [show z*((Real.exp (-u/2):ℝ):ℂ)*
    ((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I))*
      Complex.sinh (((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ)) =
    ((Real.exp (-u/2):ℝ):ℂ)*(z*((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/
      ((delta:ℂ)+(gamma:ℂ)*I))*Complex.sinh (((delta:ℂ)+(gamma:ℂ)*I)*(u:ℂ)) by ring]
  simp [Complex.mul_re,Complex.sinh_re,Complex.sinh_im]

/-- Finite phase tuning cannot repair the sign of an off-line first-cell
profile. The four test points lie in (0,log 2) before their signs are used. -/
lemma coPoisson_phase_both_signs (delta gamma : ℝ) (hdelta : delta≠0)
    (hheight : 2*Real.pi/Real.log 2<|gamma|) (z : ℂ) (hz : z≠0) :
    ∃ x y ∈ Ioo (1:ℝ) 2,
      0<(z*coPoissonComplexDensity (coPoissonRho delta gamma) x).re ∧
      (z*coPoissonComplexDensity (coPoissonRho delta gamma) y).re<0 := by
  have hg : 0<|gamma| := lt_trans (by positivity) hheight
  have hgne : gamma≠0 := abs_pos.mp hg
  let A := z*((1/4-((delta:ℂ)+(gamma:ℂ)*I)^2)/((delta:ℂ)+(gamma:ℂ)*I))
  have hA : A≠0 := by
    apply mul_ne_zero hz
    apply div_ne_zero _ (coPoissonRho_ne_real_special delta gamma hgne).2.2.2
    intro h
    have hfac : (((delta:ℂ)+(gamma:ℂ)*I)-1/2)*
        (((delta:ℂ)+(gamma:ℂ)*I)+1/2)=0 := by linear_combination -h
    rcases mul_eq_zero.mp hfac with hm | hp
    · have := congrArg Complex.im hm; simp_all
    · have := congrArg Complex.im hp; simp_all
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
      rw [abs_of_neg hn]; field_simp; ring
  have hsinh (a : ℝ) (ha : 0<a) :
      Real.sinh (delta*(a/|gamma|))≠0 ∧
      (0<Real.sinh (delta*(a/|gamma|)) ↔ 0<delta) := by
    have hpos := div_pos ha hg
    constructor
    · rw [Real.sinh_eq_zero]; exact mul_ne_zero hdelta hpos.ne'
    · rw [Real.sinh_pos_iff]; exact mul_pos_iff_of_pos_right hpos
  by_cases hAre : A.re=0
  · have hAi : A.im≠0 := by
      intro h
      apply hA
      exact Complex.ext hAre h
    obtain ⟨hu₀,hu₁,hx⟩ := hpoint (Real.pi/2) (by positivity) (by linarith [Real.pi_pos])
    obtain ⟨hv₀,hv₁,hy⟩ := hpoint (3*Real.pi/2) (by positivity) (by linarith [Real.pi_pos])
    have hxf := coPoisson_phase_formula delta gamma (Real.pi/(2*|gamma|)) z hgne
      (by convert hu₀ using 1 <;> ring) (by convert hu₁ using 1 <;> ring)
    have hyf := coPoisson_phase_formula delta gamma (3*Real.pi/(2*|gamma|)) z hgne
      (by convert hv₀ using 1 <;> ring) (by convert hv₁ using 1 <;> ring)
    have hxy : (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (Real.pi/(2*|gamma|)))).re *
      (z*coPoissonComplexDensity (coPoissonRho delta gamma)
        (Real.exp (3*Real.pi/(2*|gamma|)))).re < 0 := by
      rw [hxf,hyf]
      change (Real.exp _*(A.re*Real.sinh _*Real.cos _ -
        A.im*Real.cosh _*Real.sin _)) * (Real.exp _*(A.re*Real.sinh _*Real.cos _ -
        A.im*Real.cosh _*Real.sin _)) < 0
      rw [hAre]
      have hhalf : gamma*(Real.pi/(2*|gamma|))=if 0<gamma then Real.pi/2 else -Real.pi/2 := by
        convert htrig (Real.pi/2) using 1 <;> ring
      have hthree : gamma*(3*Real.pi/(2*|gamma|))=if 0<gamma then Real.pi+Real.pi/2 else -(Real.pi+Real.pi/2) := by
        convert htrig (3*Real.pi/2) using 1 <;> ring
      rw [hhalf,hthree]
      split_ifs <;> simp only [Real.sin_pi_div_two,Real.sin_add_pi,Real.sin_neg,
        zero_mul,zero_sub,neg_neg,mul_neg_one,mul_one] <;>
        nlinarith [Real.exp_pos (-(Real.pi/(2*|gamma|))/2),
          Real.exp_pos (-(3*Real.pi/(2*|gamma|))/2),
          Real.cosh_pos (delta*(Real.pi/(2*|gamma|))),
          Real.cosh_pos (delta*(3*Real.pi/(2*|gamma|))),sq_pos_of_ne_zero hAi]
    have hx' : Real.exp (Real.pi/(2*|gamma|)) ∈ Ioo (1:ℝ) 2 := by
      convert hx using 1 <;> congr 1 <;> ring
    have hy' : Real.exp (3*Real.pi/(2*|gamma|)) ∈ Ioo (1:ℝ) 2 := by
      convert hy using 1 <;> congr 1 <;> ring
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
        Real.cos_neg,Real.sin_neg,neg_zero,mul_zero,sub_zero,mul_one,mul_neg_one] <;>
        nlinarith [mul_pos (Real.exp_pos (-(Real.pi/|gamma|)/2))
          (Real.exp_pos (-(2*Real.pi/|gamma|)/2)),sq_pos_of_ne_zero hAre]
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
    (hheight : 3*Real.pi/(2*Real.log 2)<|gamma|) :
    (let u := 3*Real.pi/(2*|gamma|)
     0<u ∧ u<Real.log 2 ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)=
       -|gamma|*(1+1/(4*(delta^2+gamma^2)))*Real.exp (-u/2)*Real.cosh (delta*u) ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)<0) ∧
    (delta≠0 → 2*Real.pi/Real.log 2<|gamma| → ∀ z : ℂ, z≠0 →
      ∃ x y ∈ Ioo (1:ℝ) 2,
        0<(z*coPoissonComplexDensity (coPoissonRho delta gamma) x).re ∧
        (z*coPoissonComplexDensity (coPoissonRho delta gamma) y).re<0) := by
  exact ⟨coPoisson_first_cell_negative_value delta gamma hheight,
    fun hd hh z hz => coPoisson_phase_both_signs delta gamma hd hh z hz⟩

end Zeta23.OPICAFollowup
