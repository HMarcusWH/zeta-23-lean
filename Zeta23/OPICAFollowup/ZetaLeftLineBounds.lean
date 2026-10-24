import Zeta23.RvM.ZetaGrowth
import Mathlib.Analysis.Complex.Liouville
import Zeta23.GammaFacts.Complete
import Zeta23.Analytic.Stirling
import Zeta23.WeilEF.VerticalLine
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! Uniform moving-left-line estimates for zeta and its derivative. The proof
uses exact gamma reflection on real part one, integer recurrences and direct
differentiation of the functional equation on its genuine open domain. -/

noncomputable section
namespace Zeta23.OPICAFollowup
open Complex
open scoped ComplexConjugate Topology

/-- Exact gamma modulus on the line of real part one, obtained from Euler's
reflection identity. The removable value at zero is handled separately below. -/
theorem gamma_one_vertical_norm_sq {τ : ℝ} (hτ : τ ≠ 0) :
    ‖Complex.Gamma (1+Complex.I*(τ:ℂ))‖^2 =
      Real.pi*τ/Real.sinh (Real.pi*τ) := by
  have ht : Complex.I*(τ:ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hτ)
  have hrec : Complex.Gamma (1+Complex.I*(τ:ℂ)) =
      (Complex.I*(τ:ℂ))*Complex.Gamma (Complex.I*(τ:ℂ)) := by
    simpa only [add_comm] using Complex.Gamma_add_one (Complex.I*(τ:ℂ)) ht
  have hconj : conj (Complex.Gamma (1+Complex.I*(τ:ℂ))) =
      Complex.Gamma (1-Complex.I*(τ:ℂ)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp [sub_eq_add_neg]
  have hsine : Complex.sin ((Real.pi:ℂ)*(Complex.I*(τ:ℂ))) =
      (Real.sinh (Real.pi*τ):ℂ)*Complex.I := by
    rw [show (Real.pi:ℂ)*(Complex.I*(τ:ℂ)) = ((Real.pi*τ:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hc : (‖Complex.Gamma (1+Complex.I*(τ:ℂ))‖^2:ℂ) =
      ((Real.pi*τ/Real.sinh (Real.pi*τ):ℝ):ℂ) := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self, hconj, hrec]
    calc
      _ = (Complex.I*(τ:ℂ))*(Complex.Gamma (Complex.I*(τ:ℂ))*
          Complex.Gamma (1-Complex.I*(τ:ℂ))) := by ring
      _ = (Complex.I*(τ:ℂ))*((Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*(Complex.I*(τ:ℂ)))) := by
        rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = _ := by rw [hsine]; push_cast; field_simp
  exact_mod_cast hc

theorem gamma_one_vertical_norm_even (τ : ℝ) :
    ‖Complex.Gamma (1+Complex.I*(τ:ℂ))‖ =
      ‖Complex.Gamma (1+Complex.I*((|τ|:ℝ):ℂ))‖ := by
  by_cases ht : 0 ≤ τ
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    have hc : 1+Complex.I*((-τ:ℝ):ℂ) = conj (1+Complex.I*(τ:ℂ)) := by
      simp
    rw [hc, Complex.Gamma_conj, norm_conj]

/-- A coarse exponential reflection bound; it is uniform down to the removable
origin and therefore usable before the integer gamma recurrence. -/
theorem gamma_reflection_ratio_bound {x : ℝ} (hx : 0 < x) :
    x / Real.sinh x ≤ (1+2*x)*Real.exp (-x) := by
  have hsh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have he : (1+2*x)*Real.exp (-2*x) ≤ 1 := by
    have hlin := Real.add_one_le_exp (2*x)
    have hh := mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg (-2*x))
    have heq : Real.exp (2*x)*Real.exp (-2*x) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    nlinarith
  have heq : Real.exp (-x)*Real.sinh x = (1-Real.exp (-2*x))/2 := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-x)*Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-x)*Real.exp (-x) = Real.exp (-2*x) := by rw [← Real.exp_add]; ring_nf
    nlinarith
  apply (div_le_iff₀ hsh).mpr
  nlinarith

theorem gamma_one_vertical_exp_bound (τ : ℝ) :
    ‖Complex.Gamma (1+Complex.I*(τ:ℂ))‖ ≤
      2*(1+Real.pi*|τ|)*Real.exp (-(Real.pi*|τ|)/2) := by
  rw [gamma_one_vertical_norm_even]
  by_cases ht : τ = 0
  · subst τ
    norm_num [Complex.Gamma_one]
  · have habs : 0 < |τ| := abs_pos.mpr ht
    have hx : 0 < Real.pi*|τ| := mul_pos Real.pi_pos habs
    have hs := gamma_one_vertical_norm_sq (ne_of_gt habs)
    have hb := gamma_reflection_ratio_bound hx
    have he : 0 < Real.exp (-(Real.pi*|τ|)/2) := Real.exp_pos _
    have heq : Real.exp (-(Real.pi*|τ|)/2)^2 = Real.exp (-(Real.pi*|τ|)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hx0 : 0 ≤ Real.pi*|τ| := hx.le
    have hpoly : 1+2*(Real.pi*|τ|) ≤ 4*(1+Real.pi*|τ|)^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (-(Real.pi*|τ|)))
    have hsq : ‖Complex.Gamma (1+Complex.I*((|τ|:ℝ):ℂ))‖^2 ≤
        (2*(1+Real.pi*|τ|)*Real.exp (-(Real.pi*|τ|)/2))^2 := by
      rw [hs]
      calc
        _ ≤ (1+2*(Real.pi*|τ|))*Real.exp (-(Real.pi*|τ|)) := hb
        _ ≤ 4*(1+Real.pi*|τ|)^2*Real.exp (-(Real.pi*|τ|)) := hmul
        _ = _ := by rw [mul_pow, mul_pow, heq]; ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- The integer recurrence retains a single exponential decay constant and
prices every moving real-part factor explicitly. -/
theorem gamma_integer_vertical_exp_bound (n : ℕ) (τ : ℝ) :
    ‖Complex.Gamma ((n:ℂ)+1+Complex.I*(τ:ℂ))‖ ≤
      2*(1+Real.pi*|τ|)*((n:ℝ)+1+|τ|)^n*
        Real.exp (-(Real.pi*|τ|)/2) := by
  induction n with
  | zero => simpa using gamma_one_vertical_exp_bound τ
  | succ n ih =>
    let z : ℂ := (n:ℂ)+1+Complex.I*(τ:ℂ)
    let B : ℝ := (n:ℝ)+2+|τ|
    have hz : z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp [z] at hh
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hrec : Complex.Gamma (((n+1:ℕ):ℂ)+1+Complex.I*(τ:ℂ)) = z*Complex.Gamma z := by
      rw [show (((n+1:ℕ):ℂ)+1+Complex.I*(τ:ℂ)) = z+1 by dsimp [z]; push_cast; ring]
      exact Complex.Gamma_add_one z hz
    have hn : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
    have hznorm : ‖z‖ ≤ B := by
      have hb := Complex.norm_le_abs_re_add_abs_im z
      have hre : z.re = (n:ℝ)+1 := by simp [z]
      have him : z.im = τ := by simp [z]
      rw [hre,him,abs_of_nonneg hn] at hb
      dsimp [B]
      linarith
    have hpow : ((n:ℝ)+1+|τ|)^n ≤ B^n := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [B]
      linarith
    rw [hrec,norm_mul]
    calc
      _ ≤ B*(2*(1+Real.pi*|τ|)*((n:ℝ)+1+|τ|)^n*
          Real.exp (-(Real.pi*|τ|)/2)) :=
        mul_le_mul hznorm ih (norm_nonneg _) (by dsimp [B]; positivity)
      _ ≤ B*(2*(1+Real.pi*|τ|)*B^n*Real.exp (-(Real.pi*|τ|)/2)) := by
        gcongr
      _ = _ := by simp only [Nat.cast_add,Nat.cast_one,pow_succ]; dsimp [B]; ring

/-- A single constant controls both zeta and its derivative on the entire
closed right half-plane used by the reflected moving integer lines. -/
theorem zeta_right_halfplane_value_derivative_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖riemannZeta s‖+‖deriv riemannZeta s‖ ≤ C := by
  have h0 : LSeriesSummable (1 : ℕ → ℂ) 2 :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  have h1 : LSeriesSummable (LSeries.logMul (1 : ℕ → ℂ)) 2 :=
    LSeriesSummable_logMul_of_lt_re (by
      rw [LSeries.abscissaOfAbsConv_one]
      exact_mod_cast (show (1:ℝ) < (2:ℂ).re by norm_num))
  let A := ∑' n, ‖LSeries.term (1 : ℕ → ℂ) 2 n‖
  let B := ∑' n, ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) 2 n‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  have hbound (f : ℕ → ℂ) (hf : LSeriesSummable f 2) (s : ℂ) (hs : 2 ≤ s.re) :
      ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f 2 n‖ := by
    have hre : (2:ℂ).re ≤ s.re := by simpa using hs
    have hfs := LSeriesSummable.of_re_le_re hre hf
    calc
      _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hfs.norm
      _ ≤ _ := hfs.norm.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re f hre) hf.norm
  refine ⟨1+A+B, by linarith, ?_⟩
  intro s hs
  have hζ : ‖riemannZeta s‖ ≤ A := by
    rw [← LSeries_one_eq_riemannZeta (by linarith : 1 < s.re)]
    exact hbound _ h0 s hs
  have heq : deriv (LSeries (1 : ℕ → ℂ)) s = deriv riemannZeta s := by
    apply Filter.EventuallyEq.deriv_eq
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re},
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by change 1 < s.re; linarith),
        fun _ => LSeries_one_eq_riemannZeta⟩
  have hab : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast (show (1:ℝ) < s.re by linarith)
  have hdζ : ‖deriv riemannZeta s‖ ≤ B := by
    rw [← heq,LSeries_deriv hab,norm_neg]
    exact hbound _ h1 s hs
  linarith

/-- Coarse digamma control with a constant independent of the moving integer
line. The fixed-strip estimate is used only at real part one, then recurred. -/
theorem digamma_integer_vertical_bound : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (τ : ℝ), ‖Complex.digamma ((n:ℂ)+1+Complex.I*(τ:ℂ))‖ ≤
      C*((n:ℝ)+2+|τ|) := by
  obtain ⟨C0,hC0,hstrip⟩ := Zeta23.WeilEF.digamma_growth_strip
  let C := max 1 C0
  have hC : 1 ≤ C := le_max_left _ _
  have hCC : C0 ≤ C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro n
  induction n with
  | zero =>
    intro τ
    have hb := hstrip (1+Complex.I*(τ:ℂ)) (by norm_num) (by norm_num)
    have hlog : Real.log (2+|τ|) ≤ 2+|τ| := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < 2+|τ| by positivity)
      linarith
    simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add] at hb
    simp only [Nat.cast_zero,zero_add]
    calc
      _ ≤ C0*Real.log (2+|τ|) := hb
      _ ≤ C0*(2+|τ|) := mul_le_mul_of_nonneg_left hlog hC0.le
      _ ≤ C*(2+|τ|) := mul_le_mul_of_nonneg_right hCC (by positivity)
  | succ n ih =>
    intro τ
    let z : ℂ := (n:ℂ)+1+Complex.I*(τ:ℂ)
    have hz (m : ℕ) : z ≠ -(m:ℂ) := by
      intro h
      have hh := congrArg Complex.re h
      simp [z] at hh
      nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) m]
    have hznorm : 1 ≤ ‖z‖ := by
      have hh := Complex.re_le_norm z
      simp [z] at hh
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hinv : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (by linarith : 0 < ‖z‖)).mpr hznorm
    rw [show (((n+1:ℕ):ℂ)+1+Complex.I*(τ:ℂ)) = z+1 by dsimp [z]; push_cast; ring,
      Complex.digamma_apply_add_one z hz]
    have hb := (norm_add_le (Complex.digamma z) z⁻¹).trans (add_le_add (ih τ) hinv)
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

def zetaReflectionFactor (s : ℂ) : ℂ :=
  2*((2*Real.pi:ℝ):ℂ)^(-s)*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)

def zetaReflectionDerivative (s : ℂ) : ℂ :=
  2*((2*Real.pi:ℝ):ℂ)^(-s)*
    ((-Complex.log ((2*Real.pi:ℝ):ℂ))*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)+
      deriv Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)-
      Complex.Gamma s*Complex.sin ((Real.pi:ℂ)*s/2)*((Real.pi:ℂ)/2))

theorem zetaReflectionFactor_hasDerivAt {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt zetaReflectionFactor (zetaReflectionDerivative s) s := by
  have hnonneg (m : ℕ) : s ≠ -(m:ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hbase : ((2*Real.pi:ℝ):ℂ) ≠ 0 := by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne'
  have hp := ((hasDerivAt_id s).neg.const_cpow (c := ((2*Real.pi:ℝ):ℂ)) (Or.inl hbase)).const_mul 2
  have hg := (Complex.differentiableAt_Gamma s hnonneg).hasDerivAt
  have hc := (((hasDerivAt_id s).const_mul (Real.pi:ℂ)).div_const 2).ccos
  apply ((hp.mul hg).mul hc).congr_deriv
  dsimp [zetaReflectionDerivative]
  ring

/-- Both the functional equation and its derivative are used on a genuine
open half-plane. No reciprocal-zeta or zero-free premise enters. -/
theorem zeta_reflected_value_derivative {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (1-s) = zetaReflectionFactor s*riemannZeta s ∧
    -deriv riemannZeta (1-s) =
      zetaReflectionDerivative s*riemannZeta s+zetaReflectionFactor s*deriv riemannZeta s := by
  have hn (w : ℂ) (hw : 1 < w.re) (m : ℕ) : w ≠ -(m:ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hv (w : ℂ) (hw : 1 < w.re) :
      riemannZeta (1-w) = zetaReflectionFactor w*riemannZeta w := by
    have hw1 : w ≠ 1 := by intro h; simp [h] at hw
    simpa [zetaReflectionFactor,Complex.ofReal_mul] using riemannZeta_one_sub (hn w hw) hw1
  refine ⟨hv s hs,?_⟩
  have heq : (fun w : ℂ => riemannZeta (1-w)) =ᶠ[𝓝 s]
      (fun w => zetaReflectionFactor w*riemannZeta w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact hv w hw
  have hleft : HasDerivAt (fun w : ℂ => riemannZeta (1-w)) (-deriv riemannZeta (1-s)) s := by
    have hne : 1-s ≠ 1 := by
      intro h
      have hh := congrArg Complex.re h
      simp at hh
      linarith
    simpa only [Function.comp_def,id_eq,mul_neg,mul_one] using
      (differentiableAt_riemannZeta hne).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
  have hsne : s ≠ 1 := by intro h; simp [h] at hs
  have hright := (zetaReflectionFactor_hasDerivAt (by linarith : 0 < s.re)).mul
    (differentiableAt_riemannZeta hsne).hasDerivAt
  rw [← hleft.deriv,heq.deriv_eq]
  exact hright.deriv

def reflectionGammaTrigConstant : ℝ := 4*(1+Real.pi)

theorem gamma_integer_trig_bound (n : ℕ) (τ : ℝ) :
    let s : ℂ := (n:ℂ)+1+Complex.I*(τ:ℂ)
    ‖Complex.Gamma s‖*(‖Complex.cos ((Real.pi:ℂ)*s/2)‖+
      ‖Complex.sin ((Real.pi:ℂ)*s/2)‖) ≤
        reflectionGammaTrigConstant*((n:ℝ)+2+|τ|)^(n+1) := by
  let s : ℂ := (n:ℂ)+1+Complex.I*(τ:ℂ)
  let B : ℝ := (n:ℝ)+2+|τ|
  change ‖Complex.Gamma s‖*(‖Complex.cos ((Real.pi:ℂ)*s/2)‖+
      ‖Complex.sin ((Real.pi:ℂ)*s/2)‖) ≤ reflectionGammaTrigConstant*B^(n+1)
  have him : (((Real.pi:ℂ)*s/2).im) = Real.pi*τ/2 := by simp [s]
  have habs : |(((Real.pi:ℂ)*s/2).im)| = Real.pi*|τ|/2 := by
    rw [him,abs_div,abs_mul,abs_of_pos Real.pi_pos]
    norm_num
  have htrig : ‖Complex.cos ((Real.pi:ℂ)*s/2)‖+
      ‖Complex.sin ((Real.pi:ℂ)*s/2)‖ ≤ 2*Real.exp (Real.pi*|τ|/2) := by
    have hc := complex_cos_norm_le_exp_abs_im ((Real.pi:ℂ)*s/2)
    have hs := complex_sin_norm_le_exp_abs_im ((Real.pi:ℂ)*s/2)
    rw [habs] at hc hs
    linarith
  have hg := gamma_integer_vertical_exp_bound n τ
  have hp : ((n:ℝ)+1+|τ|)^n ≤ B^n := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [B]
    linarith
  have hlin : 1+Real.pi*|τ| ≤ (1+Real.pi)*B := by
    dsimp [B]
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Real.pi_pos,abs_nonneg τ]
  have he : Real.exp (-(Real.pi*|τ|)/2)*Real.exp (Real.pi*|τ|/2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    _ ≤ (2*(1+Real.pi*|τ|)*((n:ℝ)+1+|τ|)^n*Real.exp (-(Real.pi*|τ|)/2))*
        (2*Real.exp (Real.pi*|τ|/2)) :=
      mul_le_mul hg htrig (by positivity) (by positivity)
    _ = 4*(1+Real.pi*|τ|)*((n:ℝ)+1+|τ|)^n := by
      calc
        _ = 4*(1+Real.pi*|τ|)*((n:ℝ)+1+|τ|)^n*
            (Real.exp (-(Real.pi*|τ|)/2)*Real.exp (Real.pi*|τ|/2)) := by ring
        _ = _ := by rw [he,mul_one]
    _ ≤ 4*((1+Real.pi)*B)*B^n := by gcongr
    _ = _ := by unfold reflectionGammaTrigConstant; rw [pow_succ]; ring

theorem zeta_reflection_uniform_integer_bound : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (τ : ℝ),
      let s : ℂ := (n:ℂ)+1+Complex.I*(τ:ℂ)
      ‖zetaReflectionFactor s‖+‖zetaReflectionDerivative s‖ ≤
        C*((n:ℝ)+2+|τ|)^(n+2) := by
  obtain ⟨D,hD,hpsi⟩ := digamma_integer_vertical_bound
  let L : ℝ := ‖Complex.log ((2*Real.pi:ℝ):ℂ)‖
  let C := 2*reflectionGammaTrigConstant*(1+L+D+Real.pi/2)
  have hL : 0 ≤ L := norm_nonneg _
  have hCg : 1 ≤ reflectionGammaTrigConstant := by unfold reflectionGammaTrigConstant; nlinarith [Real.pi_pos]
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [Real.pi_pos]
  refine ⟨C,hC,?_⟩
  intro n τ
  let s : ℂ := (n:ℂ)+1+Complex.I*(τ:ℂ)
  let B : ℝ := (n:ℝ)+2+|τ|
  let G : ℝ := ‖Complex.Gamma s‖
  let c : ℝ := ‖Complex.cos ((Real.pi:ℂ)*s/2)‖
  let b : ℝ := ‖Complex.sin ((Real.pi:ℂ)*s/2)‖
  let p : ℝ := ‖Complex.digamma s‖
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α := ℝ) n,abs_nonneg τ]
  have hG : 0 ≤ G := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hp : 0 ≤ p := norm_nonneg _
  have hpbound : p ≤ D*B := hpsi n τ
  have hgtrig : G*(c+b) ≤ reflectionGammaTrigConstant*B^(n+1) := gamma_integer_trig_bound n τ
  have hn (m : ℕ) : s ≠ -(m:ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp [s] at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) m]
  have hd : deriv Complex.Gamma s = Complex.Gamma s*Complex.digamma s := by
    rw [Complex.digamma_def,logDeriv_apply]
    field_simp [Complex.Gamma_ne_zero hn]
  have hpow : ‖((2*Real.pi:ℝ):ℂ)^(-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · nlinarith [Real.pi_gt_three]
    · simp [s]
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hf : ‖zetaReflectionFactor s‖ ≤ 2*G*c := by
    unfold zetaReflectionFactor
    rw [norm_mul,norm_mul,norm_mul]
    norm_num
    calc
      _ ≤ 2*1*G*c := by
        gcongr
        simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using hpow
      _ = _ := by ring
  have hder : ‖zetaReflectionDerivative s‖ ≤ 2*(L*G*c+G*p*c+G*b*(Real.pi/2)) := by
    let A := (-Complex.log ((2*Real.pi:ℝ):ℂ))*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)
    let W := deriv Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)
    let V := Complex.Gamma s*Complex.sin ((Real.pi:ℂ)*s/2)*((Real.pi:ℂ)/2)
    have ht : ‖A+W-V‖ ≤ L*G*c+G*p*c+G*b*(Real.pi/2) := by
      have hh := (norm_sub_le (A+W) V).trans (add_le_add (norm_add_le A W) (le_refl ‖V‖))
      simpa [A,W,V,L,G,c,b,p,hd,norm_mul,norm_neg,norm_div,
        Complex.norm_real,abs_of_pos Real.pi_pos] using hh
    change ‖2*((2*Real.pi:ℝ):ℂ)^(-s)*(A+W-V)‖ ≤ _
    rw [norm_mul,norm_mul]
    norm_num
    calc
      _ ≤ (2*1)*(L*G*c+G*p*c+G*b*(Real.pi/2)) := by
        apply mul_le_mul
        · gcongr
          simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using hpow
        · exact ht
        · positivity
        · positivity
      _ = _ := by ring
  have hsum : ‖zetaReflectionFactor s‖+‖zetaReflectionDerivative s‖ ≤
      2*(G*(c+b))*(1+L+p+Real.pi/2) := by
    have h1 : 2*G*c+2*(L*G*c+G*p*c+G*b*(Real.pi/2)) ≤
        2*(G*(c+b))*(1+L+p+Real.pi/2) := by
      nlinarith [mul_nonneg hG hb, mul_nonneg (mul_nonneg hG hb) hL,
        mul_nonneg (mul_nonneg hG hb) hp,mul_nonneg (mul_nonneg hG hc) Real.pi_pos.le]
    linarith
  have hcoeff : 1+L+p+Real.pi/2 ≤ (1+L+D+Real.pi/2)*B := by
    have hbase : 0 ≤ 1+L+Real.pi/2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hB hbase
    nlinarith
  change ‖zetaReflectionFactor s‖+‖zetaReflectionDerivative s‖ ≤ C*B^(n+2)
  calc
    _ ≤ 2*(G*(c+b))*(1+L+p+Real.pi/2) := hsum
    _ ≤ 2*(reflectionGammaTrigConstant*B^(n+1))*((1+L+D+Real.pi/2)*B) := by
      gcongr
    _ = _ := by dsimp [C]; rw [show n+2=(n+1)+1 by omega,pow_succ]; ring

/-- One constant works on every moving integer left line, for both the actual
zeta function and its derivative. No simplicity or zero-free hypothesis is used. -/
theorem zeta_left_line_uniform_bound : ∃ A0 : ℝ, 1 ≤ A0 ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ τ : ℝ,
      ‖riemannZeta (-(n:ℂ)+Complex.I*(τ:ℂ))‖+
        ‖deriv riemannZeta (-(n:ℂ)+Complex.I*(τ:ℂ))‖ ≤
      A0^(n+1)*((n:ℝ)+2+|τ|)^(n+2) := by
  obtain ⟨Cz,hCz,hzeta⟩ := zeta_right_halfplane_value_derivative_bound
  obtain ⟨Cr,hCr,hreflect⟩ := zeta_reflection_uniform_integer_bound
  let A0 := max 1 (Cr*Cz)
  have hA : 1 ≤ A0 := le_max_left _ _
  have hCC : Cr*Cz ≤ A0 := le_max_right _ _
  refine ⟨A0,hA,?_⟩
  intro n hn τ
  let s : ℂ := (n:ℂ)+1+Complex.I*((-τ:ℝ):ℂ)
  let B : ℝ := (n:ℝ)+2+|τ|
  have hre : 2 ≤ s.re := by
    simp [s]
    exact_mod_cast (show 2 ≤ n+1 by omega)
  have hleft : 1-s = -(n:ℂ)+Complex.I*(τ:ℂ) := by dsimp [s]; push_cast; ring
  have hv := zeta_reflected_value_derivative (s := s) (by linarith : 1 < s.re)
  have hz := hzeta s hre
  have hr : ‖zetaReflectionFactor s‖+‖zetaReflectionDerivative s‖ ≤ Cr*B^(n+2) := by
    simpa [s,B,abs_neg] using hreflect n (-τ)
  have hval : ‖riemannZeta (1-s)‖ = ‖zetaReflectionFactor s‖*‖riemannZeta s‖ := by
    rw [hv.1,norm_mul]
  have hder : ‖deriv riemannZeta (1-s)‖ ≤
      ‖zetaReflectionDerivative s‖*‖riemannZeta s‖+
        ‖zetaReflectionFactor s‖*‖deriv riemannZeta s‖ := by
    calc
      _ = ‖-deriv riemannZeta (1-s)‖ := (norm_neg _).symm
      _ = _ := congrArg norm hv.2
      _ ≤ _ := (norm_add_le _ _).trans_eq (by rw [norm_mul,norm_mul])
  have hcombined : ‖riemannZeta (1-s)‖+‖deriv riemannZeta (1-s)‖ ≤
      (‖zetaReflectionFactor s‖+‖zetaReflectionDerivative s‖)*
        (‖riemannZeta s‖+‖deriv riemannZeta s‖) := by
    have hmiss : 0 ≤ ‖zetaReflectionDerivative s‖*‖deriv riemannZeta s‖ := by positivity
    nlinarith
  have hpower : A0 ≤ A0^(n+1) := by
    have hh : 1 ≤ A0^n := one_le_pow₀ hA
    rw [pow_succ]
    nlinarith
  rw [← hleft]
  change ‖riemannZeta (1-s)‖+‖deriv riemannZeta (1-s)‖ ≤ A0^(n+1)*B^(n+2)
  calc
    _ ≤ (‖zetaReflectionFactor s‖+‖zetaReflectionDerivative s‖)*
        (‖riemannZeta s‖+‖deriv riemannZeta s‖) := hcombined
    _ ≤ (Cr*B^(n+2))*Cz := mul_le_mul hr hz (by positivity) (by positivity)
    _ = (Cr*Cz)*B^(n+2) := by ring
    _ ≤ A0^(n+1)*B^(n+2) := mul_le_mul_of_nonneg_right (hCC.trans hpower) (by dsimp [B]; positivity)


open Set Filter MeasureTheory
open scoped Topology BigOperators

/-- Absolute values in the genuine Beta integral only discard oscillation. -/
theorem betaIntegral_norm_le_real_parts {u v : ℂ} (hu : 0<u.re) (hv : 0<v.re) :
    ‖Complex.betaIntegral u v‖ ≤ ‖Complex.betaIntegral (u.re:ℂ) (v.re:ℂ)‖ := by
  let f : ℝ → ℂ := fun x => (x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)
  let g : ℝ → ℂ := fun x => (x:ℂ)^((u.re:ℂ)-1)*(1-(x:ℂ))^((v.re:ℂ)-1)
  have hg0 := Complex.betaIntegral_convergent (u := (u.re:ℂ)) (v := (v.re:ℂ))
    (by simpa only [Complex.ofReal_re] using hu) (by simpa only [Complex.ofReal_re] using hv)
  have hg : Integrable g (volume.restrict (Ioo (0:ℝ) 1)) := hg0.1.mono_set Ioo_subset_Ioc_self
  have hpoint (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : ‖f x‖=(g x).re := by
    have hbase : (1:ℂ)-(x:ℂ)=((1-x:ℝ):ℂ) := by push_cast; rfl
    have hreal : g x=((x^(u.re-1)*(1-x)^(v.re-1):ℝ):ℂ) := by
      have huarg : (u.re:ℂ)-1=((u.re-1:ℝ):ℂ) := by push_cast; rfl
      have hvarg : (v.re:ℂ)-1=((v.re-1:ℝ):ℂ) := by push_cast; rfl
      dsimp [g]
      rw [huarg,hvarg,hbase,←Complex.ofReal_cpow hx.1.le _,
        ←Complex.ofReal_cpow (sub_pos.mpr hx.2).le _,←Complex.ofReal_mul]
    calc
      _ = x^(u.re-1)*(1-x)^(v.re-1) := by
        dsimp [f]
        rw [norm_mul,hbase,Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
          Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
        simp only [Complex.sub_re,Complex.one_re]
      _ = _ := by rw [hreal,Complex.ofReal_re]
  simp only [Complex.betaIntegral,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_Ioc_eq_integral_Ioo]
  change ‖∫ x : ℝ in Ioo 0 1, f x‖ ≤ ‖∫ x : ℝ in Ioo 0 1, g x‖
  calc
    _ ≤ ∫ x : ℝ in Ioo 0 1, ‖f x‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioo 0 1, (g x).re := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpoint x hx
    _ = (∫ x : ℝ in Ioo 0 1, g x).re := integral_re hg
    _ ≤ _ := Complex.re_le_norm _

/-- A positive fractional real part is compared to a genuinely larger integer
line by the Beta integral. No digamma or Stirling premise is required. -/
theorem gamma_vertical_compare_integer (n : ℕ) {σ : ℝ} (hσ : 0<σ)
    (hσn : σ<(n:ℝ)+1) (τ : ℝ) :
    ‖Complex.Gamma ((σ:ℂ)+I*(τ:ℂ))‖ ≤
      ‖Complex.Gamma (σ:ℂ)‖*‖Complex.Gamma ((n:ℂ)+1+I*(τ:ℂ))‖ := by
  let z : ℂ := (σ:ℂ)+I*(τ:ℂ)
  let v : ℂ := (((n:ℝ)+1-σ:ℝ):ℂ)
  have hz : 0<z.re := by simpa [z] using hσ
  have hv : 0<v.re := by change 0<(n:ℝ)+1-σ; linarith
  have hs : 0<(σ:ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  have hsum : z+v=(n:ℂ)+1+I*(τ:ℂ) := by dsimp [z,v]; push_cast; ring_nf
  have hsum0 : (σ:ℂ)+v=(n:ℂ)+1 := by dsimp [v]; push_cast; ring_nf
  have hc := congrArg norm (Complex.Gamma_mul_Gamma_eq_betaIntegral hz hv)
  have hr := congrArg norm (Complex.Gamma_mul_Gamma_eq_betaIntegral hs hv)
  simp only [norm_mul,hsum] at hc
  simp only [norm_mul,hsum0] at hr
  have hG : (1:ℝ)≤‖Complex.Gamma ((n:ℂ)+1)‖ := by
    rw [Complex.Gamma_nat_eq_factorial,Complex.norm_natCast]
    exact_mod_cast (show 1≤n.factorial from Nat.factorial_pos n)
  have hβ : ‖Complex.betaIntegral (σ:ℂ) v‖ ≤ ‖Complex.Gamma (σ:ℂ)‖*‖Complex.Gamma v‖ := by
    have h := mul_le_mul_of_nonneg_right hG (norm_nonneg (Complex.betaIntegral (σ:ℂ) v))
    nlinarith [hr]
  have hb : ‖Complex.betaIntegral z v‖ ≤ ‖Complex.betaIntegral (σ:ℂ) v‖ := by
    have h := betaIntegral_norm_le_real_parts hz hv
    simpa [z,v] using h
  have hvne : Complex.Gamma v≠0 := Complex.Gamma_ne_zero (by
    intro m hm
    have h := congrArg Complex.re hm
    simp only [Complex.neg_re,Complex.natCast_re] at h
    nlinarith [Nat.cast_nonneg (α:=ℝ) m])
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hvne)).mp
  calc
    _ = ‖Complex.Gamma ((n:ℂ)+1+I*(τ:ℂ))‖*‖Complex.betaIntegral z v‖ := hc
    _ ≤ ‖Complex.Gamma ((n:ℂ)+1+I*(τ:ℂ))‖*(‖Complex.Gamma (σ:ℂ)‖*‖Complex.Gamma v‖) :=
      mul_le_mul_of_nonneg_left (hb.trans hβ) (norm_nonneg _)
    _ = _ := by ring_nf

/-- The exact exponential Gamma decay holds uniformly over every closed
positive real strip, including all fractional real parts. -/
theorem gamma_positive_fixed_strip_exp_bound {a b : ℝ} (ha : 0<a) (_hab : a≤b) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), a≤σ → σ≤b →
      ‖Complex.Gamma ((σ:ℂ)+I*(τ:ℂ))‖ ≤
        C*(1+|τ|)^N*Real.exp (-(Real.pi*|τ|)/2) := by
  have hcont : ContinuousOn (fun x : ℝ => Complex.Gamma (x:ℂ)) (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hne : ∀ m : ℕ, (x:ℂ)≠-(m:ℂ) := by
      intro m hm
      have h := congrArg Complex.re hm
      simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at h
      nlinarith [Nat.cast_nonneg (α:=ℝ) m,hx.1]
    exact (Complex.differentiableAt_Gamma _ hne).continuousAt.comp Complex.continuous_ofReal.continuousAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let n : ℕ := Nat.ceil b
  let C : ℝ := (1+|M|)*2*(1+Real.pi)*((n:ℝ)+1)^n
  refine ⟨C,by dsimp [C]; positivity, n+1,fun σ τ hσa hσb => ?_⟩
  have hσ : 0<σ := ha.trans_le hσa
  have hσn : σ<(n:ℝ)+1 := hσb.trans_lt (by
    have h := Nat.le_ceil b
    dsimp [n]
    linarith)
  have hg := gamma_vertical_compare_integer n hσ hσn τ
  have hreal : ‖Complex.Gamma (σ:ℂ)‖ ≤ 1+|M| :=
    (hM σ ⟨hσa,hσb⟩).trans (by linarith [le_abs_self M])
  have hi := gamma_integer_vertical_exp_bound n τ
  have hp : (n:ℝ)+1+|τ| ≤ ((n:ℝ)+1)*(1+|τ|) := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) n,abs_nonneg τ]
  have hπ : 1+Real.pi*|τ| ≤ (1+Real.pi)*(1+|τ|) := by
    nlinarith [Real.pi_pos,abs_nonneg τ]
  calc
    _ ≤ ‖Complex.Gamma (σ:ℂ)‖*‖Complex.Gamma ((n:ℂ)+1+I*(τ:ℂ))‖ := hg
    _ ≤ (1+|M|)*(2*(1+Real.pi*|τ|)*((n:ℝ)+1+|τ|)^n*
        Real.exp (-(Real.pi*|τ|)/2)) := mul_le_mul hreal hi (norm_nonneg _) (by positivity)
    _ ≤ (1+|M|)*(2*((1+Real.pi)*(1+|τ|))*(((n:ℝ)+1)*(1+|τ|))^n*
        Real.exp (-(Real.pi*|τ|)/2)) := by gcongr
    _ = _ := by dsimp [C]; rw [mul_pow,pow_succ]; ring_nf

/-- A fixed lower real-part bound gives polynomial growth on the entire
half-plane at nonzero large height. Fractional left real parts use the actual
functional equation and the positive-strip Beta estimate. -/
theorem zeta_fixed_halfplane_polynomial_value_bound (a : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ s : ℂ, a≤s.re → 1≤|s.im| →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^N := by
  obtain ⟨G,hG,N,hΓ⟩ := gamma_positive_fixed_strip_exp_bound
    (a := (1/2:ℝ)) (b := 1+|a|) (by norm_num) (by have h := abs_nonneg a; linarith)
  let C : ℝ := 1+9/2+9*G
  refine ⟨C,by dsimp [C]; positivity,N+1,fun s hs ht => ?_⟩
  have hbase : 1≤1+|s.im| := by linarith [abs_nonneg s.im]
  have hC₁ : (9/2:ℝ)≤C := by dsimp [C]; linarith
  have hC₂ : 9*G≤C := by dsimp [C]; linarith
  by_cases hr : (1/2:ℝ)≤s.re
  · have h := RvM.riemannZeta_linear_growth (δ := (1/2:ℝ)) (by norm_num) hr ht
    norm_num only [inv_div,inv_one,mul_one,one_div,one_mul] at h
    have hpow : |s.im|≤(1+|s.im|)^(N+1) := by
      calc
        _ ≤ 1+|s.im| := by linarith
        _ ≤ _ := by simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1≤N+1 by omega)
    calc
      _ ≤ (9/2:ℝ)*|s.im| := by nlinarith [h]
      _ ≤ C*(1+|s.im|)^(N+1) := mul_le_mul hC₁ hpow (abs_nonneg _) (by dsimp [C]; positivity)
  · let w : ℂ := 1-s
    have hwre : (1/2:ℝ)≤w.re := by change (1/2:ℝ)≤1-s.re; linarith
    have hwupper : w.re≤1+|a| := by
      change 1-s.re≤1+|a|
      linarith [neg_abs_le a]
    have hwim : |w.im|=|s.im| := by simp [w]
    have hΓw : ‖Complex.Gamma w‖≤G*(1+|s.im|)^N*Real.exp (-(Real.pi*|s.im|)/2) := by
      have h := hΓ w.re w.im hwre hwupper
      have hrepr : (w.re:ℂ)+I*(w.im:ℂ)=w := by rw [mul_comm I,Complex.re_add_im]
      rwa [hrepr,hwim] at h
    have hζw : ‖riemannZeta w‖≤(9/2:ℝ)*|s.im| := by
      have h := RvM.riemannZeta_linear_growth (δ := (1/2:ℝ)) (by norm_num) hwre (by simpa [hwim] using ht)
      rw [hwim] at h
      norm_num at h ⊢
      exact h
    have hn (m : ℕ) : w≠-(m:ℂ) := by
      intro hm
      have h := congrArg Complex.re hm
      simp only [Complex.neg_re,Complex.natCast_re] at h
      nlinarith [Nat.cast_nonneg (α:=ℝ) m]
    have hw1 : w≠1 := by intro h; rw [h] at hwim; simp at hwim; linarith
    have hζeq : riemannZeta s=zetaReflectionFactor w*riemannZeta w := by
      have h := riemannZeta_one_sub hn hw1
      have heq : 1-w=s := by dsimp [w]; ring_nf
      rw [heq] at h
      simpa only [zetaReflectionFactor,Complex.ofReal_mul,Complex.ofReal_ofNat] using h
    have hp : ‖(((2*Real.pi:ℝ):ℂ)^(-w))‖≤1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ)<2*Real.pi),Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by nlinarith [Real.pi_gt_three]) (by linarith)
    have him : (((Real.pi:ℂ)*w/2).im)=Real.pi*w.im/2 := by simp
    have habs : |(((Real.pi:ℂ)*w/2).im)|=Real.pi*|s.im|/2 := by
      rw [him,abs_div,abs_mul,abs_of_pos Real.pi_pos,hwim]
      norm_num
    have hcos := complex_cos_norm_le_exp_abs_im ((Real.pi:ℂ)*w/2)
    rw [habs] at hcos
    have he : Real.exp (-(Real.pi*|s.im|)/2)*Real.exp (Real.pi*|s.im|/2)=1 := by
      rw [←Real.exp_add]
      convert Real.exp_zero using 1
      ring_nf
    calc
      _ = 2*‖(((2*Real.pi:ℝ):ℂ)^(-w))‖*‖Complex.Gamma w‖*
          ‖Complex.cos ((Real.pi:ℂ)*w/2)‖*‖riemannZeta w‖ := by
        rw [hζeq]
        simp only [zetaReflectionFactor,norm_mul,Complex.norm_ofNat]
      _ ≤ 2*1*(G*(1+|s.im|)^N*Real.exp (-(Real.pi*|s.im|)/2))*
          Real.exp (Real.pi*|s.im|/2)*((9/2:ℝ)*|s.im|) := by gcongr
      _ = 9*G*|s.im| *(1+|s.im|)^N := by
        calc
          _ = (9*G*|s.im| *(1+|s.im|)^N)*
              (Real.exp (-(Real.pi*|s.im|)/2)*Real.exp (Real.pi*|s.im|/2)) := by ring_nf
          _ = _ := by rw [he,mul_one]
      _ ≤ 9*G*(1+|s.im|)^(N+1) := by
        calc
          _ = (9*G*(1+|s.im|)^N)*|s.im| := by ring_nf
          _ ≤ (9*G*(1+|s.im|)^N)*(1+|s.im|) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = _ := by rw [pow_succ]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right hC₂ (by positivity)

/-- A fixed-radius genuine Cauchy estimate prices the zeta derivative on the
whole half-plane, using the value estimate on a slightly larger half-plane. -/
theorem zeta_fixed_halfplane_polynomial_value_derivative_bound (a : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ s : ℂ, a≤s.re → 2≤|s.im| →
      ‖riemannZeta s‖+‖deriv riemannZeta s‖ ≤ C*(1+|s.im|)^N := by
  obtain ⟨C,hC,N,hvalue⟩ := zeta_fixed_halfplane_polynomial_value_bound (a-1)
  let D : ℝ := C*(1+2*2^N)
  refine ⟨D,by dsimp [D]; positivity,N,fun s hs ht => ?_⟩
  have hgeometry (z : ℂ) (hz : dist z s≤1/2) :
      a-1≤z.re ∧ 1≤|z.im| ∧ 1+|z.im|≤2*(1+|s.im|) := by
    have hnorm : ‖z-s‖≤1/2 := by simpa only [dist_eq_norm] using hz
    have hre : |z.re-s.re|≤1/2 := by
      simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z-s)).trans hnorm
    have him : |z.im-s.im|≤1/2 := by
      simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z-s)).trans hnorm
    have hrere := abs_le.mp hre
    have hdown := abs_sub_abs_le_abs_sub s.im z.im
    rw [abs_sub_comm] at hdown
    have hup := abs_sub_abs_le_abs_sub z.im s.im
    exact ⟨by linarith,by linarith,by linarith [abs_nonneg s.im]⟩
  have hdiff : DiffContOnCl ℂ riemannZeta (Metric.ball s (1/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s (by norm_num)]
    intro z hz
    have hgeom := hgeometry z (Metric.mem_closedBall.mp hz)
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro hz1
    rw [hz1] at hgeom
    norm_num at hgeom
  have hsphere : ∀ z∈Metric.sphere s (1/2),
      ‖riemannZeta z‖≤C*2^N*(1+|s.im|)^N := by
    intro z hz
    have hgeom := hgeometry z (Metric.mem_sphere.mp hz).le
    calc
      _ ≤ C*(1+|z.im|)^N := hvalue z hgeom.1 hgeom.2.1
      _ ≤ C*(2*(1+|s.im|))^N := by gcongr; exact hgeom.2.2
      _ = _ := by rw [mul_pow]; ring_nf
  have hderiv : ‖deriv riemannZeta s‖≤2*C*2^N*(1+|s.im|)^N := by
    calc
      _ ≤ (C*2^N*(1+|s.im|)^N)/(1/2) :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hdiff hsphere
      _ = _ := by ring_nf
  have hv := hvalue s (by linarith) (by linarith)
  calc
    _ ≤ C*(1+|s.im|)^N+2*C*2^N*(1+|s.im|)^N := add_le_add hv hderiv
    _ = _ := by dsimp [D]; ring_nf

theorem zeta_fixed_strip_polynomial_value_derivative_bound (a b : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), a≤σ → σ≤b → 2≤|τ| →
      ‖riemannZeta ((σ:ℂ)+(τ:ℂ)*I)‖+‖deriv riemannZeta ((σ:ℂ)+(τ:ℂ)*I)‖ ≤
        C*(1+|τ|)^N := by
  obtain ⟨C,hC,N,h⟩ := zeta_fixed_halfplane_polynomial_value_derivative_bound a
  refine ⟨C,hC,N,fun σ τ hσ _ ht => ?_⟩
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    mul_zero,Complex.ofReal_im,Complex.I_im,mul_one,sub_self,add_zero,Complex.add_im,
    Complex.mul_im,zero_add] using h ((σ:ℂ)+(τ:ℂ)*I) (by simpa using hσ) (by simpa using ht)

end Zeta23.OPICAFollowup
