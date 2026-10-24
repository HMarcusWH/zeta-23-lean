import Zeta23.OPICAFollowup.NativeSourceTransforms
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Zeta23.OPICAFollowup.ZetaLeftLineBounds
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
open MeasureTheory Set Real
namespace Zeta23.OPICAFollowup

theorem sqrt_decay_moment_integrableOn {c : ℝ} (hc : 0 < c) (N : ℕ) :
    IntegrableOn (fun t : ℝ => t^N*Real.exp (-c*Real.sqrt t)) (Ioi 0) := by
  simpa only [Real.rpow_natCast,← Real.sqrt_eq_rpow] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1/2) (s := N)
      (b := c) (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by norm_num) hc

theorem sqrt_decay_moment_integral_Ioi {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∫ t in Ioi (0:ℝ), t^N*Real.exp (-c*Real.sqrt t)) =
      2*((2*N+1).factorial:ℝ)/c^(2*N+2) := by
  calc
    _ = c^(-((N:ℝ)+1)/(1/2))*(1/(1/2))*Real.Gamma (((N:ℝ)+1)/(1/2)) := by
      simpa only [Real.rpow_natCast,← Real.sqrt_eq_rpow] using
        integral_rpow_mul_exp_neg_mul_rpow (p := 1/2) (q := N) (b := c)
          (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) N; linarith) hc
    _ = _ := by
      rw [show -((N:ℝ)+1)/(1/2) = -((2*N+2:ℕ):ℝ) by push_cast; ring,
        show ((N:ℝ)+1)/(1/2) = ((2*N+1:ℕ):ℝ)+1 by push_cast; ring,
        Real.rpow_neg hc.le,Real.rpow_natCast,Real.Gamma_nat_eq_factorial]
      norm_num
      ring

theorem sqrt_decay_moment_integrable {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Integrable (fun t : ℝ => |t|^N*Real.exp (-c*Real.sqrt |t|)) := by
  let f : ℝ → ℝ := fun t => |t|^N*Real.exp (-c*Real.sqrt |t|)
  have hpos : IntegrableOn f (Ioi 0) :=
    (sqrt_decay_moment_integrableOn hc N).congr_fun
      (fun t ht => by dsimp [f]; rw [abs_of_pos ht]) measurableSet_Ioi
  have hneg : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simpa only [Function.comp_def,f,abs_neg,neg_preimage,neg_Iic,neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos)
  simpa only [Iic_union_Ioi,integrableOn_univ] using hneg.union hpos

theorem sqrt_decay_moment_integral {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∫ t : ℝ, |t|^N*Real.exp (-c*Real.sqrt |t|)) =
      4*((2*N+1).factorial:ℝ)/c^(2*N+2) := by
  change (∫ t : ℝ, (fun x : ℝ => x^N*Real.exp (-c*Real.sqrt x)) |t|) = _
  rw [integral_comp_abs (f := fun x : ℝ => x^N*Real.exp (-c*Real.sqrt x)),
    sqrt_decay_moment_integral_Ioi hc N]
  ring

theorem shifted_power_split {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (N : ℕ) :
    (a+u)^N ≤ (2:ℝ)^N*(a^N+u^N) := by
  have hmax : a+u ≤ 2*max a u := by
    have h1 := le_max_left a u
    have h2 := le_max_right a u
    linarith
  have hm : (max a u)^N ≤ a^N+u^N := by
    rcases le_total a u with h | h
    · rw [max_eq_right h]
      linarith [pow_nonneg ha N]
    · rw [max_eq_left h]
      linarith [pow_nonneg hu N]
  calc
    _ ≤ (2*max a u)^N := pow_le_pow_left₀ (add_nonneg ha hu) hmax N
    _ = (2:ℝ)^N*(max a u)^N := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

theorem shifted_sqrt_decay_integrable {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (N : ℕ) :
    Integrable (fun t : ℝ => (a+|t|)^N*Real.exp (-c*Real.sqrt |t|)) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-c*Real.sqrt |t|)) := by
    simpa only [pow_zero,one_mul] using sqrt_decay_moment_integrable hc 0
  have he := ((h0.const_mul (a^N)).add (sqrt_decay_moment_integrable hc N)).const_mul ((2:ℝ)^N)
  apply he.mono'
  · fun_prop
  · exact Filter.Eventually.of_forall fun t => by
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hp := mul_le_mul_of_nonneg_right (shifted_power_split ha (abs_nonneg t) N)
        (Real.exp_nonneg (-c*Real.sqrt |t|))
      nlinarith

theorem shifted_sqrt_decay_integral_bound {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (N : ℕ) :
    (∫ t : ℝ, (a+|t|)^N*Real.exp (-c*Real.sqrt |t|)) ≤
      (2:ℝ)^N*(a^N*4/c^2+4*((2*N+1).factorial:ℝ)/c^(2*N+2)) := by
  have h0 : Integrable (fun t : ℝ => Real.exp (-c*Real.sqrt |t|)) := by
    simpa only [pow_zero,one_mul] using sqrt_decay_moment_integrable hc 0
  have he := ((h0.const_mul (a^N)).add (sqrt_decay_moment_integrable hc N)).const_mul ((2:ℝ)^N)
  have hi0 : (∫ t : ℝ, Real.exp (-c*Real.sqrt |t|)) = 4/c^2 := by
    simpa using sqrt_decay_moment_integral hc 0
  calc
    _ ≤ ∫ t : ℝ, (2:ℝ)^N*(a^N*Real.exp (-c*Real.sqrt |t|)+
        |t|^N*Real.exp (-c*Real.sqrt |t|)) := by
      apply integral_mono (shifted_sqrt_decay_integrable ha hc N) he
      intro t
      dsimp only [Pi.add_apply]
      have hp := mul_le_mul_of_nonneg_right (shifted_power_split ha (abs_nonneg t) N)
        (Real.exp_nonneg (-c*Real.sqrt |t|))
      nlinarith
    _ = _ := by
      rw [integral_const_mul,integral_add (h0.const_mul (a^N))
        (sqrt_decay_moment_integrable hc N),integral_const_mul,hi0,sqrt_decay_moment_integral hc N]
      ring

open Zeta23.CCM Zeta23.ExceptionalZero

def forwardLeftContour (n : ℕ) (τ : ℝ) : ℂ :=
  -(((n:ℝ)+1/2):ℂ)+Complex.I*(τ:ℂ)

theorem sourceFamilyLaplace_box_formula (d : ℕ) (z : ℂ) :
    sourceFamilyLaplace d z = (z^2-1/4)^(d+2)*sourceBoxProduct z := by
  rw [sourceFamilyLaplace_factor,nativeOriginalSourceLaplace_formula]
  have hp : ((Complex.I*z)^2+1/4)^2 = (z^2-1/4)^2 := by rw [mul_pow,Complex.I_sq]; ring
  rw [hp,pow_add]
  dsimp [sourceBoxProduct]
  ring

theorem forwardLeftContour_norm (n : ℕ) (τ : ℝ) :
    ‖forwardLeftContour n τ‖ ≤ (n:ℝ)+1/2+|τ| := by
  have hh := Complex.norm_le_abs_re_add_abs_im (forwardLeftContour n τ)
  have hre : (forwardLeftContour n τ).re = -((n:ℝ)+1/2) := by simp [forwardLeftContour]
  have him : (forwardLeftContour n τ).im = τ := by simp [forwardLeftContour]
  rw [hre,him,abs_neg,abs_of_nonneg (by positivity)] at hh
  exact hh

theorem forwardLeftContour_source_bound (d n : ℕ) (τ : ℝ) :
    ‖sourceFamilyLaplace d (forwardLeftContour n τ)‖ ≤
      (2:ℝ)^(d+2)*((n:ℝ)+2+|τ|)^(2*(d+2))*
        (8*Real.exp (UniversalSinc.fixedScale*((n:ℝ)+1/2))*
          Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) := by
  let B : ℝ := (n:ℝ)+2+|τ|
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α := ℝ) n,abs_nonneg τ]
  have hz : ‖forwardLeftContour n τ‖ ≤ B :=
    (forwardLeftContour_norm n τ).trans (by dsimp [B]; linarith)
  have hpoly : ‖(forwardLeftContour n τ)^2-1/4‖ ≤ 2*B^2 := by
    have hh := norm_sub_le ((forwardLeftContour n τ)^2) (1/4:ℂ)
    rw [norm_pow] at hh
    norm_num at hh
    have hs := pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith
  have hq : ‖sourceBoxProduct (forwardLeftContour n τ)‖ ≤
      8*Real.exp (UniversalSinc.fixedScale*((n:ℝ)+1/2))*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) := by
    have hb := source_product_vertical_bound (-((n:ℝ)+1/2)) τ
    rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1/2)] at hb
    simpa [forwardLeftContour,Complex.ofReal_add,Complex.ofReal_div] using hb
  rw [sourceFamilyLaplace_box_formula,norm_mul,norm_pow]
  calc
    _ ≤ (2*B^2)^(d+2)*(8*Real.exp (UniversalSinc.fixedScale*((n:ℝ)+1/2))*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpoly (d+2)) hq (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow,← pow_mul]

/-- Fixed orders give one envelope uniform over all positive integer contour shifts.
The exponent slack is explicitly `2*b+1`; the constants depend only on `a,b,c`.
The statement even permits `a=0`, although Q2 uses `a=ell+1≥1`. -/
theorem fixed_linear_factorial_envelope (a b : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      (2:ℝ)^(a*n+b) *
        (((n:ℝ)+2)^(a*n+b)*4/c^2 +
          4*((2*(a*n+b)+1).factorial:ℝ)/c^(2*(a*n+b)+2)) ≤
        C*Real.exp (D*(n:ℝ))*(n:ℝ)^(2*a*n+(2*b+1)) := by
  let L : ℝ := max 1 c⁻¹
  let K : ℝ := 3+2*(a:ℝ)+2*(b:ℝ)
  let E : ℝ := 2^a*L^(2*a)*K^(2*a)
  let C : ℝ := 8*2^b*L^(2*b+2)*K^(2*b+1)
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hinv : c⁻¹ ≤ L := le_max_right _ _
  have hK : 3 ≤ K := by
    dsimp [K]
    nlinarith [show (0:ℝ) ≤ (a:ℝ) from Nat.cast_nonneg a,
      show (0:ℝ) ≤ (b:ℝ) from Nat.cast_nonneg b]
  have hKpos : 0 < K := by linarith
  have hE : 1 ≤ E := by
    dsimp [E]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hL))
      (one_le_pow₀ (by linarith))
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  refine ⟨C, Real.log E, by dsimp [C]; positivity, Real.log_nonneg hE, ?_⟩
  intro n hn
  let N : ℕ := a*n+b
  let m : ℕ := 2*N+1
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hM : 1 ≤ K*(n:ℝ) := by nlinarith
  have hnm : (n:ℝ)+2 ≤ K*(n:ℝ) := by nlinarith
  have hNm : N ≤ m := by dsimp [m]; omega
  have hm : (m:ℝ) ≤ K*(n:ℝ) := by
    have hb : 0 ≤ 2*(b:ℝ)+3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hnr hb
    dsimp [m,N,K]
    push_cast
    nlinarith
  have hpoly : ((n:ℝ)+2)^N ≤ (K*(n:ℝ))^m :=
    (pow_le_pow_left₀ (by positivity) hnm N).trans (pow_le_pow_right₀ hM hNm)
  have hfac : (m.factorial:ℝ) ≤ (K*(n:ℝ))^m := by
    have hfac₀ : (m.factorial:ℝ) ≤ (m:ℝ)^m := by exact_mod_cast Nat.factorial_le_pow m
    exact hfac₀.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hm m)
  have hci : ∀ j : ℕ, (c⁻¹)^j ≤ L^j :=
    fun j => pow_le_pow_left₀ (inv_pos.mpr hc).le hinv j
  have hci₂ : (c⁻¹)^2 ≤ L^(2*N+2) :=
    (hci 2).trans (pow_le_pow_right₀ hL (by omega))
  have hfirst : ((n:ℝ)+2)^N*4/c^2 ≤ 4*(K*(n:ℝ))^m*L^(2*N+2) := by
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      ((n:ℝ)+2)^N*4*(c⁻¹)^2 = 4*((n:ℝ)+2)^N*(c⁻¹)^2 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by norm_num)) hci₂
        (by positivity) (by positivity)
  have hsecond : 4*(m.factorial:ℝ)/c^(2*N+2) ≤
      4*(K*(n:ℝ))^m*L^(2*N+2) := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hfac (by norm_num)) (hci _)
      (by positivity) (by positivity)
  have hbudget : (2:ℝ)^N *
      (((n:ℝ)+2)^N*4/c^2 + 4*(m.factorial:ℝ)/c^(2*N+2)) ≤
      8*2^N*L^(2*N+2)*(K*(n:ℝ))^m := by
    have hadd := add_le_add hfirst hsecond
    calc
      _ ≤ (2:ℝ)^N*(4*(K*(n:ℝ))^m*L^(2*N+2) +
          4*(K*(n:ℝ))^m*L^(2*N+2)) :=
        mul_le_mul_of_nonneg_left hadd (by positivity)
      _ = _ := by ring
  have hN₂ : 2*N+2 = (2*a)*n+(2*b+2) := by dsimp [N]; ring
  have hm₂ : m = (2*a)*n+(2*b+1) := by dsimp [m,N]; ring
  have hsplit : 8*2^N*L^(2*N+2)*(K*(n:ℝ))^m =
      C*E^n*(n:ℝ)^m := by
    dsimp [C,E,N]
    rw [hN₂, mul_pow, hm₂]
    simp only [pow_add, pow_mul, mul_pow]
    ring
  have hexp : Real.exp (Real.log E*(n:ℝ)) = E^n := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hEpos]
  change (2:ℝ)^N *
      (((n:ℝ)+2)^N*4/c^2 + 4*(m.factorial:ℝ)/c^(2*N+2)) ≤ _
  calc
    _ ≤ _ := hbudget
    _ = C*E^n*(n:ℝ)^m := hsplit
    _ = _ := by rw [hexp, hm₂]


def forwardContourIntegrand (d ell k n : ℕ) (τ : ℝ) : ℂ :=
  let z := forwardLeftContour n τ
  z^k*(-sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2))

theorem forwardContour_pointwise_budget (d ell k : ℕ) :
    ∃ C0 D0 : ℝ, 0 < C0 ∧ 0 < D0 ∧ ∀ n : ℕ, 1 ≤ n → ∀ τ : ℝ,
      ‖forwardContourIntegrand d ell k n τ‖ ≤
        C0*D0^n*((n:ℝ)+2+|τ|)^((ell+1)*n+(2*(ell+1)+2*(d+2)+k))*
          Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) := by
  obtain ⟨A0,hA0,hzeta⟩ := zeta_left_line_uniform_bound
  let C0 := 8*(2:ℝ)^(d+2)*Real.exp (UniversalSinc.fixedScale/2)*A0^(ell+1)
  let D0 := Real.exp UniversalSinc.fixedScale*A0^(ell+1)
  have hApos : 0 < A0 := zero_lt_one.trans_le hA0
  refine ⟨C0,D0,by dsimp [C0]; positivity,by dsimp [D0]; positivity,?_⟩
  intro n hn τ
  let z := forwardLeftContour n τ
  let B : ℝ := (n:ℝ)+2+|τ|
  let P : ℝ := A0^(n+1)*B^(n+2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hshift : z+1/2 = -(n:ℂ)+Complex.I*(τ:ℂ) := by
    dsimp [z,forwardLeftContour]
    ring
  have hzsum : ‖riemannZeta (z+1/2)‖+‖deriv riemannZeta (z+1/2)‖ ≤ P := by
    rw [hshift]
    exact hzeta n hn τ
  have hzval : ‖riemannZeta (z+1/2)‖ ≤ P := by nlinarith [norm_nonneg (deriv riemannZeta (z+1/2))]
  have hzder : ‖deriv riemannZeta (z+1/2)‖ ≤ P := by nlinarith [norm_nonneg (riemannZeta (z+1/2))]
  have hzprod : ‖riemannZeta (z+1/2)‖^ell*‖deriv riemannZeta (z+1/2)‖ ≤ P^(ell+1) := by
    rw [pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hzval ell) hzder
      (norm_nonneg _) (pow_nonneg hP ell)
  have hznorm : ‖z‖ ≤ B :=
    (forwardLeftContour_norm n τ).trans (by dsimp [B]; linarith)
  have hj := forwardLeftContour_source_bound d n τ
  have he : Real.exp (UniversalSinc.fixedScale*((n:ℝ)+1/2)) =
      Real.exp (UniversalSinc.fixedScale/2)*(Real.exp UniversalSinc.fixedScale)^n := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  have hAexp : (n+1)*(ell+1) = (ell+1)*n+(ell+1) := by ring
  have hBexp : (ell+1)*n+(2*(ell+1)+2*(d+2)+k) =
      k+2*(d+2)+(n+2)*(ell+1) := by ring
  change ‖z^k*(-sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2))‖ ≤ _
  simp only [norm_mul,norm_neg,norm_pow]
  calc
    _ = ‖z‖^k*‖sourceFamilyLaplace d z‖*
        (‖riemannZeta (z+1/2)‖^ell*‖deriv riemannZeta (z+1/2)‖) := by ring
    _ ≤ B^k*((2:ℝ)^(d+2)*B^(2*(d+2))*
        (8*Real.exp (UniversalSinc.fixedScale*((n:ℝ)+1/2))*
          Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)))*P^(ell+1) :=
      mul_le_mul
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hznorm k) hj
          (norm_nonneg _) (by positivity)) hzprod (by positivity) (by positivity)
    _ = _ := by
      dsimp [P,C0,D0,B]
      rw [mul_pow,← pow_mul,he,hAexp,hBexp]
      simp only [pow_add,mul_pow,pow_mul]
      ring

theorem forwardContourIntegrand_eq_germ (d ell k n : ℕ) (τ : ℝ) :
    forwardContourIntegrand d ell k n τ =
      (forwardLeftContour n τ)^k*forwardKernelTransformGerm d ell (forwardLeftContour n τ) := rfl

theorem forwardContourIntegrand_continuous (d ell k n : ℕ) :
    Continuous (forwardContourIntegrand d ell k n) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  have hz : forwardLeftContour n τ ≠ 1/2 := by
    intro h
    have hh := congrArg Complex.re h
    simp [forwardLeftContour] at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have ha := (analyticAt_id.pow k).mul (forwardKernelTransformGerm_analyticAt (d := d) (ell := ell) hz)
  have hc : Continuous (forwardLeftContour n) := by unfold forwardLeftContour; fun_prop
  change ContinuousAt (fun τ => (forwardLeftContour n τ)^k*
    forwardKernelTransformGerm d ell (forwardLeftContour n τ)) τ
  exact ha.continuousAt.comp hc.continuousAt

/-- The full contour-index cost is established before saddle selection. This
bound concerns the literal source transform and actual zeta factors; physical
inversion and the optimized decay statement are separate obligations. -/
theorem forwardKernel_left_contour_budget (d ell k : ℕ) :
    ∃ C D : ℝ, ∃ B : ℕ, 0 < C ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (forwardContourIntegrand d ell k n) ∧
      (∫ τ : ℝ, ‖forwardContourIntegrand d ell k n τ‖) ≤
        C*Real.exp (D*(n:ℝ))*(n:ℝ)^(2*(ell+1)*n+B) := by
  obtain ⟨C0,D0,hC0,hD0,hpoint⟩ := forwardContour_pointwise_budget d ell k
  let a := ell+1
  let b := 2*(ell+1)+2*(d+2)+k
  obtain ⟨C1,D1,hC1,hD1,hfac⟩ :=
    fixed_linear_factorial_envelope a b sourceVerticalDecayConstant_pos
  let C := C0*C1
  let D := max 0 (D1+Real.log D0)
  refine ⟨C,D,2*b+1,mul_pos hC0 hC1,le_max_left _ _,?_⟩
  intro n hn
  let N := a*n+b
  have hshift := shifted_sqrt_decay_integrable (show 0 ≤ (n:ℝ)+2 by positivity)
    sourceVerticalDecayConstant_pos N
  have hmajor := hshift.const_mul (C0*D0^n)
  have hpointN (τ : ℝ) : ‖forwardContourIntegrand d ell k n τ‖ ≤
      C0*D0^n*(((n:ℝ)+2+|τ|)^N*Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) := by
    have hp := hpoint n hn τ
    dsimp [N,a,b]
    nlinarith
  have hint : Integrable (forwardContourIntegrand d ell k n) :=
    hmajor.mono' (forwardContourIntegrand_continuous d ell k n).aestronglyMeasurable
      (Filter.Eventually.of_forall hpointN)
  refine ⟨hint,?_⟩
  have hpoly := shifted_sqrt_decay_integral_bound (show 0 ≤ (n:ℝ)+2 by positivity)
    sourceVerticalDecayConstant_pos N
  have heq : D0^n*Real.exp (D1*(n:ℝ)) = Real.exp ((D1+Real.log D0)*(n:ℝ)) := by
    have hp : D0^n = Real.exp (Real.log D0*(n:ℝ)) := by
      rw [mul_comm,Real.exp_nat_mul,Real.exp_log hD0]
    rw [hp,← Real.exp_add]
    congr 1
    ring
  have hDex : Real.exp ((D1+Real.log D0)*(n:ℝ)) ≤ Real.exp (D*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg n)
  calc
    _ ≤ ∫ τ : ℝ, C0*D0^n*(((n:ℝ)+2+|τ|)^N*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) := integral_mono hint.norm hmajor hpointN
    _ = C0*D0^n*(∫ τ : ℝ, ((n:ℝ)+2+|τ|)^N*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) := integral_const_mul _ _
    _ ≤ C0*D0^n*((2:ℝ)^N*(((n:ℝ)+2)^N*4/sourceVerticalDecayConstant^2+
        4*((2*N+1).factorial:ℝ)/sourceVerticalDecayConstant^(2*N+2))) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ C0*D0^n*(C1*Real.exp (D1*(n:ℝ))*(n:ℝ)^(2*a*n+(2*b+1))) :=
      mul_le_mul_of_nonneg_left (hfac n hn) (by positivity)
    _ = C0*C1*(D0^n*Real.exp (D1*(n:ℝ)))*(n:ℝ)^(2*a*n+(2*b+1)) := by ring
    _ = C0*C1*Real.exp ((D1+Real.log D0)*(n:ℝ))*(n:ℝ)^(2*a*n+(2*b+1)) := by rw [heq]
    _ ≤ _ := by dsimp [C,a]; gcongr


open Complex
open scoped FourierTransform

/-- Optimize a uniform integer contour budget. The `n = 1` estimate handles the
whole initial interval, so no unproved compact-time boundedness is supplied. -/
theorem integer_contour_saddle_decay {f : ℝ → ℝ} {C D a : ℝ} {B : ℕ}
    (hC : 0 < C) (hD : 0 ≤ D) (ha : 0 < a)
    (hbudget : ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
      f t ≤ C * Real.exp (D*(n:ℝ) - (n:ℝ)*t) *
        (n:ℝ)^(2*(a:ℝ)*n+B : ℝ)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      f t ≤ A * Real.exp (-c*Real.exp (t/(2*a))) := by
  let K : ℝ := (D+B+2)/(2*a)
  let c : ℝ := Real.exp (-K)
  let A : ℝ := C * Real.exp D * Real.exp 2
  have hc : 0 < c := Real.exp_pos _
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,c,hA,hc,?_⟩
  intro t ht
  let x : ℝ := c*Real.exp (t/(2*a))
  have hx : 0 < x := mul_pos hc (Real.exp_pos _)
  have hxexp : x = Real.exp (t/(2*a)-K) := by
    dsimp [x,c]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [neg_mul]
  change f t ≤ A*Real.exp (-x)
  by_cases hx2 : 2 ≤ x
  · let n : ℕ := ⌊x⌋₊
    have hn : 1 ≤ n := Nat.le_floor (by norm_num; linarith)
    have hnr : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    have hnpos : 0 < (n:ℝ) := by linarith
    have hnle : (n:ℝ) ≤ x := Nat.floor_le hx.le
    have hnlow : x/2 ≤ (n:ℝ) := by
      have hfloor := Nat.lt_floor_add_one x
      change x < (n:ℝ)+1 at hfloor
      linarith
    have hlog : Real.log (n:ℝ) ≤ t/(2*a)-K := by
      calc
        _ ≤ Real.log x := Real.log_le_log hnpos hnle
        _ = _ := by rw [hxexp,Real.log_exp]
    have hlogsmall : Real.log (n:ℝ) ≤ (n:ℝ) := Real.log_le_self hnpos.le
    have hexp : D*(n:ℝ)-(n:ℝ)*t +
        (2*a*n+B)*Real.log (n:ℝ) ≤ -2*(n:ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2*a*(n:ℝ))
      have h2 := mul_le_mul_of_nonneg_left hlogsmall (Nat.cast_nonneg (α := ℝ) B)
      have hK : (2*a)*K = D+B+2 := by
        dsimp [K]
        field_simp
      have htdiv : (2*a)*(t/(2*a)) = t := mul_div_cancel₀ _ (by positivity)
      nlinarith
    have hpow : (n:ℝ)^(2*a*n+B : ℝ) =
        Real.exp ((2*a*n+B)*Real.log (n:ℝ)) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    have hCA : C ≤ A := by
      have h1 : 1 ≤ Real.exp D := Real.one_le_exp hD
      have h2 : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp (by norm_num)
      dsimp [A]
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left h1 hC.le).trans
        (le_mul_of_one_le_right (by positivity) h2)
    calc
      f t ≤ C*Real.exp (D*(n:ℝ)-(n:ℝ)*t)*(n:ℝ)^(2*a*n+B : ℝ) := hbudget n hn t ht
      _ = C*Real.exp (D*(n:ℝ)-(n:ℝ)*t+(2*a*n+B)*Real.log (n:ℝ)) := by
        rw [hpow,mul_assoc,← Real.exp_add]
      _ ≤ C*Real.exp (-2*(n:ℝ)) := by gcongr
      _ ≤ C*Real.exp (-x) := by gcongr; linarith
      _ ≤ A*Real.exp (-x) := mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le
  · have hxlt : x < 2 := lt_of_not_ge hx2
    have hsmall := hbudget 1 le_rfl t ht
    simp only [Nat.cast_one,one_mul,Real.one_rpow,mul_one] at hsmall
    have hbound : f t ≤ C*Real.exp D := hsmall.trans (by gcongr; linarith)
    calc
      f t ≤ C*Real.exp D := hbound
      _ ≤ C*Real.exp D*Real.exp (2-x) := by
        have he : 1 ≤ Real.exp (2-x) := Real.one_le_exp (by linarith)
        have hp : 0 < C*Real.exp D := mul_pos hC (Real.exp_pos _)
        nlinarith
      _ = A*Real.exp (-x) := by
        dsimp [A]
        rw [show (2:ℝ)-x = 2+(-x) by ring,Real.exp_add]
        ring



def dampedHistory (σ : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-((σ:ℂ)*(t:ℂ)))*f t

theorem fourier_dampedHistory (σ : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (dampedHistory σ f) ξ =
      ∫ t : ℝ, Complex.exp (-((σ:ℂ)+Complex.I*((2*Real.pi*ξ:ℝ):ℂ))*(t:ℂ))*f t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [dampedHistory,smul_eq_mul]
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Actual bilateral Laplace inversion at every continuity point, with the
normalizing Jacobian derived from Mathlib's `2π` Fourier convention. -/
theorem bilateralLaplace_inverse {σ : ℝ} {f : ℝ → ℂ} {F : ℂ → ℂ}
    (hf : Integrable (dampedHistory σ f))
    (hF : Integrable (fun τ : ℝ => F ((σ:ℂ)+Complex.I*(τ:ℂ))))
    (hLaplace : ∀ τ : ℝ,
      (∫ t : ℝ, Complex.exp (-((σ:ℂ)+Complex.I*(τ:ℂ))*(t:ℂ))*f t) =
        F ((σ:ℂ)+Complex.I*(τ:ℂ)))
    {t : ℝ} (hcont : ContinuousAt f t) :
    f t = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, Complex.exp (((σ:ℂ)+Complex.I*(τ:ℂ))*(t:ℂ))*
        F ((σ:ℂ)+Complex.I*(τ:ℂ)) := by
  have hfourier : 𝓕 (dampedHistory σ f) =
      fun ξ : ℝ => F ((σ:ℂ)+Complex.I*((2*Real.pi*ξ:ℝ):ℂ)) := by
    funext ξ
    rw [fourier_dampedHistory,hLaplace]
  have hscale : (2*Real.pi:ℝ) ≠ 0 := by positivity
  have hfourierInt : Integrable (𝓕 (dampedHistory σ f)) := by
    rw [hfourier]
    exact hF.comp_mul_left' hscale
  have hdcont : ContinuousAt (dampedHistory σ f) t :=
    (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-((σ:ℂ)*(x:ℂ))))).continuousAt.mul hcont
  have hinv := hf.fourierInv_fourier_eq hfourierInt hdcont
  let g : ℝ → ℂ := fun τ =>
    Complex.exp (Complex.I*(τ:ℂ)*(t:ℂ))*F ((σ:ℂ)+Complex.I*(τ:ℂ))
  have hnormalize : (𝓕⁻ (𝓕 (dampedHistory σ f))) t =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, g τ) := by
    calc
      _ = ∫ ξ : ℝ, g ((2*Real.pi)*ξ) := by
        rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,hfourier]
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [g,smul_eq_mul]
        congr 2
        push_cast
        ring
      _ = |((2*Real.pi:ℝ))⁻¹| • ∫ τ : ℝ, g τ :=
        Measure.integral_comp_mul_left g (2*Real.pi)
      _ = _ := by
        rw [abs_of_pos (inv_pos.mpr (by positivity)),RCLike.real_smul_eq_coe_mul]
        simp only [one_div]
        congr 1
  have hcancel : Complex.exp ((σ:ℂ)*(t:ℂ))*dampedHistory σ f t = f t := by
    dsimp [dampedHistory]
    rw [← mul_assoc,← Complex.exp_add]
    simp
  calc
    f t = Complex.exp ((σ:ℂ)*(t:ℂ))*dampedHistory σ f t := hcancel.symm
    _ = Complex.exp ((σ:ℂ)*(t:ℂ))*
        (((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, g τ)) := by rw [← hinv,hnormalize]
    _ = ((1/(2*Real.pi):ℝ):ℂ)*
        (∫ τ : ℝ, Complex.exp ((σ:ℂ)*(t:ℂ))*g τ) := by
      rw [integral_const_mul]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      dsimp [g]
      rw [← mul_assoc,← Complex.exp_add]
      congr 2
      ring


theorem bilateral_inverse_integrand_norm (σ t τ : ℝ) (F : ℂ → ℂ) :
    ‖Complex.exp (((σ:ℂ)+I*(τ:ℂ))*(t:ℂ))*F ((σ:ℂ)+I*(τ:ℂ))‖ =
      Real.exp (σ*t)*‖F ((σ:ℂ)+I*(τ:ℂ))‖ := by
  rw [norm_mul,Complex.norm_exp]
  congr 2
  simp

theorem bilateral_inverse_integrable (σ t : ℝ) (F : ℂ → ℂ)
    (hF : Integrable (fun τ : ℝ => F ((σ:ℂ)+I*(τ:ℂ)))) :
    Integrable (fun τ : ℝ =>
      Complex.exp (((σ:ℂ)+I*(τ:ℂ))*(t:ℂ))*F ((σ:ℂ)+I*(τ:ℂ))) := by
  apply (hF.norm.const_mul (Real.exp (σ*t))).mono'
  · exact (by fun_prop : Continuous (fun τ : ℝ =>
      Complex.exp (((σ:ℂ)+I*(τ:ℂ))*(t:ℂ)))).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · filter_upwards with τ
    exact (bilateral_inverse_integrand_norm σ t τ F).le

theorem norm_bilateralLaplace_inverse_le {σ t : ℝ} {f : ℝ → ℂ} {F : ℂ → ℂ}
    (hf : Integrable (dampedHistory σ f))
    (hF : Integrable (fun τ : ℝ => F ((σ:ℂ)+I*(τ:ℂ))))
    (hLaplace : ∀ τ : ℝ,
      (∫ u : ℝ, Complex.exp (-((σ:ℂ)+I*(τ:ℂ))*(u:ℂ))*f u) =
        F ((σ:ℂ)+I*(τ:ℂ)))
    (hcont : ContinuousAt f t) :
    ‖f t‖ ≤ (1/(2*Real.pi))*Real.exp (σ*t)*
      (∫ τ : ℝ, ‖F ((σ:ℂ)+I*(τ:ℂ))‖) := by
  rw [bilateralLaplace_inverse hf hF hLaplace hcont,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (by positivity : 0<(1/(2*Real.pi):ℝ))]
  calc
    _ ≤ (1/(2*Real.pi))*(∫ τ : ℝ,
        ‖Complex.exp (((σ:ℂ)+I*(τ:ℂ))*(t:ℂ))*F ((σ:ℂ)+I*(τ:ℂ))‖) := by
      apply mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by
      simp_rw [bilateral_inverse_integrand_norm]
      rw [integral_const_mul]
      ring

open Filter Set
open scoped Topology BigOperators

theorem shifted_sqrt_decay_tendsto {L c : ℝ} (hL : 0≤L) (hc : 0<c) (N : ℕ) :
    Tendsto (fun τ : ℝ => (L+|τ|)^N*Real.exp (-c*Real.sqrt |τ|)) atTop (𝓝 0) ∧
    Tendsto (fun τ : ℝ => (L+|τ|)^N*Real.exp (-c*Real.sqrt |τ|)) atBot (𝓝 0) := by
  have hm (m : ℕ) : Tendsto (fun x : ℝ => x^m*Real.exp (-c*Real.sqrt x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*m) c hc).comp
      Real.tendsto_sqrt_atTop
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Function.comp_apply]
    rw [show (2*(m:ℝ))=((2*m:ℕ):ℝ) by push_cast; ring_nf,
      Real.rpow_natCast,pow_mul,Real.sq_sqrt hx]
  have hall (l : Filter ℝ) (hl : Tendsto (fun τ : ℝ => |τ|) l atTop) :
      Tendsto (fun τ : ℝ => (L+|τ|)^N*Real.exp (-c*Real.sqrt |τ|)) l (𝓝 0) := by
    have h0 : Tendsto (fun τ : ℝ => Real.exp (-c*Real.sqrt |τ|)) l (𝓝 0) := by
      simpa only [Function.comp_def,pow_zero,one_mul] using (hm 0).comp hl
    have hN := (hm N).comp hl
    apply squeeze_zero (fun τ => by positivity)
      (fun τ => mul_le_mul_of_nonneg_right (shifted_power_split hL (abs_nonneg τ) N)
        (Real.exp_nonneg _))
    have hlim := ((h0.const_mul (L^N)).add hN).const_mul ((2:ℝ)^N)
    simpa only [Function.comp_def,mul_zero,zero_add] using hlim.congr (fun τ => by dsimp [Function.comp_def]; ring_nf)
  exact ⟨hall atTop tendsto_abs_atTop_atTop,hall atBot tendsto_abs_atBot_atTop⟩

theorem forwardEntire_fixed_strip_large_height_bound (d ell k : ℕ) (hd : ell≤d)
    (a b t : ℝ) :
    ∃ A : ℝ, 0<A ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), a≤σ → σ≤b → 2≤|τ| →
      ‖(((σ:ℂ)+(τ:ℂ)*I)^k*forwardKernelEntireContinuation d ell ((σ:ℂ)+(τ:ℂ)*I))*
          Complex.exp (((σ:ℂ)+(τ:ℂ)*I)*(t:ℂ))‖ ≤
        A*(1+|a|+|b|+|τ|)^N*Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) := by
  obtain ⟨G,hG,N,hζ⟩ := zeta_fixed_halfplane_polynomial_value_derivative_bound (a+1/2)
  let L : ℝ := 1+|a|+|b|
  let A : ℝ := 8*2^(d+2)*Real.exp (Zeta23.CCM.UniversalSinc.fixedScale*L)*
    G^(ell+1)*Real.exp (L*|t|)
  refine ⟨A,by dsimp [A]; positivity,k+2*(d+2)+N*(ell+1),fun σ τ hσa hσb ht => ?_⟩
  let z : ℂ := (σ:ℂ)+(τ:ℂ)*I
  let B : ℝ := L+|τ|
  have hL : 1≤L := by dsimp [L]; linarith [abs_nonneg a,abs_nonneg b]
  have hB : 1≤B := by dsimp [B]; linarith [abs_nonneg τ]
  have hσ : |σ|≤L := by
    rw [abs_le]
    constructor <;> dsimp [L] <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hzre : z.re=σ := by simp [z]
  have hzim : z.im=τ := by simp [z]
  have hz : ‖z‖≤B := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [hzre,hzim] at h
    exact h.trans (by dsimp [B]; linarith)
  have hp : ‖z^2-1/4‖≤2*B^2 := by
    have h := norm_sub_le (z^2) (1/4:ℂ)
    rw [norm_pow] at h
    norm_num at h
    have hs := pow_le_pow_left₀ (norm_nonneg _) hz 2
    nlinarith
  have hbox : ‖sourceBoxProduct z‖≤8*Real.exp (Zeta23.CCM.UniversalSinc.fixedScale*L)*
      Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) := by
    have h := source_product_vertical_bound σ τ
    have hrepr : (σ:ℂ)+I*(τ:ℂ)=z := by dsimp [z]; ring_nf
    rw [hrepr] at h
    exact h.trans (by gcongr; exact Zeta23.CCM.UniversalSinc.fixedScale_pos.le)
  have hj : ‖sourceFamilyLaplace d z‖≤(2:ℝ)^(d+2)*B^(2*(d+2))*
      (8*Real.exp (Zeta23.CCM.UniversalSinc.fixedScale*L)*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) := by
    rw [sourceFamilyLaplace_box_formula,norm_mul,norm_pow]
    calc
      _ ≤ (2*B^2)^(d+2)*(8*Real.exp (Zeta23.CCM.UniversalSinc.fixedScale*L)*
          Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)) := by gcongr
      _ = _ := by rw [mul_pow,←pow_mul]
  have hζ0 := hζ (z+1/2) (by simp [z]; exact hσa) (by simpa [z] using ht)
  have hsum : ‖riemannZeta (z+1/2)‖+‖deriv riemannZeta (z+1/2)‖≤G*B^N := by
    apply hζ0.trans
    have hb : 1+|(z+1/2).im|≤B := by simp only [Complex.add_im, show (1/2:ℂ).im=0 by norm_num, add_zero, hzim]; dsimp [B]; linarith
    gcongr
  have hζv : ‖riemannZeta (z+1/2)‖≤G*B^N := le_trans (by linarith [norm_nonneg (deriv riemannZeta (z+1/2))]) hsum
  have hζd : ‖deriv riemannZeta (z+1/2)‖≤G*B^N := le_trans (by linarith [norm_nonneg (riemannZeta (z+1/2))]) hsum
  have hzhalf : z≠1/2 := by
    intro he
    have him := congrArg Complex.im he
    rw [hzim] at him
    norm_num at him
    rw [him] at ht
    norm_num at ht
  have he : ‖Complex.exp (z*(t:ℂ))‖≤Real.exp (L*|t|) := by
    rw [Complex.norm_exp]
    have hre : (z*(t:ℂ)).re=σ*t := by simp [z]
    rw [hre]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |σ*t| := le_abs_self _
      _ = |σ| *|t| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
  change ‖z^k*forwardKernelEntireContinuation d ell z*Complex.exp (z*(t:ℂ))‖≤_
  calc
    _ = ‖z‖^k*‖sourceFamilyLaplace d z‖*‖riemannZeta (z+1/2)‖^ell*
        ‖deriv riemannZeta (z+1/2)‖*‖Complex.exp (z*(t:ℂ))‖ := by
      rw [forwardKernelEntireContinuation_agrees d ell hd hzhalf,forwardKernelTransformGerm]
      simp only [norm_mul,norm_pow,norm_neg]
      ring_nf
    _ ≤ B^k*((2:ℝ)^(d+2)*B^(2*(d+2))*
        (8*Real.exp (Zeta23.CCM.UniversalSinc.fixedScale*L)*
          Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|)))*
        (G*B^N)^ell*(G*B^N)*Real.exp (L*|t|) := by gcongr
    _ = _ := by dsimp [A,B,L]; rw [mul_pow,←pow_mul,pow_succ,pow_add,pow_add]; ring_nf

theorem forwardEntire_fixed_strip_majorant (d ell k : ℕ) (hd : ell≤d) (a b t : ℝ) :
    ∃ φ : ℝ → ℝ, Integrable φ ∧
      (∀ (σ τ : ℝ), a≤σ → σ≤b →
        ‖(((σ:ℂ)+(τ:ℂ)*I)^k*forwardKernelEntireContinuation d ell ((σ:ℂ)+(τ:ℂ)*I))*
          Complex.exp (((σ:ℂ)+(τ:ℂ)*I)*(t:ℂ))‖ ≤ φ τ) ∧
      Tendsto φ atTop (𝓝 0) ∧ Tendsto φ atBot (𝓝 0) := by
  obtain ⟨A,hA,N,hlarge⟩ := forwardEntire_fixed_strip_large_height_bound d ell k hd a b t
  let L : ℝ := 1+|a|+|b|
  let c : ℝ := sourceVerticalDecayConstant
  have hc : 0<c := sourceVerticalDecayConstant_pos
  have hL : 1≤L := by dsimp [L]; linarith [abs_nonneg a,abs_nonneg b]
  let f : ℂ → ℂ := fun z => (z^k*forwardKernelEntireContinuation d ell z)*Complex.exp (z*(t:ℂ))
  have hEc : Continuous (forwardKernelEntireContinuation d ell) :=
    continuous_iff_continuousAt.mpr fun z =>
      (forwardKernelEntireContinuation_analyticAt d ell z).continuousAt
  have hfc : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) (L+2)).exists_bound_of_continuousOn hfc.continuousOn
  let K : ℝ := 1+|M|
  let D : ℝ := A+K*Real.exp (c*Real.sqrt 2)
  let φ : ℝ → ℝ := fun τ => D*(L+|τ|)^N*Real.exp (-c*Real.sqrt |τ|)
  have hK : 0<K := by dsimp [K]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hφi : Integrable φ := by
    have h := (shifted_sqrt_decay_integrable (show 0≤L by linarith) hc N).const_mul D
    simpa only [φ,mul_assoc] using h
  refine ⟨φ,hφi,fun σ τ hσa hσb => ?_,?_,?_⟩
  · have hσ : |σ|≤L := by
      rw [abs_le]
      constructor <;> dsimp [L] <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
    have hbase : 1≤L+|τ| := by linarith [abs_nonneg τ]
    by_cases ht : 2≤|τ|
    · apply (hlarge σ τ hσa hσb ht).trans
      change A*(L+|τ|)^N*Real.exp (-c*Real.sqrt |τ|) ≤ _
      dsimp [φ]
      have hAD : A≤D := by
        dsimp [D]
        linarith [mul_pos hK (Real.exp_pos (c*Real.sqrt 2))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAD (by positivity)) (by positivity)
    · have ht2 : |τ|≤2 := le_of_lt (lt_of_not_ge ht)
      let z : ℂ := (σ:ℂ)+(τ:ℂ)*I
      have hz : z∈Metric.closedBall (0:ℂ) (L+2) := by
        rw [Metric.mem_closedBall,dist_zero_right]
        have h := Complex.norm_le_abs_re_add_abs_im z
        have hre : z.re=σ := by simp [z]
        have him : z.im=τ := by simp [z]
        rw [hre,him] at h
        linarith
      have hMf : ‖f z‖≤K := (hM z hz).trans (by dsimp [K]; linarith [le_abs_self M])
      have hsqrt : Real.sqrt |τ|≤Real.sqrt 2 := Real.sqrt_le_sqrt ht2
      have hexp : 1≤Real.exp (c*Real.sqrt 2)*Real.exp (-c*Real.sqrt |τ|) := by
        rw [←Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by nlinarith)
      have hpow : 1≤(L+|τ|)^N := one_le_pow₀ hbase
      change ‖f z‖≤φ τ
      apply hMf.trans
      calc
        K ≤ K*(Real.exp (c*Real.sqrt 2)*Real.exp (-c*Real.sqrt |τ|)) :=
          le_mul_of_one_le_right hK.le hexp
        _ = (K*Real.exp (c*Real.sqrt 2))*Real.exp (-c*Real.sqrt |τ|) := by ring_nf
        _ ≤ D*(L+|τ|)^N*Real.exp (-c*Real.sqrt |τ|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          calc
            _ ≤ D := by dsimp [D]; linarith
            _ ≤ D*(L+|τ|)^N := le_mul_of_one_le_right hD.le hpow
        _ = φ τ := rfl
  · have h := ((shifted_sqrt_decay_tendsto (show 0≤L by linarith) hc N).1).const_mul D
    simpa only [mul_zero,mul_assoc,φ] using h
  · have h := ((shifted_sqrt_decay_tendsto (show 0≤L by linarith) hc N).2).const_mul D
    simpa only [mul_zero,mul_assoc,φ] using h

theorem forwardEntire_vertical_line_shift (d ell k : ℕ) (hd : ell≤d)
    {a b : ℝ} (hab : a≤b) (t : ℝ) :
    (∫ τ : ℝ, (((b:ℂ)+(τ:ℂ)*I)^k*forwardKernelEntireContinuation d ell ((b:ℂ)+(τ:ℂ)*I))*
      Complex.exp (((b:ℂ)+(τ:ℂ)*I)*(t:ℂ))) =
    (∫ τ : ℝ, (((a:ℂ)+(τ:ℂ)*I)^k*forwardKernelEntireContinuation d ell ((a:ℂ)+(τ:ℂ)*I))*
      Complex.exp (((a:ℂ)+(τ:ℂ)*I)*(t:ℂ))) := by
  obtain ⟨φ,hφ,hbound,htop,hbot⟩ := forwardEntire_fixed_strip_majorant d ell k hd a b t
  apply Zeta23.WeilEF.vertical_line_shift
    (f := fun z => (z^k*forwardKernelEntireContinuation d ell z)*Complex.exp (z*(t:ℂ)))
    hab _ hφ hbound htop hbot
  intro z _ _
  have hE := (forwardKernelEntireContinuation_analyticAt d ell z).differentiableAt
  fun_prop



theorem forwardEntire_vertical_integrable (d ell k : ℕ) (hd : ell≤d) (σ : ℝ) :
    Integrable (fun τ : ℝ => ((σ:ℂ)+I*(τ:ℂ))^k*
      forwardKernelEntireContinuation d ell ((σ:ℂ)+I*(τ:ℂ))) := by
  obtain ⟨φ,hφ,hbound,_htop,_hbot⟩ := forwardEntire_fixed_strip_majorant d ell k hd σ σ 0
  apply hφ.mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro τ
    have ha : AnalyticAt ℂ (fun z : ℂ => z^k*forwardKernelEntireContinuation d ell z)
        ((σ:ℂ)+I*(τ:ℂ)) := (analyticAt_id.pow k).mul
      (forwardKernelEntireContinuation_analyticAt d ell ((σ:ℂ)+I*(τ:ℂ)))
    exact ContinuousAt.comp_of_eq ha.continuousAt
      (by fun_prop : Continuous (fun u : ℝ => (σ:ℂ)+I*(u:ℂ))).continuousAt rfl
  · filter_upwards with τ
    simpa only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,mul_comm I] using
      hbound σ τ le_rfl le_rfl

theorem forwardKernel_iteratedDeriv_contour_formula (d ell k : ℕ) (hd : ell≤d)
    (n : ℕ) (t : ℝ) :
    Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t) =
      ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, Complex.exp ((forwardLeftContour n τ)*(t:ℂ))*forwardContourIntegrand d ell k n τ := by
  let f : ℝ → ℂ := fun u => Complex.ofReal (iteratedDeriv k (forwardKernel d ell) u)
  let F : ℂ → ℂ := fun z => z^k*forwardKernelEntireContinuation d ell z
  let a : ℝ := -(n:ℝ)-1/2
  have hf : Integrable (dampedHistory (3/2) f) := by
    unfold dampedHistory
    dsimp [f]
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,neg_mul] using
      forwardKernel_iteratedDeriv_integrable d ell k (z := (3/2:ℂ)) (by norm_num)
  have hLaplace (τ : ℝ) :
      (∫ u : ℝ, Complex.exp (-(((3/2:ℝ):ℂ)+I*(τ:ℂ))*(u:ℂ))*f u)=
        F (((3/2:ℝ):ℂ)+I*(τ:ℂ)) :=
    forwardKernel_iteratedDeriv_laplace_entire d ell k hd (by simp; norm_num)
  have hcont : ContinuousAt f t := by
    dsimp [f]
    exact Complex.continuous_ofReal.continuousAt.comp
      (contDiff_infty_iteratedDeriv (forwardKernel_contDiff d ell) k).continuous.continuousAt
  have hinv := bilateralLaplace_inverse hf (forwardEntire_vertical_integrable d ell k hd (3/2))
    hLaplace hcont
  have hshift := forwardEntire_vertical_line_shift d ell k hd
    (a := a) (b := (3/2:ℝ)) (by dsimp [a]; have h := Nat.cast_nonneg (α:=ℝ) n; linarith) t
  have hz (τ : ℝ) : (a:ℂ)+(τ:ℂ)*I=forwardLeftContour n τ := by
    dsimp [a,forwardLeftContour]
    push_cast
    ring
  have hzpole (τ : ℝ) : forwardLeftContour n τ≠1/2 := by
    intro he
    have h := congrArg Complex.re he
    simp [forwardLeftContour] at h
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  calc
    _ = ((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, (((3/2:ℂ)+(τ:ℂ)*I)^k*forwardKernelEntireContinuation d ell ((3/2:ℂ)+(τ:ℂ)*I))*
          Complex.exp (((3/2:ℂ)+(τ:ℂ)*I)*(t:ℂ)) := by
      simpa only [F,f,mul_comm I,mul_comm (Complex.exp _),Complex.ofReal_div,Complex.ofReal_ofNat] using hinv
    _ = ((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, (((a:ℂ)+(τ:ℂ)*I)^k*forwardKernelEntireContinuation d ell ((a:ℂ)+(τ:ℂ)*I))*
          Complex.exp (((a:ℂ)+(τ:ℂ)*I)*(t:ℂ)) := by
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
        congrArg (fun value : ℂ => ((1/(2*Real.pi):ℝ):ℂ)*value) hshift
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      rw [hz τ,forwardKernelEntireContinuation_agrees d ell hd (hzpole τ)]
      rw [forwardContourIntegrand_eq_germ]
      ring

theorem forwardKernel_iteratedDeriv_contour_norm (d ell k : ℕ) (hd : ell≤d)
    (n : ℕ) (t : ℝ) :
    |iteratedDeriv k (forwardKernel d ell) t| ≤
      (1/(2*Real.pi))*Real.exp ((-(n:ℝ)-1/2)*t)*
        (∫ τ : ℝ, ‖forwardContourIntegrand d ell k n τ‖) := by
  have he (τ : ℝ) :
      ‖Complex.exp ((forwardLeftContour n τ)*(t:ℂ))*forwardContourIntegrand d ell k n τ‖=
        Real.exp ((-(n:ℝ)-1/2)*t)*‖forwardContourIntegrand d ell k n τ‖ := by
    have hre : ((forwardLeftContour n τ)*(t:ℂ)).re = (-(n:ℝ)-1/2)*t := by
      norm_num [forwardLeftContour]; ring_nf; simp
    rw [norm_mul,Complex.norm_exp,hre]
  calc
    _ = ‖Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t)‖ := by simp
    _ = (1/(2*Real.pi))*‖∫ τ : ℝ,
        Complex.exp ((forwardLeftContour n τ)*(t:ℂ))*forwardContourIntegrand d ell k n τ‖ := by
      rw [forwardKernel_iteratedDeriv_contour_formula d ell k hd n t,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (by positivity : 0<(1/(2*Real.pi):ℝ))]
    _ ≤ (1/(2*Real.pi))*(∫ τ : ℝ,
        ‖Complex.exp ((forwardLeftContour n τ)*(t:ℂ))*forwardContourIntegrand d ell k n τ‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by simp_rw [he]; rw [integral_const_mul]; ring

theorem forwardKernel_double_exp_decay (d ell k : ℕ) (hd : ell≤d) :
    ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ t : ℝ, 0≤t →
      |iteratedDeriv k (forwardKernel d ell) t| ≤
        A*Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) := by
  obtain ⟨C,D,B,hC,hD,hbudget⟩ := forwardKernel_left_contour_budget d ell k
  let C2 : ℝ := (1/(2*Real.pi))*C
  apply integer_contour_saddle_decay (C := C2) (D := D) (B := B)
    (a := (ell:ℝ)+1) (by dsimp [C2]; positivity) hD (by positivity)
  intro n hn t ht
  have hp : (n:ℝ)^(2*((ell:ℝ)+1)*(n:ℝ)+(B:ℝ))=
      (n:ℝ)^(2*(ell+1)*n+B) := by
    rw [show 2*((ell:ℝ)+1)*(n:ℝ)+(B:ℝ)=((2*(ell+1)*n+B:ℕ):ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hp]
  have he : Real.exp ((-(n:ℝ)-1/2)*t)≤Real.exp (-(n:ℝ)*t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (1/(2*Real.pi))*Real.exp ((-(n:ℝ)-1/2)*t)*
        (∫ τ : ℝ, ‖forwardContourIntegrand d ell k n τ‖) :=
      forwardKernel_iteratedDeriv_contour_norm d ell k hd n t
    _ ≤ (1/(2*Real.pi))*Real.exp (-(n:ℝ)*t)*
        (C*Real.exp (D*(n:ℝ))*(n:ℝ)^(2*(ell+1)*n+B)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) (hbudget n hn).2
        (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)
    _ = _ := by
      dsimp [C2]
      have hexp : Real.exp (-(n:ℝ)*t)*Real.exp (D*(n:ℝ))=
          Real.exp (D*(n:ℝ)-(n:ℝ)*t) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        _ = (1/(2*Real.pi))*C*(Real.exp (-(n:ℝ)*t)*Real.exp (D*(n:ℝ)))*
            (n:ℝ)^(2*(ell+1)*n+B) := by ring
        _ = _ := by rw [hexp]

end Zeta23.OPICAFollowup
