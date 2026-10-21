import Zeta23.OPICAFollowup.NativeSourceTransforms
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Zeta23.OPICAFollowup.ZetaLeftLineBounds
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

end Zeta23.OPICAFollowup
