import Zeta23.OPICAFollowup.NativeSourceTransforms
import Zeta23.OPICA.NativeArithmeticAdapter
import Mathlib.Analysis.Convolution

/-! Concrete finite native generators. Their physical causal actions and
their multiplier identities are distinct obligations. -/

noncomputable section
open Set MeasureTheory Filter Finset Complex
open scoped Topology BigOperators Convolution
namespace Zeta23.OPICAFollowup
open Zeta23.CCM

/-- A regular causal component with explicit domain control. No transform,
rate, range, pole, or preservation conclusion is a field of this structure. -/
structure NativeRegularCausal where
  toFun : ℝ → ℂ
  measurable : Measurable toFun
  zero_before : ∀ t : ℝ, t < 0 → toFun t = 0
  amplitude : ℝ
  exponent : ℝ
  amplitude_nonneg : 0 ≤ amplitude
  exponent_nonneg : 0 ≤ exponent
  norm_le : ∀ t : ℝ, 0 ≤ t → ‖toFun t‖ ≤ amplitude*Real.exp (exponent*t)

instance : CoeFun NativeRegularCausal (fun _ => ℝ → ℂ) := ⟨NativeRegularCausal.toFun⟩

structure NativeCausalTerm where
  coefficient : ℂ
  order : ℕ
  regular : NativeRegularCausal

/-- The term `(c,k,f)` has the actual weak interpretation `c D^k f`, with
`f` zero to the left of zero. Endpoint delta derivatives are thereby kept. -/
abbrev NativeCausalState := List NativeCausalTerm

structure NativeCompactTest where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compact : HasCompactSupport toFun

instance : CoeFun NativeCompactTest (fun _ => ℝ → ℂ) := ⟨NativeCompactTest.toFun⟩

def NativeCausalState.applyTest (state : NativeCausalState) (test : NativeCompactTest) : ℂ :=
  (state.map fun term => term.coefficient*(-1:ℂ)^term.order*
    ∫ t : ℝ, term.regular t*iteratedDeriv term.order test.toFun t).sum

def NativeCausalState.laplace (state : NativeCausalState) (z : ℂ) : ℂ :=
  (state.map fun term => term.coefficient*z^term.order*
    ∫ t : ℝ, Complex.exp (-z*(t:ℂ))*term.regular t).sum

def NativeCausalState.sourceDifferentialAction (state : NativeCausalState) : NativeCausalState :=
  (state.map fun term => {term with order := term.order+2}) ++
    state.map (fun term => {term with coefficient := -(1/4:ℂ)*term.coefficient})

theorem NativeRegularCausal.norm_le_on_Icc (f : NativeRegularCausal) {R t : ℝ}
    (ht : t ∈ Icc (-R) R) : ‖f t‖ ≤ f.amplitude*Real.exp (f.exponent*R) := by
  by_cases ht0 : t<0
  · rw [f.zero_before t ht0,norm_zero]
    exact mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le
  · exact (f.norm_le t (le_of_not_gt ht0)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2 f.exponent_nonneg)) f.amplitude_nonneg)

theorem NativeRegularCausal.laplace_integrable (f : NativeRegularCausal) {z : ℂ}
    (hz : f.exponent<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*f t) := by
  have hdecay : -(z.re-f.exponent)<0 := by linarith
  have hint : IntegrableOn (fun t : ℝ =>
      f.amplitude*Real.exp (-(z.re-f.exponent)*t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi hdecay 0).const_mul f.amplitude)
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ici 0) ?_
    (fun t ht => by rw [f.zero_before t (lt_of_not_ge ht),mul_zero])
  apply hint.mono'
    (((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ)))).measurable.mul
      f.measurable).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  change ‖Complex.exp (-z*(t:ℂ))*f t‖ ≤ _
  rw [norm_mul,Complex.norm_exp]
  have hre : (-z*(t:ℂ)).re = -z.re*t := by simp
  rw [hre]
  calc
    _ ≤ Real.exp (-z.re*t)*(f.amplitude*Real.exp (f.exponent*t)) :=
      mul_le_mul_of_nonneg_left (f.norm_le t ht) (Real.exp_pos _).le
    _ = f.amplitude*(Real.exp (-z.re*t)*Real.exp (f.exponent*t)) := by ring
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

theorem NativeCompactTest.iteratedDeriv_support (test : NativeCompactTest) (k : ℕ) :
    tsupport (iteratedDeriv k test.toFun) ⊆ tsupport test.toFun := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem NativeCompactTest.iteratedDeriv_compact (test : NativeCompactTest) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k test.toFun) :=
  test.compact.of_isClosed_subset (isClosed_tsupport _) (test.iteratedDeriv_support k)

theorem NativeRegularCausal.testPairing_bound (f : NativeRegularCausal)
    (test : NativeCompactTest) (k : ℕ) (R B : ℝ)
    (hsupport : tsupport test.toFun ⊆ Icc (-R) R)
    (hB : ∀ t ∈ Icc (-R) R, ‖iteratedDeriv k test.toFun t‖ ≤ B) :
    ‖∫ t : ℝ, f t*iteratedDeriv k test.toFun t‖ ≤
      (f.amplitude*Real.exp (f.exponent*R)*B)*volume.real (Icc (-R) R) := by
  have hzero : ∀ t, t ∉ Icc (-R) R → f t*iteratedDeriv k test.toFun t=0 := by
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => ht (hsupport (test.iteratedDeriv_support k h))),mul_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro t ht
  rw [norm_mul]
  exact mul_le_mul (f.norm_le_on_Icc ht) (hB t ht) (norm_nonneg _)
    (mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le)

theorem NativeRegularCausal.testPairing_integrable (f : NativeRegularCausal)
    (test : NativeCompactTest) (k : ℕ) :
    Integrable (fun t : ℝ => f t*iteratedDeriv k test.toFun t) := by
  obtain ⟨R,hR,hbound⟩ := test.compact.isBounded.exists_pos_norm_le
  have hsupp : tsupport test.toFun ⊆ Icc (-R) R := by
    intro t ht
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound t ht)
  have hc := test.smooth.continuous_iteratedDeriv k
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  obtain ⟨B,hB⟩ := (test.iteratedDeriv_compact k).exists_bound_of_continuous hc
  have hzero : ∀ t, t ∉ Icc (-R) R → f t*iteratedDeriv k test.toFun t=0 := by
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => ht (hsupp (test.iteratedDeriv_support k h))),mul_zero]
  have hint : IntegrableOn (fun _ : ℝ => f.amplitude*Real.exp (f.exponent*R)*B)
      (Icc (-R) R) := integrableOn_const isCompact_Icc.measure_ne_top
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Icc (-R) R) ?_ hzero
  apply hint.mono' (f.measurable.mul hc.measurable).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ‖f t*iteratedDeriv k test.toFun t‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (f.norm_le_on_Icc ht) (hB t) (norm_nonneg _)
    (mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le)

def NativeCausalState.testBound (state : NativeCausalState) (R : ℝ) (B : ℕ → ℝ) : ℝ :=
  (state.map fun term => ‖term.coefficient‖*
    (term.regular.amplitude*Real.exp (term.regular.exponent*R)*B term.order)*
      volume.real (Icc (-R) R)).sum

/-- A finite fixed-support test seminorm bound for the actual weak action.
Thus the state is controlled as a local distribution, rather than an
arbitrary function on tests. -/
theorem NativeCausalState.applyTest_bound (state : NativeCausalState)
    (test : NativeCompactTest) (R : ℝ) (B : ℕ → ℝ)
    (hsupport : tsupport test.toFun ⊆ Icc (-R) R)
    (hB : ∀ term ∈ state, ∀ t ∈ Icc (-R) R, ‖iteratedDeriv term.order test.toFun t‖ ≤ B term.order) :
    ‖state.applyTest test‖ ≤ state.testBound R B := by
  induction state with
  | nil => simp [applyTest,testBound]
  | cons term state ih =>
    have hb := term.regular.testPairing_bound test term.order R (B term.order) hsupport
      (hB term (by simp))
    have hhead : ‖term.coefficient*(-1:ℂ)^term.order*
        ∫ t : ℝ, term.regular t*iteratedDeriv term.order test.toFun t‖ ≤
        ‖term.coefficient‖*(term.regular.amplitude*Real.exp (term.regular.exponent*R)*B term.order)*
          volume.real (Icc (-R) R) := by
      simpa only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,one_mul,mul_assoc]
        using mul_le_mul_of_nonneg_left hb (norm_nonneg term.coefficient)
    have htail := ih (fun other ho => hB other (by simp [ho]))
    change ‖term.coefficient*(-1:ℂ)^term.order*
        (∫ t : ℝ, term.regular t*iteratedDeriv term.order test.toFun t)+
          NativeCausalState.applyTest state test‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add hhead htail)

/-- An actual compact causal history, rather than an analytic function
supplied without a physical source. -/
structure NativeCompactHistory where
  test : NativeCompactTest
  zero_before : ∀ t : ℝ, t<0 → test t=0

def NativeCompactHistory.toRegularCausal (history : NativeCompactHistory) : NativeRegularCausal :=
  let hb := history.test.compact.exists_bound_of_continuous history.test.smooth.continuous
  { toFun := history.test.toFun
    measurable := history.test.smooth.continuous.measurable
    zero_before := history.zero_before
    amplitude := max 0 (Classical.choose hb)
    exponent := 0
    amplitude_nonneg := le_max_left _ _
    exponent_nonneg := le_rfl
    norm_le := by
      intro t ht
      simpa only [zero_mul,Real.exp_zero,mul_one] using
        (Classical.choose_spec hb t).trans (le_max_right 0 _) }

def NativeCompactHistory.toCausalState (history : NativeCompactHistory) : NativeCausalState :=
  [{coefficient := 1,order := 0,regular := history.toRegularCausal}]

def NativeCompactHistory.laplace (history : NativeCompactHistory) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z*(t:ℂ))*history.test t

theorem NativeCompactHistory.toCausalState_laplace (history : NativeCompactHistory) (z : ℂ) :
    history.toCausalState.laplace z=history.laplace z := by
  simp [toCausalState,NativeCausalState.laplace,laplace,toRegularCausal]

theorem NativeCompactHistory.laplace_integrable (history : NativeCompactHistory) (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*history.test t) :=
  ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ)))).mul
    history.test.smooth.continuous).integrable_of_hasCompactSupport history.test.compact.mul_left

theorem NativeCompactHistory.laplace_analyticAt (history : NativeCompactHistory) (z : ℂ) :
    AnalyticAt ℂ history.laplace z := by
  have heq : history.laplace = fun w : ℂ => Zeta23.paperFT history.test.toFun (I*w) := by
    funext w
    unfold laplace Zeta23.paperFT
    apply integral_congr_ae
    filter_upwards with t
    have he : I*(I*w)*(t:ℂ) = -w*(t:ℂ) := by
      calc
        _ = (I*I)*w*(t:ℂ) := by ring
        _ = _ := by rw [I_mul_I]; ring
    rw [he,mul_comm]
  rw [heq]
  exact ((Zeta23.WeilEF.differentiable_paperFT history.test.smooth.continuous
    history.test.compact).analyticAt (I*z)).comp (by fun_prop)

def NativeCompactTest.add (a b : NativeCompactTest) : NativeCompactTest :=
  ⟨fun t => a t+b t,a.smooth.add b.smooth,a.compact.add b.compact⟩

def NativeCompactTest.constMul (c : ℂ) (a : NativeCompactTest) : NativeCompactTest :=
  ⟨fun t => c*a t,contDiff_const.mul a.smooth,a.compact.mul_left⟩

theorem NativeRegularCausal.testPairing_add (f : NativeRegularCausal)
    (a b : NativeCompactTest) (k : ℕ) :
    (∫ t : ℝ, f t*iteratedDeriv k (a.add b).toFun t) =
      (∫ t : ℝ, f t*iteratedDeriv k a.toFun t)+
        ∫ t : ℝ, f t*iteratedDeriv k b.toFun t := by
  have heq : (fun t : ℝ => f t*iteratedDeriv k (a.add b).toFun t) =
      fun t => f t*iteratedDeriv k a.toFun t+f t*iteratedDeriv k b.toFun t := by
    funext t
    rw [show (a.add b).toFun = a.toFun+b.toFun from rfl,
      iteratedDeriv_add
        ((a.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt)
        ((b.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt)]
    ring
  rw [heq,integral_add (f.testPairing_integrable a k) (f.testPairing_integrable b k)]

theorem NativeRegularCausal.testPairing_constMul (f : NativeRegularCausal)
    (c : ℂ) (a : NativeCompactTest) (k : ℕ) :
    (∫ t : ℝ, f t*iteratedDeriv k (a.constMul c).toFun t) =
      c*∫ t : ℝ, f t*iteratedDeriv k a.toFun t := by
  have heq : (fun t : ℝ => f t*iteratedDeriv k (a.constMul c).toFun t) =
      fun t => c*(f t*iteratedDeriv k a.toFun t) := by
    funext t
    change f t*iteratedDeriv k (fun u : ℝ => c*a u) t = _
    rw [iteratedDeriv_const_mul_field]
    ring
  rw [heq,integral_const_mul]

theorem NativeCausalState.applyTest_add (state : NativeCausalState)
    (a b : NativeCompactTest) :
    state.applyTest (a.add b)=state.applyTest a+state.applyTest b := by
  induction state with
  | nil => simp [applyTest]
  | cons term state ih =>
    simp only [applyTest,List.map_cons,List.sum_cons] at ih ⊢
    rw [term.regular.testPairing_add a b term.order,ih]
    ring

theorem NativeCausalState.applyTest_constMul (state : NativeCausalState)
    (c : ℂ) (a : NativeCompactTest) :
    state.applyTest (a.constMul c)=c*state.applyTest a := by
  induction state with
  | nil => simp [applyTest]
  | cons term state ih =>
    simp only [applyTest,List.map_cons,List.sum_cons] at ih ⊢
    rw [term.regular.testPairing_constMul c a term.order,ih]
    ring

def sourceFamilyAmplitude (d : ℕ) : ℝ :=
  max 0 (Classical.choose ((sourceFamily_hasCompactSupport d).exists_bound_of_continuous
    (sourceFamily_contDiff d).continuous))

theorem sourceFamilyAmplitude_nonneg (d : ℕ) : 0≤sourceFamilyAmplitude d := le_max_left _ _

theorem sourceFamily_abs_le_amplitude (d : ℕ) (t : ℝ) :
    |sourceOrderFamily d t| ≤ sourceFamilyAmplitude d := by
  have h := Classical.choose_spec ((sourceFamily_hasCompactSupport d).exists_bound_of_continuous
    (sourceFamily_contDiff d).continuous) t
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_right 0 _)

theorem compactSource_history_exponential_bound (d : ℕ) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, |c n|≤(n:ℝ)) {t : ℝ} (ht : 0≤t) :
    |∑ n ∈ range (nativeHistoryCutoff UniversalSinc.fixedScale t+1),
      c n*sourceOrderFamily d (t-Real.log n)| ≤
        2*Real.exp (2*UniversalSinc.fixedScale)*sourceFamilyAmplitude d*Real.exp (2*t) := by
  let E := Real.exp (t+UniversalSinc.fixedScale)
  let N := nativeHistoryCutoff UniversalSinc.fixedScale t+1
  have hE : 0<E := Real.exp_pos _
  have hE1 : 1≤E := Real.one_le_exp_iff.mpr (by linarith [UniversalSinc.fixedScale_pos])
  have hfloor : (nativeHistoryCutoff UniversalSinc.fixedScale t:ℝ) ≤ E :=
    Nat.floor_le hE.le
  have hN : (N:ℝ) ≤ 2*E := by dsimp [N]; push_cast; linarith
  have hM := sourceFamilyAmplitude_nonneg d
  calc
    _ ≤ ∑ n ∈ range N, |c n*sourceOrderFamily d (t-Real.log n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, E*sourceFamilyAmplitude d := by
      apply sum_le_sum
      intro n hn
      have hnle : n≤nativeHistoryCutoff UniversalSinc.fixedScale t := Nat.lt_succ_iff.mp (mem_range.mp hn)
      rw [abs_mul]
      exact mul_le_mul ((hc n).trans ((Nat.cast_le.mpr hnle).trans hfloor))
        (sourceFamily_abs_le_amplitude d _) (abs_nonneg _) hE.le
    _ = (N:ℝ)*(E*sourceFamilyAmplitude d) := by simp [nsmul_eq_mul]
    _ ≤ (2*E)*(E*sourceFamilyAmplitude d) := mul_le_mul_of_nonneg_right hN (mul_nonneg hE.le hM)
    _ = _ := by
      have heq : E*E=Real.exp (2*UniversalSinc.fixedScale)*Real.exp (2*t) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      calc
        _ = 2*(E*E)*sourceFamilyAmplitude d := by ring
        _ = _ := by rw [heq]; ring

theorem nativePrimeCoefficient_abs_le_nat (n : ℕ) : |nativePrimeCoefficient n|≤(n:ℝ) := by
  by_cases hn : n=0
  · subst n; simp [nativePrimeCoefficient]
  have hnpos : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : 1≤Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hlog : Real.log (n:ℝ)≤(n:ℝ) := (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  rw [nativePrimeCoefficient,abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  exact (div_le_self ArithmeticFunction.vonMangoldt_nonneg hsqrt).trans
    (ArithmeticFunction.vonMangoldt_le_log.trans hlog)

def primeFamilyRegularCausal (d : ℕ) : NativeRegularCausal where
  toFun t := (primeFieldFamily d t:ℂ)
  measurable := (Complex.continuous_ofReal.comp (primeFieldFamily_contDiff d).continuous).measurable
  zero_before := by
    intro t ht
    rw [primeFieldFamily_zero_before d (by linarith [nativeCausalGap_pos]),Complex.ofReal_zero]
  amplitude := 2*Real.exp (2*UniversalSinc.fixedScale)*sourceFamilyAmplitude d
  exponent := 2
  amplitude_nonneg := mul_nonneg (by positivity) (sourceFamilyAmplitude_nonneg d)
  exponent_nonneg := by norm_num
  norm_le := by
    intro t ht
    have h := compactSource_history_exponential_bound d nativePrimeCoefficient
      nativePrimeCoefficient_abs_le_nat ht
    rw [←primeFieldFamily_history d (le_refl t)] at h
    simpa only [Complex.norm_real,Real.norm_eq_abs] using h

def primeFamilyCausalState (d : ℕ) : NativeCausalState :=
  [{coefficient := 1,order := 0,regular := primeFamilyRegularCausal d}]

def NativeRegularCausal.delay (f : NativeRegularCausal) (tau : ℝ) (htau : 0≤tau) :
    NativeRegularCausal where
  toFun t := f (t-tau)
  measurable := f.measurable.comp (continuous_id.sub continuous_const).measurable
  zero_before := fun t ht => f.zero_before _ (by linarith)
  amplitude := f.amplitude
  exponent := f.exponent
  amplitude_nonneg := f.amplitude_nonneg
  exponent_nonneg := f.exponent_nonneg
  norm_le := by
    intro t ht
    by_cases hshift : t-tau<0
    · rw [f.zero_before _ hshift,norm_zero]
      exact mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le
    · exact (f.norm_le _ (le_of_not_gt hshift)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (by linarith) f.exponent_nonneg)) f.amplitude_nonneg)

theorem NativeRegularCausal.delay_laplace (f : NativeRegularCausal) (tau : ℝ)
    (htau : 0≤tau) (z : ℂ) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(f.delay tau htau) t) =
      Complex.exp (-(tau:ℂ)*z)*(∫ t : ℝ, Complex.exp (-z*(t:ℂ))*f t) := by
  have hfactor (t : ℝ) : Complex.exp (-z*(t:ℂ))*(f.delay tau htau) t =
      Complex.exp (-(tau:ℂ)*z)*(Complex.exp (-z*((t-tau:ℝ):ℂ))*f (t-tau)) := by
    change Complex.exp (-z*(t:ℂ))*f (t-tau)=_
    rw [←mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hfactor]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun t : ℝ => Complex.exp (-z*(t:ℂ))*f t) tau

def NativeCausalState.delayAction (state : NativeCausalState) (tau : ℝ) (htau : 0≤tau) :
    NativeCausalState := state.map fun term => {term with regular := term.regular.delay tau htau}

def NativeCausalState.addAction (state other : NativeCausalState) : NativeCausalState := state++other

def NativeCausalState.scaleAction (c : ℂ) (state : NativeCausalState) : NativeCausalState :=
  state.map fun term => {term with coefficient := c*term.coefficient}

def NativeCausalState.derivativeAction (state : NativeCausalState) (k : ℕ) : NativeCausalState :=
  state.map fun term => {term with order := term.order+k}

theorem NativeCausalState.laplace_addAction (state other : NativeCausalState) (z : ℂ) :
    (state.addAction other).laplace z=state.laplace z+other.laplace z := by
  simp [addAction,laplace,List.map_append,List.sum_append]

theorem NativeCausalState.laplace_scaleAction (c : ℂ) (state : NativeCausalState) (z : ℂ) :
    (scaleAction c state).laplace z=c*state.laplace z := by
  induction state with
  | nil => simp [scaleAction,laplace]
  | cons term state ih =>
    simp only [scaleAction,laplace,List.map_map,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem NativeCausalState.laplace_derivativeAction (state : NativeCausalState) (k : ℕ) (z : ℂ) :
    (state.derivativeAction k).laplace z=z^k*state.laplace z := by
  induction state with
  | nil => simp [derivativeAction,laplace]
  | cons term state ih =>
    simp only [derivativeAction,laplace,List.map_map,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih,pow_add]
    ring

theorem NativeCausalState.laplace_delayAction (state : NativeCausalState) (tau : ℝ)
    (htau : 0≤tau) (z : ℂ) :
    (state.delayAction tau htau).laplace z=Complex.exp (-(tau:ℂ)*z)*state.laplace z := by
  induction state with
  | nil => simp [delayAction,laplace]
  | cons term state ih =>
    simp only [delayAction,laplace,List.map_map,List.map_cons,List.sum_cons] at ih ⊢
    rw [term.regular.delay_laplace tau htau z,ih]
    ring

theorem NativeCausalState.laplace_sourceDifferentialAction (state : NativeCausalState) (z : ℂ) :
    state.sourceDifferentialAction.laplace z=(z^2-1/4)*state.laplace z := by
  change ((state.derivativeAction 2).addAction (scaleAction (-(1/4:ℂ)) state)).laplace z=_
  rw [laplace_addAction,laplace_derivativeAction,laplace_scaleAction]
  ring

inductive NativeGenerator where
  | sourceDerivative (d : ℕ)
  | delay (tau : ℝ) (nonneg : 0 ≤ tau)
  | finiteEuler (Q : ℕ) (positive : 0 < Q)
  | inverseFiniteEuler (Q : ℕ) (positive : 0 < Q)
  | rational (a b : ℝ) (apos : 0 < a) (bpos : 0 < b)
  | inverseRational (a b : ℝ) (apos : 0 < a) (bpos : 0 < b)
  | residualPower (Y r : ℕ)
  | completion

def finiteEulerMultiplier (Q : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ Q.primeFactors, (1-Complex.exp (-(z+1/2)*(Real.log p:ℂ)))

def truncatedMoebiusMultiplier (Y : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range (Y+1), (ArithmeticFunction.moebius n:ℂ)*nativeIntegerLaplaceCoefficient z n

def NativeGenerator.multiplier : NativeGenerator → ℂ → ℂ
  | .sourceDerivative d, z => (z^2-1/4)^d
  | .delay tau _, z => Complex.exp (-(tau:ℂ)*z)
  | .finiteEuler Q _, z => finiteEulerMultiplier Q z
  | .inverseFiniteEuler Q _, z => (finiteEulerMultiplier Q z)⁻¹
  | .rational a b _ _, z => (z+(a:ℂ))/(z+(b:ℂ))
  | .inverseRational a b _ _, z => (z+(b:ℂ))/(z+(a:ℂ))
  | .residualPower Y r, z => (1-riemannZeta (z+1/2)*truncatedMoebiusMultiplier Y z)^r
  | .completion, z => nativeCompletionRationalMultiplier z*riemannZeta (z+1/2)

def NativeGenerator.unitMultiplier : NativeGenerator → ℂ → ℂ
  | .completion, z => nativeCompletionRationalMultiplier z
  | g, z => g.multiplier z

def NativeGenerator.completionCount : NativeGenerator → ℕ
  | .completion => 1
  | _ => 0

theorem NativeGenerator.multiplier_eq_unit_zeta (g : NativeGenerator) (z : ℂ) :
    g.multiplier z = g.unitMultiplier z*riemannZeta (z+1/2)^g.completionCount := by
  cases g <;> simp [multiplier,unitMultiplier,completionCount]

theorem shiftedZeta_analyticAt_right_zero (rho : zetaZeroConfig.carrier) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (z+1/2)) ((rho:ℂ)-1/2) := by
  have hz : AnalyticAt ℂ riemannZeta ((rho:ℂ)-1/2+1/2) := by
    simpa only [sub_add_cancel] using
      riemannZeta_analyticOnNhd_compl_one _ rho.property.not_trivial.2
  exact hz.comp (f := fun z : ℂ => z+1/2) (x := (rho:ℂ)-1/2) (by fun_prop)

theorem finiteEulerMultiplier_analyticAt (Q : ℕ) (z : ℂ) :
    AnalyticAt ℂ (finiteEulerMultiplier Q) z := by
  unfold finiteEulerMultiplier
  fun_prop

theorem truncatedMoebiusMultiplier_analyticAt (Y : ℕ) (z : ℂ) :
    AnalyticAt ℂ (truncatedMoebiusMultiplier Y) z := by
  unfold truncatedMoebiusMultiplier nativeIntegerLaplaceCoefficient
  fun_prop

theorem finiteEulerMultiplier_ne_zero_at_right_zero (Q : ℕ)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    finiteEulerMultiplier Q ((rho:ℂ)-1/2) ≠ 0 := by
  unfold finiteEulerMultiplier
  apply prod_ne_zero_iff.mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hnorm : ‖Complex.exp (-(rho:ℂ)*(Real.log p:ℂ))‖ < 1 := by
    rw [Complex.norm_exp,Real.exp_lt_one_iff]
    simp only [neg_mul,neg_re,mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    nlinarith
  rw [sub_add_cancel]
  intro hz
  have he := (sub_eq_zero.mp hz).symm
  rw [he,norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem right_zero_add_positive_ne_zero (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) {a : ℝ} (ha : 0<a) :
    (rho:ℂ)-1/2+(a:ℂ) ≠ 0 := by
  intro hz
  have he := congrArg Complex.re hz
  norm_num at he
  linarith

theorem NativeGenerator.unit_ne_zero (g : NativeGenerator)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    g.unitMultiplier ((rho:ℂ)-1/2) ≠ 0 := by
  cases g with
  | sourceDerivative d => exact pow_ne_zero d (right_zero_source_factor_ne_zero rho hright)
  | delay tau ht => exact Complex.exp_ne_zero _
  | finiteEuler Q hQ => exact finiteEulerMultiplier_ne_zero_at_right_zero Q rho hright
  | inverseFiniteEuler Q hQ => exact inv_ne_zero (finiteEulerMultiplier_ne_zero_at_right_zero Q rho hright)
  | rational a b ha hb =>
    exact div_ne_zero
      (right_zero_add_positive_ne_zero rho hright ha) (right_zero_add_positive_ne_zero rho hright hb)
  | inverseRational a b ha hb =>
    exact div_ne_zero
      (right_zero_add_positive_ne_zero rho hright hb) (right_zero_add_positive_ne_zero rho hright ha)
  | residualPower Y r => simp [unitMultiplier,multiplier,sub_add_cancel,rho.property.1]
  | completion => exact Zeta23.ExceptionalZero.nativeCompletionRationalMultiplier_at_zero_ne_zero rho

theorem NativeGenerator.unit_analytic (g : NativeGenerator)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ g.unitMultiplier ((rho:ℂ)-1/2) := by
  cases g with
  | sourceDerivative d => change AnalyticAt ℂ (fun z : ℂ => (z^2-1/4)^d) _; fun_prop
  | delay tau ht => change AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(tau:ℂ)*z)) _; fun_prop
  | finiteEuler Q hQ => exact finiteEulerMultiplier_analyticAt Q _
  | inverseFiniteEuler Q hQ =>
    exact (finiteEulerMultiplier_analyticAt Q _).inv
      (finiteEulerMultiplier_ne_zero_at_right_zero Q rho hright)
  | rational a b ha hb =>
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z+(a:ℂ)) _).div
      (by fun_prop) (right_zero_add_positive_ne_zero rho hright hb)
  | inverseRational a b ha hb =>
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z+(b:ℂ)) _).div
      (by fun_prop) (right_zero_add_positive_ne_zero rho hright ha)
  | residualPower Y r =>
    exact
      (analyticAt_const.sub ((shiftedZeta_analyticAt_right_zero rho).mul
        (truncatedMoebiusMultiplier_analyticAt Y _))).pow r
  | completion => exact Zeta23.ExceptionalZero.nativeCompletionRationalMultiplier_at_zero_analyticAt rho

theorem NativeGenerator.residual_value_one (Y r : ℕ) (rho : zetaZeroConfig.carrier) :
    (NativeGenerator.residualPower Y r).multiplier ((rho:ℂ)-1/2) = 1 := by
  simp [multiplier,sub_add_cancel,rho.property.1]

theorem nativeGenerator_unit_or_completion (g : NativeGenerator)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (∀ z : ℂ, g.multiplier z = g.unitMultiplier z*riemannZeta (z+1/2)^g.completionCount) ∧
    AnalyticAt ℂ g.unitMultiplier ((rho:ℂ)-1/2) ∧
    g.unitMultiplier ((rho:ℂ)-1/2) ≠ 0 ∧
    (∀ Y r : ℕ, (NativeGenerator.residualPower Y r).multiplier ((rho:ℂ)-1/2) = 1) :=
  ⟨g.multiplier_eq_unit_zeta,g.unit_analytic rho hright,g.unit_ne_zero rho hright,
    fun Y r => NativeGenerator.residual_value_one Y r rho⟩



structure NativeCausalL1Kernel where
  toFun : ℝ → ℂ
  measurable : Measurable toFun
  integrable : Integrable toFun
  zero_before : ∀ t : ℝ, t<0 → toFun t=0

instance : CoeFun NativeCausalL1Kernel (fun _ => ℝ → ℂ) := ⟨NativeCausalL1Kernel.toFun⟩

def NativeCausalL1Kernel.laplace (k : NativeCausalL1Kernel) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z*(t:ℂ))*k t

theorem NativeCausalL1Kernel.damped_integrable (k : NativeCausalL1Kernel) {z : ℂ}
    (hz : 0≤z.re) : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*k t) := by
  apply k.integrable.norm.mono'
    (((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ)))).measurable.mul
      k.measurable).aestronglyMeasurable)
  filter_upwards with t
  change ‖Complex.exp (-z*(t:ℂ))*k t‖ ≤ ‖k t‖
  by_cases ht : t<0
  · rw [k.zero_before t ht,mul_zero,norm_zero]
  · rw [norm_mul,Complex.norm_exp]
    have he : (-z*(t:ℂ)).re = -z.re*t := by simp
    rw [he]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) (le_of_not_gt ht)))

theorem NativeCausalL1Kernel.convolve_integrand_bound
    (k : NativeCausalL1Kernel) (f : NativeRegularCausal) (t s : ℝ) (_ht : 0≤t) :
    ‖k s*f (t-s)‖ ≤ ‖k s‖*(f.amplitude*Real.exp (f.exponent*t)) := by
  by_cases hs : s<0
  · simp only [k.zero_before s hs,zero_mul,norm_zero]
    exact le_rfl
  by_cases hts : t-s<0
  · rw [f.zero_before (t-s) hts,mul_zero,norm_zero]
    exact mul_nonneg (norm_nonneg _) (mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (f.norm_le (t-s) (le_of_not_gt hts)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_self t (le_of_not_gt hs)) f.exponent_nonneg))
      f.amplitude_nonneg)

theorem NativeCausalL1Kernel.convolve_integrable (k : NativeCausalL1Kernel)
    (f : NativeRegularCausal) (t : ℝ) : Integrable (fun s : ℝ => k s*f (t-s)) := by
  have hm : Measurable (fun s : ℝ => k s*f (t-s)) :=
    k.measurable.mul (f.measurable.comp (by fun_prop))
  by_cases ht : t<0
  · have heq : (fun s : ℝ => k s*f (t-s))=0 := by
      funext s
      by_cases hs : s<0
      · rw [k.zero_before s hs,zero_mul]; rfl
      · rw [f.zero_before (t-s) (by linarith),mul_zero]; rfl
    rw [heq]
    exact integrable_zero _ _ _
  · apply (k.integrable.norm.mul_const (f.amplitude*Real.exp (f.exponent*t))).mono'
      hm.aestronglyMeasurable
    exact Eventually.of_forall fun s => k.convolve_integrand_bound f t s (le_of_not_gt ht)

def NativeCausalL1Kernel.convolve (k : NativeCausalL1Kernel) (f : NativeRegularCausal) :
    NativeRegularCausal where
  toFun := fun t => ∫ s : ℝ, k s*f (t-s)
  measurable := by
    have hm : Measurable (fun p : ℝ×ℝ => k p.2*f (p.1-p.2)) :=
      (k.measurable.comp measurable_snd).mul
        (f.measurable.comp (measurable_fst.sub measurable_snd))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  zero_before := by
    intro t ht
    apply integral_eq_zero_of_ae
    filter_upwards with s
    by_cases hs : s<0
    · simp only [k.zero_before s hs,zero_mul,Pi.zero_apply]
    · simp only [f.zero_before (t-s) (by linarith),mul_zero,Pi.zero_apply]
  amplitude := (∫ s : ℝ, ‖k s‖)*f.amplitude
  exponent := f.exponent
  amplitude_nonneg := mul_nonneg (integral_nonneg fun s => norm_nonneg (k s)) f.amplitude_nonneg
  exponent_nonneg := f.exponent_nonneg
  norm_le := by
    intro t ht
    calc
      _ ≤ ∫ s : ℝ, ‖k s*f (t-s)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ, ‖k s‖*(f.amplitude*Real.exp (f.exponent*t)) :=
        integral_mono (k.convolve_integrable f t).norm
          (k.integrable.norm.mul_const _) (fun s => k.convolve_integrand_bound f t s ht)
      _ = _ := by rw [integral_mul_const]; ring

theorem NativeCausalL1Kernel.convolve_laplace (k : NativeCausalL1Kernel)
    (f : NativeRegularCausal) {z : ℂ} (hz : f.exponent<z.re) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*k.convolve f t) =
      k.laplace z*(∫ t : ℝ, Complex.exp (-z*(t:ℂ))*f t) := by
  let dk : ℝ → ℂ := fun t => Complex.exp (-z*(t:ℂ))*k t
  let df : ℝ → ℂ := fun t => Complex.exp (-z*(t:ℂ))*f t
  have hk : Integrable dk := k.damped_integrable (le_trans f.exponent_nonneg hz.le)
  have hf : Integrable df := f.laplace_integrable hz
  have heq : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*k.convolve f t) =
      dk ⋆[ContinuousLinearMap.mul ℂ ℂ] df := by
    funext t
    rw [convolution_mul]
    change Complex.exp (-z*(t:ℂ))*(∫ s : ℝ, k s*f (t-s))=_
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    dsimp [dk,df]
    have hexp : Complex.exp (-z*(t:ℂ)) =
        Complex.exp (-z*(s:ℂ))*Complex.exp (-z*((t-s:ℝ):ℂ)) := by
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [heq,integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hk hf]
  rfl

def NativeCausalState.convolveAction (state : NativeCausalState) (k : NativeCausalL1Kernel) :
    NativeCausalState := state.map fun term => {term with regular := k.convolve term.regular}

theorem NativeCausalState.laplace_convolveAction (state : NativeCausalState)
    (k : NativeCausalL1Kernel) {z : ℂ}
    (hz : ∀ term ∈ state, term.regular.exponent<z.re) :
    (state.convolveAction k).laplace z=k.laplace z*state.laplace z := by
  induction state with
  | nil => simp [convolveAction,laplace]
  | cons term state ih =>
    have hterm := k.convolve_laplace term.regular (hz term (by simp))
    have htail := ih (fun other ho => hz other (by simp [ho]))
    simp only [convolveAction,List.map_cons,laplace,List.sum_cons] at *
    rw [hterm,htail]
    ring

def NativeCausalL1Kernel.exponential (b : ℝ) (hb : 0<b) : NativeCausalL1Kernel where
  toFun := fun t => if 0≤t then Complex.exp (-(b:ℂ)*(t:ℂ)) else 0
  measurable := by
    exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  integrable := by
    have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(b:ℂ)*(t:ℂ))) (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
        (integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hb) 0)
    exact hint.integrable_indicator measurableSet_Ici
  zero_before := by intro t ht; simp only [not_le.mpr ht,ite_false]

theorem NativeCausalL1Kernel.exponential_laplace (b : ℝ) (hb : 0<b) {z : ℂ}
    (hz : 0≤z.re) : (NativeCausalL1Kernel.exponential b hb).laplace z=1/(z+(b:ℂ)) := by
  have hsum : (-(z+(b:ℂ))).re<0 := by simp; linarith
  unfold laplace exponential
  change (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(if 0≤t then Complex.exp (-(b:ℂ)*(t:ℂ)) else 0))=_
  have heq : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(if 0≤t then Complex.exp (-(b:ℂ)*(t:ℂ)) else 0))=
      (Set.Ici 0).indicator (fun t : ℝ => Complex.exp (-(z+(b:ℂ))*(t:ℂ))) := by
    funext t
    by_cases ht : 0≤t
    · rw [indicator_of_mem (show t∈Ici (0:ℝ) from ht)]
      simp only [ht,ite_true]
      rw [←Complex.exp_add]
      congr 1
      ring
    · rw [indicator_of_notMem (show t∉Ici (0:ℝ) from ht)]
      simp only [ht,ite_false,mul_zero]
  rw [heq,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi hsum]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div,one_div,inv_neg,neg_neg]

def NativeCausalState.rationalAction (state : NativeCausalState) (a b : ℝ) (hb : 0<b) :
    NativeCausalState := state.addAction
      ((state.convolveAction (NativeCausalL1Kernel.exponential b hb)).scaleAction ((a-b:ℝ):ℂ))

theorem NativeCausalState.laplace_rationalAction (state : NativeCausalState)
    (a b : ℝ) (hb : 0<b) {z : ℂ} (hz0 : 0≤z.re)
    (hz : ∀ term ∈ state, term.regular.exponent<z.re) :
    (state.rationalAction a b hb).laplace z=
      ((z+(a:ℂ))/(z+(b:ℂ)))*state.laplace z := by
  have hbz : z+(b:ℂ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [add_re,ofReal_re,zero_re] at hre
    linarith
  rw [rationalAction,laplace_addAction,laplace_scaleAction,
    laplace_convolveAction state _ hz,NativeCausalL1Kernel.exponential_laplace b hb hz0]
  push_cast
  field_simp
  ring

def nativeCompletionCausalKernel : NativeCausalL1Kernel where
  toFun := fun t => (CCM.nativePositiveCompletion t:ℂ)
  measurable := Complex.measurable_ofReal.comp CCM.nativePositiveCompletion_measurable
  integrable := CCM.nativePositiveCompletion_integrable.ofReal
  zero_before := by intro t ht; rw [CCM.nativePositiveCompletion_eq_zero_of_neg ht,Complex.ofReal_zero]

theorem nativeCompletionCausalKernel_laplace {z : ℂ} (hz : 1/2<z.re) :
    nativeCompletionCausalKernel.laplace z=
      CCM.nativeCompletionRationalMultiplier z*riemannZeta (z+1/2) :=
  CCM.nativePositiveCompletion_complexLaplace_of_half_lt_re hz

def NativeCausalState.completionAction (state : NativeCausalState) : NativeCausalState :=
  state.convolveAction nativeCompletionCausalKernel

theorem NativeCausalState.laplace_completionAction (state : NativeCausalState) {z : ℂ}
    (hz0 : 1/2<z.re) (hz : ∀ term ∈ state, term.regular.exponent<z.re) :
    state.completionAction.laplace z=
      (CCM.nativeCompletionRationalMultiplier z*riemannZeta (z+1/2))*state.laplace z := by
  rw [completionAction,laplace_convolveAction state _ hz,nativeCompletionCausalKernel_laplace hz0]





theorem nativeIntegerCoefficient_eq_halfExp {n : ℕ} (hn : 0<n) :
    (nativeIntegerCoefficient n:ℂ)=Complex.exp (-(1/2:ℂ)*(Real.log n:ℂ)) := by
  have hnreal : 0<(n:ℝ) := by exact_mod_cast hn
  have hrootreal : Real.sqrt (n:ℝ)=Real.exp (Real.log n/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hnreal]
    congr 1
    ring
  have hroot : (Real.sqrt (n:ℝ):ℂ)=Complex.exp ((Real.log n:ℂ)/2) := by
    rw [hrootreal,Complex.ofReal_exp]
    push_cast
    rfl
  unfold nativeIntegerCoefficient
  rw [Complex.ofReal_div,Complex.ofReal_one,hroot,one_div,←Complex.exp_neg]
  congr 1
  ring

theorem NativeCausalState.applyTest_addAction (state other : NativeCausalState)
    (test : NativeCompactTest) :
    (state.addAction other).applyTest test=state.applyTest test+other.applyTest test := by
  simp [addAction,applyTest,List.map_append,List.sum_append]

theorem NativeCausalState.applyTest_scaleAction (c : ℂ) (state : NativeCausalState)
    (test : NativeCompactTest) :
    (scaleAction c state).applyTest test=c*state.applyTest test := by
  induction state with
  | nil => simp [scaleAction,applyTest]
  | cons term state ih =>
    simp only [scaleAction,applyTest,List.map_map,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    ring

def NativeCausalState.primeEulerAction (state : NativeCausalState) (p : ℕ) : NativeCausalState :=
  state.addAction (scaleAction (-Complex.exp (-(1/2:ℂ)*(Real.log p:ℂ)))
    (state.delayAction (Real.log p) (Real.log_natCast_nonneg p)))

theorem NativeCausalState.applyTest_primeEulerAction (state : NativeCausalState)
    (p : ℕ) (hp : 0<p) (test : NativeCompactTest) :
    (state.primeEulerAction p).applyTest test=state.applyTest test-
      (nativeIntegerCoefficient p:ℂ)*
        (state.delayAction (Real.log p) (Real.log_natCast_nonneg p)).applyTest test := by
  rw [primeEulerAction,applyTest_addAction,applyTest_scaleAction,
    nativeIntegerCoefficient_eq_halfExp hp]
  ring

theorem NativeCausalState.laplace_primeEulerAction (state : NativeCausalState)
    (p : ℕ) (z : ℂ) :
    (state.primeEulerAction p).laplace z =
      (1-Complex.exp (-(z+1/2)*(Real.log p:ℂ)))*state.laplace z := by
  rw [primeEulerAction,laplace_addAction,laplace_scaleAction,laplace_delayAction]
  have he : Complex.exp (-(1/2:ℂ)*(Real.log p:ℂ))*
      Complex.exp (-(Real.log p:ℂ)*z) =
      Complex.exp (-(z+1/2)*(Real.log p:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  calc
    _ = state.laplace z-(Complex.exp (-(1/2:ℂ)*(Real.log p:ℂ))*
        Complex.exp (-(Real.log p:ℂ)*z))*state.laplace z := by ring
    _ = _ := by rw [he]; ring

def NativeCausalState.eulerListAction : NativeCausalState → List ℕ → NativeCausalState
  | state, [] => state
  | state, p::ps => (state.primeEulerAction p).eulerListAction ps

theorem NativeCausalState.laplace_eulerListAction (state : NativeCausalState)
    (primes : List ℕ) (z : ℂ) :
    (state.eulerListAction primes).laplace z =
      (primes.map (fun p : ℕ => 1-Complex.exp (-(z+1/2)*(Real.log p:ℂ)))).prod*state.laplace z := by
  induction primes generalizing state with
  | nil => simp [eulerListAction]
  | cons p ps ih =>
    rw [eulerListAction,ih,laplace_primeEulerAction]
    simp only [List.map_cons,List.prod_cons]
    ring

def NativeCausalState.finiteEulerAction (state : NativeCausalState) (Q : ℕ) : NativeCausalState :=
  state.eulerListAction Q.primeFactors.toList

theorem NativeCausalState.laplace_finiteEulerAction (state : NativeCausalState)
    (Q : ℕ) (z : ℂ) :
    (state.finiteEulerAction Q).laplace z=finiteEulerMultiplier Q z*state.laplace z := by
  rw [finiteEulerAction,laplace_eulerListAction]
  simp only [finiteEulerMultiplier,Finset.prod_map_toList]





theorem NativeRegularCausal.weightedTranslate_eq_history (f : NativeRegularCausal)
    (c : ℕ → ℂ) {T t : ℝ} (ht : t≤T) :
    (∑' n : ℕ, c n*f (t-Real.log n)) =
      ∑ n ∈ range (nativeHistoryCutoff 0 T+1), c n*f (t-Real.log n) := by
  apply tsum_eq_sum
  intro n hn
  have hcut : nativeHistoryCutoff 0 T<n := by
    simp only [Finset.mem_range,not_lt] at hn
    omega
  have he : Real.exp T<(n:ℝ) := by simpa only [nativeHistoryCutoff,add_zero] using Nat.lt_of_floor_lt hcut
  have hnpos : 0<(n:ℝ) := (Real.exp_pos T).trans he
  have hlog : T<Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr he
  rw [f.zero_before _ (by linarith),mul_zero]

theorem NativeRegularCausal.translate_norm_le (f : NativeRegularCausal)
    (t : ℝ) (_ht : 0≤t) (n : ℕ) :
    ‖f (t-Real.log n)‖≤f.amplitude*Real.exp (f.exponent*t) := by
  by_cases hnegative : t-Real.log n<0
  · rw [f.zero_before _ hnegative,norm_zero]
    exact mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le
  · exact (f.norm_le _ (le_of_not_gt hnegative)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_self t (Real.log_natCast_nonneg n))
          f.exponent_nonneg)) f.amplitude_nonneg)

theorem NativeRegularCausal.weightedTranslate_norm_le (f : NativeRegularCausal)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖≤1) (t : ℝ) (ht : 0≤t) :
    ‖∑' n : ℕ, c n*f (t-Real.log n)‖≤
      (2*f.amplitude)*Real.exp ((f.exponent+1)*t) := by
  rw [f.weightedTranslate_eq_history c (le_refl t)]
  let N := nativeHistoryCutoff 0 t+1
  have hN : (N:ℝ)≤2*Real.exp t := by
    have hf : (nativeHistoryCutoff 0 t:ℝ)≤Real.exp t := by
      simpa only [nativeHistoryCutoff,add_zero] using Nat.floor_le (Real.exp_pos t).le
    have hE : 1≤Real.exp t := Real.one_le_exp_iff.mpr ht
    dsimp [N]
    push_cast
    linarith
  calc
    _ ≤ ∑ n ∈ range N, ‖c n*f (t-Real.log n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, f.amplitude*Real.exp (f.exponent*t) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)).trans
        (by simpa using f.translate_norm_le t ht n)
    _ = (N:ℝ)*(f.amplitude*Real.exp (f.exponent*t)) := by simp [nsmul_eq_mul]
    _ ≤ (2*Real.exp t)*(f.amplitude*Real.exp (f.exponent*t)) :=
      mul_le_mul_of_nonneg_right hN (mul_nonneg f.amplitude_nonneg (Real.exp_pos _).le)
    _ = _ := by rw [show (f.exponent+1)*t=f.exponent*t+t by ring,Real.exp_add]; ring

def NativeRegularCausal.weightedIntegerTranslate (f : NativeRegularCausal)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖≤1) : NativeRegularCausal where
  toFun t := ∑' n : ℕ, c n*f (t-Real.log n)
  measurable := Measurable.tsum fun n => measurable_const.mul
    (f.measurable.comp (continuous_id.sub continuous_const).measurable)
  zero_before := by
    intro t ht
    have hzero (n : ℕ) : c n*f (t-Real.log n)=0 := by
      rw [f.zero_before _ (by linarith [Real.log_natCast_nonneg n]),mul_zero]
    simp only [hzero,tsum_zero]
  amplitude := 2*f.amplitude
  exponent := f.exponent+1
  amplitude_nonneg := mul_nonneg (by norm_num) f.amplitude_nonneg
  exponent_nonneg := by linarith [f.exponent_nonneg]
  norm_le := f.weightedTranslate_norm_le c hc

theorem nativeIntegerCoefficient_complex_norm_le_one (n : ℕ) :
    ‖(nativeIntegerCoefficient n:ℂ)‖≤1 := by
  by_cases hn : n=0
  · subst n; norm_num [nativeIntegerCoefficient]
  have hs : 1≤Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  rw [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0≤nativeIntegerCoefficient n from by unfold nativeIntegerCoefficient; positivity)]
  exact (div_le_one (by positivity : 0<Real.sqrt (n:ℝ))).mpr hs

def NativeRegularCausal.integerTranslate (f : NativeRegularCausal) : NativeRegularCausal :=
  f.weightedIntegerTranslate (fun n => (nativeIntegerCoefficient n:ℂ))
    nativeIntegerCoefficient_complex_norm_le_one

theorem NativeRegularCausal.integerTranslate_integrable_laplace (f : NativeRegularCausal)
    (z : ℂ) (hz : 1/2<z.re)
    (hf : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*f t)) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*f.integerTranslate t) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*f.integerTranslate t)=
      riemannZeta (z+1/2)*(∫ t : ℝ, Complex.exp (-z*(t:ℂ))*f t) := by
  have h := complexWeightedTranslate_integrable_laplace
    (fun n => (nativeIntegerCoefficient n:ℂ)) f.toFun z hf
    (nativeIntegerLaplaceCoefficient_summable_norm hz)
  have hsum : (∑' n : ℕ, (nativeIntegerCoefficient n:ℂ)*Complex.exp (-z*(Real.log n:ℂ)))=
      riemannZeta (z+1/2) := nativeIntegerLaplaceCoefficient_tsum hz
  simpa only [integerTranslate,weightedIntegerTranslate,hsum] using h

def NativeCausalState.integerTranslateAction (state : NativeCausalState) : NativeCausalState :=
  state.map fun term => {term with regular := term.regular.integerTranslate}

theorem NativeCausalState.laplace_integerTranslateAction (state : NativeCausalState)
    (z : ℂ) (hz : 1/2<z.re)
    (hf : ∀ term∈state, Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) :
    state.integerTranslateAction.laplace z=riemannZeta (z+1/2)*state.laplace z := by
  induction state with
  | nil => simp [integerTranslateAction,laplace]
  | cons term state ih =>
    simp only [integerTranslateAction,laplace,List.map_map,List.map_cons,List.sum_cons] at ih ⊢
    rw [(term.regular.integerTranslate_integrable_laplace z hz (hf term (by simp))).2,
      ih (fun other ho => hf other (by simp [ho]))]
    ring





def NativeCausalState.finiteTranslateListAction (state : NativeCausalState)
    (c : ℕ → ℂ) : List ℕ → NativeCausalState
  | [] => []
  | n::ns => (scaleAction (c n) (state.delayAction (Real.log n)
      (Real.log_natCast_nonneg n))).addAction (state.finiteTranslateListAction c ns)

theorem NativeCausalState.laplace_finiteTranslateListAction (state : NativeCausalState)
    (c : ℕ → ℂ) (ns : List ℕ) (z : ℂ) :
    (state.finiteTranslateListAction c ns).laplace z=
      (ns.map (fun n => c n*Complex.exp (-z*(Real.log n:ℂ)))).sum*state.laplace z := by
  induction ns with
  | nil => simp [finiteTranslateListAction,laplace]
  | cons n ns ih =>
    rw [finiteTranslateListAction,laplace_addAction,laplace_scaleAction,laplace_delayAction,ih]
    simp only [List.map_cons,List.sum_cons]
    have he : -(Real.log n:ℂ)*z = -z*(Real.log n:ℂ) := by ring
    rw [he]
    ring

def NativeCausalState.truncatedMoebiusAction (state : NativeCausalState) (Y : ℕ) :
    NativeCausalState :=
  state.finiteTranslateListAction
    (fun n => (ArithmeticFunction.moebius n:ℂ)*(nativeIntegerCoefficient n:ℂ))
    (List.range (Y+1))

theorem NativeCausalState.laplace_truncatedMoebiusAction (state : NativeCausalState)
    (Y : ℕ) (z : ℂ) :
    (state.truncatedMoebiusAction Y).laplace z=truncatedMoebiusMultiplier Y z*state.laplace z := by
  rw [truncatedMoebiusAction,laplace_finiteTranslateListAction]
  congr 1
  simp only [truncatedMoebiusMultiplier,nativeIntegerLaplaceCoefficient,mul_assoc]
  simpa only [List.toFinset_range] using
    (List.sum_toFinset (fun n : ℕ => (ArithmeticFunction.moebius n:ℂ)*
      ((nativeIntegerCoefficient n:ℂ)*Complex.exp (-z*(Real.log n:ℂ))))
        (show (List.range (Y+1)).Nodup from List.nodup_range)).symm

theorem NativeCausalState.exists_regular_laplace_threshold (state : NativeCausalState) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re → ∀ term∈state,
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t) := by
  induction state with
  | nil => exact ⟨0,fun z hz term ht => by simp at ht⟩
  | cons term state ih =>
    obtain ⟨S,hS⟩ := ih
    refine ⟨max term.regular.exponent S,fun z hz other ho => ?_⟩
    rcases List.mem_cons.mp ho with h | h
    · subst other
      exact term.regular.laplace_integrable ((le_max_left _ _).trans_lt hz)
    · exact hS z ((le_max_right _ _).trans_lt hz) other h

def NativeCausalState.residualStepAction (state : NativeCausalState) (Y : ℕ) : NativeCausalState :=
  state.addAction (scaleAction (-1) (state.truncatedMoebiusAction Y).integerTranslateAction)

theorem NativeCausalState.laplace_residualStepAction (state : NativeCausalState) (Y : ℕ) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.residualStepAction Y).laplace z=
        (1-riemannZeta (z+1/2)*truncatedMoebiusMultiplier Y z)*state.laplace z := by
  obtain ⟨S,hS⟩ := (state.truncatedMoebiusAction Y).exists_regular_laplace_threshold
  refine ⟨max (1/2) S,fun z hz => ?_⟩
  rw [residualStepAction,laplace_addAction,laplace_scaleAction,
    laplace_integerTranslateAction _ z ((le_max_left _ _).trans_lt hz)
      (hS z ((le_max_right _ _).trans_lt hz)),laplace_truncatedMoebiusAction]
  ring

def NativeCausalState.residualPowerAction (state : NativeCausalState) (Y : ℕ) :
    ℕ → NativeCausalState
  | 0 => state
  | r+1 => (state.residualPowerAction Y r).residualStepAction Y

theorem NativeCausalState.laplace_residualPowerAction (state : NativeCausalState)
    (Y r : ℕ) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.residualPowerAction Y r).laplace z=
        (1-riemannZeta (z+1/2)*truncatedMoebiusMultiplier Y z)^r*state.laplace z := by
  induction r with
  | zero => exact ⟨0,fun z hz => by simp [residualPowerAction]⟩
  | succ r ih =>
    obtain ⟨S,hS⟩ := ih
    obtain ⟨T,hT⟩ := (state.residualPowerAction Y r).laplace_residualStepAction Y
    refine ⟨max S T,fun z hz => ?_⟩
    rw [residualPowerAction,hT z ((le_max_right _ _).trans_lt hz),
      hS z ((le_max_left _ _).trans_lt hz),pow_succ]
    ring


/-- The paper's arbitrary real cutoff. The natural index is its exact
finite-support encoding, with the physical history equality proved below. -/
def truncatedMoebiusRealMultiplier (Y : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, if (n:ℝ)≤Y then
    (ArithmeticFunction.moebius n:ℂ)*nativeIntegerLaplaceCoefficient z n else 0

theorem realCutoff_history_eq_floor (Y : ℝ) (hY : 0≤Y) (F : ℕ → ℂ) :
    (∑' n : ℕ, if (n:ℝ)≤Y then F n else 0) =
      ∑ n ∈ range (Nat.floor Y+1), F n := by
  calc
    _ = ∑ n ∈ range (Nat.floor Y+1), if (n:ℝ)≤Y then F n else 0 := by
      apply tsum_eq_sum
      intro n hn
      have hn' : Nat.floor Y<n := by
        have hn1 : ¬n<Nat.floor Y+1 := by simpa only [Finset.mem_range] using hn
        omega
      rw [if_neg (not_le.mpr (Nat.lt_of_floor_lt hn'))]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [if_pos ((Nat.le_floor_iff hY).mp (Nat.lt_succ_iff.mp (mem_range.mp hn)))]

theorem truncatedMoebiusRealMultiplier_eq_floor (Y : ℝ) (hY : 0≤Y) (z : ℂ) :
    truncatedMoebiusRealMultiplier Y z=truncatedMoebiusMultiplier (Nat.floor Y) z :=
  realCutoff_history_eq_floor Y hY _

theorem truncatedMoebiusReal_physical_history (Y : ℝ) (hY : 0≤Y)
    (f : ℝ → ℂ) (t : ℝ) :
    (∑' n : ℕ, if (n:ℝ)≤Y then
      (ArithmeticFunction.moebius n:ℂ)*(nativeIntegerCoefficient n:ℂ)*f (t-Real.log n) else 0) =
    ∑ n ∈ range (Nat.floor Y+1),
      (ArithmeticFunction.moebius n:ℂ)*(nativeIntegerCoefficient n:ℂ)*f (t-Real.log n) :=
  realCutoff_history_eq_floor Y hY _

def NativeGenerator.residualPowerReal (Y : ℝ) (r : ℕ) : NativeGenerator :=
  .residualPower (Nat.floor Y) r

theorem NativeGenerator.residualPowerReal_multiplier (Y : ℝ) (hY : 0≤Y) (r : ℕ) (z : ℂ) :
    (NativeGenerator.residualPowerReal Y r).multiplier z=
      (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier Y z)^r := by
  rw [truncatedMoebiusRealMultiplier_eq_floor Y hY]
  rfl

def NativeCausalState.residualPowerRealAction (state : NativeCausalState) (Y : ℝ)
    (r : ℕ) : NativeCausalState := state.residualPowerAction (Nat.floor Y) r

theorem NativeCausalState.laplace_residualPowerRealAction (state : NativeCausalState)
    (Y : ℝ) (hY : 0≤Y) (r : ℕ) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.residualPowerRealAction Y r).laplace z=
        (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier Y z)^r*state.laplace z := by
  simpa only [residualPowerRealAction,truncatedMoebiusRealMultiplier_eq_floor Y hY] using
    state.laplace_residualPowerAction (Nat.floor Y) r

end Zeta23.OPICAFollowup
