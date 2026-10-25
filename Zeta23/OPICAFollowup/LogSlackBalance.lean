import Zeta23.OPICAFollowup.BalancedCoefficients
import Zeta23.OPICAFollowup.ForwardLocalization
import Zeta23.OPICA.NativeArithmeticAdapter
import Mathlib.Tactic

/-! Actual logarithmic-slack cutoffs and locally finite arithmetic histories.
The coefficients and palette filters below are literal arithmetic functions;
all translated sums are regrouped using their causal finite histories. -/

noncomputable section
open Finset Set MeasureTheory Filter
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup
open Zeta23.CCM Zeta23.OPICA

def logSlackY (r : ℕ) (K T : ℝ) : ℝ :=
  Real.exp (T/(r:ℝ)-(K/(r:ℝ))*Real.log T)

def logSlackZ (r : ℕ) (K T : ℝ) : ℝ :=
  Real.exp (T/(r:ℝ)-nativeCausalGap+(K*((r:ℝ)-1)/(r:ℝ))*Real.log T)

theorem logSlackY_pos (r : ℕ) (K T : ℝ) : 0<logSlackY r K T := Real.exp_pos _

theorem logSlackZ_pos (r : ℕ) (K T : ℝ) : 0<logSlackZ r K T := Real.exp_pos _

theorem log_logSlackY (r : ℕ) (K T : ℝ) :
    Real.log (logSlackY r K T)=T/(r:ℝ)-(K/(r:ℝ))*Real.log T := Real.log_exp _

theorem log_logSlackZ (r : ℕ) (K T : ℝ) :
    Real.log (logSlackZ r K T)=T/(r:ℝ)-nativeCausalGap+
      (K*((r:ℝ)-1)/(r:ℝ))*Real.log T := Real.log_exp _

theorem logSlackY_eq_paper (r : ℕ) (K : ℝ) {T : ℝ} (hT : 0<T) :
    logSlackY r K T=Real.exp (T/(r:ℝ))*T^(-K/(r:ℝ)) := by
  rw [Real.rpow_def_of_pos hT,←Real.exp_add]
  dsimp [logSlackY]
  congr 1
  ring

theorem logSlackZ_eq_paper (r : ℕ) (K : ℝ) {T : ℝ} (hT : 0<T) :
    logSlackZ r K T=Real.exp (T/(r:ℝ)-nativeCausalGap)*T^(K*((r:ℝ)-1)/(r:ℝ)) := by
  rw [Real.rpow_def_of_pos hT,←Real.exp_add]
  dsimp [logSlackZ]
  congr 1
  ring

theorem logSlackY_continuousOn (r : ℕ) (K : ℝ) : ContinuousOn (logSlackY r K) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) := fun x hx =>
    (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  exact Real.continuous_exp.comp_continuousOn ((continuous_id.div_const _).continuousOn.sub
    (continuousOn_const.mul hlog))

theorem logSlackZ_continuousOn (r : ℕ) (K : ℝ) : ContinuousOn (logSlackZ r K) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) := fun x hx =>
    (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  exact Real.continuous_exp.comp_continuousOn (((continuous_id.div_const _).continuousOn.sub continuousOn_const).add
    (continuousOn_const.mul hlog))

/-- The action retains the real square-root weight at every actual integer. -/
def arithmeticHistoryAction (a : ArithmeticFunction ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  realWeightedLogTranslate (fun n => a n/Real.sqrt (n:ℝ)) f t

theorem arithmeticHistoryAction_history (a : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    {g T t : ℝ} (hf : ∀ u<g, f u=0) (ht : t≤T) :
    arithmeticHistoryAction a f t=
      ∑ n∈range (Nat.floor (Real.exp (T-g))+1), a n/Real.sqrt (n:ℝ)*f (t-Real.log n) :=
  realWeightedLogTranslate_history _ hf ht

theorem arithmeticHistoryAction_zero_before (a : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    {g t : ℝ} (hf : ∀ u<g, f u=0) (ht : t<g) : arithmeticHistoryAction a f t=0 := by
  apply Eq.trans (tsum_congr ?_) (tsum_zero)
  intro n
  by_cases hn : n=0
  · subst n; simp
  · have hlog : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    rw [hf _ (by linarith),mul_zero]

theorem arithmeticHistoryAction_add (a b : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    {g : ℝ} (hf : ∀ u<g, f u=0) (t : ℝ) :
    arithmeticHistoryAction (a+b) f t=arithmeticHistoryAction a f t+arithmeticHistoryAction b f t := by
  rw [arithmeticHistoryAction_history (a+b) hf le_rfl,
    arithmeticHistoryAction_history a hf le_rfl,arithmeticHistoryAction_history b hf le_rfl,←sum_add_distrib]
  apply sum_congr rfl
  intro n _
  simp only [ArithmeticFunction.add_apply]
  ring

theorem arithmeticHistoryAction_one (f : ℝ → ℝ) (t : ℝ) : arithmeticHistoryAction 1 f t=f t := by
  calc
    _ = ∑' n : ℕ, if n=1 then f t else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : n=1
      · subst n; simp
      · simp [hn]
    _ = _ := by simp

theorem arithmeticHistoryAction_zeta (f : ℝ → ℝ) (t : ℝ) :
    arithmeticHistoryAction (ArithmeticFunction.zeta : ArithmeticFunction ℝ) f t=
      nativeIntegerTranslateAction f t := by
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n; simp [nativeIntegerCoefficient]
  · simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hn,nativeIntegerCoefficient]

/-- The finite divisor filter is the paper's literal D_Q. -/
def paletteDivisorCoefficients (Q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n∣Q then (ArithmeticFunction.moebius n:ℝ) else 0,by simp⟩

def nativePaletteDrive (d Q : ℕ) : ℝ → ℝ :=
  arithmeticHistoryAction (paletteDivisorCoefficients Q) (integerDriveFamily d)

def typeIField (d r Q : ℕ) (Y : ℝ) : ℝ → ℝ :=
  arithmeticHistoryAction (typeICoefficients Q Y r) (nativePaletteDrive d Q)

def balancedField (d r Q : ℕ) (Y : ℝ) : ℝ → ℝ :=
  arithmeticHistoryAction (balancedInverseCoefficients Q Y r) (nativePaletteDrive d Q)

theorem small_coefficients_support (Q : ℕ) (Y : ℝ) (n : ℕ)
    (hn : nativeSmallCoefficients Q Y n≠0) : (n:ℝ)≤Y := by
  by_contra h
  apply hn
  simp [nativeSmallCoefficients,h]

theorem large_coefficients_support (Q : ℕ) (Y : ℝ) (n : ℕ)
    (hn : nativeLargeCoefficients Q Y n≠0) : Y<(n:ℝ) := by
  by_contra h
  apply hn
  simp [nativeLargeCoefficients,h]

theorem small_power_support (Q : ℕ) {Y : ℝ} (_hY : 0≤Y) (k n : ℕ)
    (hn : (nativeSmallCoefficients Q Y^k) n≠0) : (n:ℝ)≤Y^k := by
  by_contra hbound
  apply hn
  rw [dirichlet_power_tuple_expansion]
  apply sum_eq_zero
  intro w hw
  by_contra hp
  have hcoord (i : Fin k) : (w i:ℝ)≤Y :=
    small_coefficients_support Q Y (w i) (Finset.prod_ne_zero_iff.mp hp i (mem_univ _))
  have hprod : (∏ i : Fin k, (w i:ℝ))≤Y^k := by
    calc
      _ ≤ ∏ _i : Fin k, Y := prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hcoord i)
      _ = _ := by simp
  have heq : (∏ i : Fin k, (w i:ℝ))=(n:ℝ) := by
    rw [←Nat.cast_prod,Nat.prod_eq_of_mem_finMulAntidiag hw]
  rw [heq] at hprod
  exact hbound hprod

/-- This multiplication-indexed summand is used only to justify regrouping. -/
def arithmeticHistoryPairTerm (a b : ArithmeticFunction ℝ) (f : ℝ → ℝ) (t : ℝ)
    (p : ℕ×ℕ) : ℝ :=
  (a p.1*b p.2)/Real.sqrt ((p.1*p.2:ℕ):ℝ)*f (t-Real.log ((p.1*p.2:ℕ):ℝ))

theorem arithmeticHistoryPairTerm_translate (a b : ArithmeticFunction ℝ)
    (f : ℝ → ℝ) (t : ℝ) (m n : ℕ) :
    arithmeticHistoryPairTerm a b f t (m,n)=
      (a m/Real.sqrt (m:ℝ))*((b n/Real.sqrt (n:ℝ))*f ((t-Real.log m)-Real.log n)) := by
  by_cases hm : m=0
  · subst m; simp [arithmeticHistoryPairTerm]
  by_cases hn : n=0
  · subst n; simp [arithmeticHistoryPairTerm]
  have hmreal : (m:ℝ)≠0 := by exact_mod_cast hm
  have hnreal : (n:ℝ)≠0 := by exact_mod_cast hn
  have harg : t-Real.log ((m*n:ℕ):ℝ)=(t-Real.log m)-Real.log n := by
    rw [Nat.cast_mul,Real.log_mul hmreal hnreal]
    ring
  dsimp [arithmeticHistoryPairTerm]
  rw [harg,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem arithmeticHistoryPair_summable (a b : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    {g : ℝ} (hf : ∀ u<g, f u=0) (t : ℝ) : Summable (arithmeticHistoryPairTerm a b f t) := by
  let N := Nat.floor (Real.exp (t-g))
  apply summable_of_ne_finset_zero (s := range (N+1)×ˢrange (N+1))
  rintro ⟨m,n⟩ hnot
  by_cases hm : m=0
  · subst m; simp [arithmeticHistoryPairTerm]
  by_cases hn : n=0
  · subst n; simp [arithmeticHistoryPairTerm]
  have hprod : N<m*n := by
    simp only [Finset.mem_product,Finset.mem_range,not_and_or,not_lt] at hnot
    rcases hnot with hmcut | hncut
    · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hn))
    · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm))
  have he : Real.exp (t-g)<((m*n:ℕ):ℝ) := Nat.lt_of_floor_lt hprod
  have hpos : 0<((m*n:ℕ):ℝ) := (Real.exp_pos _).trans he
  have hlog : t-g<Real.log ((m*n:ℕ):ℝ) := (Real.lt_log_iff_exp_lt hpos).mpr he
  dsimp [arithmeticHistoryPairTerm]
  rw [hf _ (by linarith),mul_zero]

theorem arithmeticHistoryPair_fiber (a b : ArithmeticFunction ℝ)
    (f : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    (∑' p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, arithmeticHistoryPairTerm a b f t p.val)=
      (a*b) n/Real.sqrt (n:ℝ)*f (t-Real.log n) := by
  by_cases hn : n=0
  · subst n
    have hzero : ∀ p : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {0},
        arithmeticHistoryPairTerm a b f t p.val=0 := by
      rintro ⟨⟨m,n⟩,hp⟩
      have hmn : m*n=0 := by simpa using hp
      rcases Nat.mul_eq_zero.mp hmn with hm | hn
      · subst m; simp [arithmeticHistoryPairTerm]
      · subst n; simp [arithmeticHistoryPairTerm]
    simp [hzero]
  rw [show (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}=n.divisorsAntidiagonal by ext p; simp [hn]]
  rw [Finset.tsum_subtype' n.divisorsAntidiagonal (arithmeticHistoryPairTerm a b f t)]
  calc
    _ = ∑ p∈n.divisorsAntidiagonal, (a p.1*b p.2)/Real.sqrt (n:ℝ)*f (t-Real.log n) := by
      apply sum_congr rfl
      intro p hp
      dsimp [arithmeticHistoryPairTerm]
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = _ := by rw [ArithmeticFunction.mul_apply,Finset.sum_div,Finset.sum_mul]

theorem arithmeticHistoryPair_inner (a b : ArithmeticFunction ℝ)
    (f : ℝ → ℝ) (t : ℝ) (m : ℕ) :
    (∑' n : ℕ, arithmeticHistoryPairTerm a b f t (m,n))=
      (a m/Real.sqrt (m:ℝ))*arithmeticHistoryAction b f (t-Real.log m) := by
  simp_rw [arithmeticHistoryPairTerm_translate]
  rw [tsum_mul_left]
  rfl

/-- Genuine local Fubini for arbitrary arithmetic coefficients and a causal
history. No global summability or conclusion-shaped field hypothesis is used. -/
theorem arithmeticHistoryAction_mul (a b : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    {g : ℝ} (hf : ∀ u<g, f u=0) (t : ℝ) :
    arithmeticHistoryAction a (arithmeticHistoryAction b f) t=arithmeticHistoryAction (a*b) f t := by
  have hpair := arithmeticHistoryPair_summable a b hf t
  calc
    _ = ∑' m : ℕ, ∑' n : ℕ, arithmeticHistoryPairTerm a b f t (m,n) := by
      apply tsum_congr
      intro m
      exact (arithmeticHistoryPair_inner a b f t m).symm
    _ = ∑' p : ℕ×ℕ, arithmeticHistoryPairTerm a b f t p := hpair.tsum_prod.symm
    _ = _ := by
      have h := hpair.hasSum.tsum_fiberwise (fun p : ℕ×ℕ => p.1*p.2)
      have hsum : HasSum (fun n : ℕ => (a*b) n/Real.sqrt (n:ℝ)*f (t-Real.log n))
          (∑' p : ℕ×ℕ, arithmeticHistoryPairTerm a b f t p) := by
        simpa only [arithmeticHistoryPair_fiber] using h
      exact hsum.tsum_eq.symm

theorem paletteDivisor_mul_zeta (Q : ℕ) :
    paletteDivisorCoefficients Q*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)=nativeFreeCoefficients Q := by
  ext n
  by_cases hn : n=0
  · subst n; simp
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  change (∑ d∈n.divisors, if d∣Q then (ArithmeticFunction.moebius d:ℝ) else 0)=_
  rw [←Finset.sum_filter]
  have hg : Nat.gcd n Q≠0 := (Nat.gcd_pos_of_pos_left Q (Nat.pos_of_ne_zero hn)).ne'
  have hset : n.divisors.filter (fun d => d∣Q)=(Nat.gcd n Q).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    exact ⟨fun h => ⟨Nat.dvd_gcd h.1.1 h.2,hg⟩,
      fun h => ⟨⟨h.1.trans (Nat.gcd_dvd_left _ _),hn⟩,h.1.trans (Nat.gcd_dvd_right _ _)⟩⟩
  rw [hset]
  have hsum : (∑ d∈(Nat.gcd n Q).divisors, (ArithmeticFunction.moebius d:ℝ))=
      (1:ArithmeticFunction ℝ) (Nat.gcd n Q) := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd n Q))
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
    rw [ArithmeticFunction.coe_mul_zeta_apply] at h
    simpa only [ArithmeticFunction.intCoe_apply] using h
  rw [hsum]
  change (if Nat.gcd n Q=1 then 1 else 0)=
    if Nat.Coprime n Q then (ArithmeticFunction.zeta : ArithmeticFunction ℝ) n else 0
  simp only [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hn,Nat.cast_one,
    Nat.coprime_iff_gcd_eq_one]

theorem nativePaletteDrive_zero_before (d Q : ℕ) {t : ℝ} (ht : t<nativeCausalGap) :
    nativePaletteDrive d Q t=0 :=
  arithmeticHistoryAction_zero_before _ (fun _ hu => integerDriveFamily_zero_before d hu) ht

/-- The complete i-fold palette shift is paid before any forward-kernel estimate. -/
theorem logSlack_argument_lower_bound (r : ℕ) (hr : 0<r) (C eta K T : ℝ)
    (hT : 1≤T) (Q : ℕ) (hQ : 0<Q) (hQbudget : (Q:ℝ)≤T^eta)
    (hY : 1≤logSlackY r K T) (i : ℕ) (hi : i≤r)
    (n q : Fin i → ℕ) (hn : ∀ j, 0<n j ∧ (n j:ℝ)≤logSlackY r K T)
    (hq : ∀ j, q j∣Q) (t : ℝ) (ht : T-C*Real.log T≤t) :
    (K-C-(r:ℝ)*eta)*Real.log T ≤
      t-(∑ j, Real.log (n j:ℝ))-(∑ j, Real.log (q j:ℝ)) := by
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hQpos : (0:ℝ)<Q := by exact_mod_cast hQ
  have hlogQ : Real.log (Q:ℝ)≤eta*Real.log T := by
    have h := Real.log_le_log hQpos hQbudget
    rwa [Real.log_rpow hTpos] at h
  have hlogQ0 : 0≤Real.log (Q:ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hlogY0 : 0≤Real.log (logSlackY r K T) := Real.log_nonneg hY
  have hnlog : (∑ j, Real.log (n j:ℝ))≤(i:ℝ)*Real.log (logSlackY r K T) := by
    calc
      _ ≤ ∑ _j : Fin i, Real.log (logSlackY r K T) := sum_le_sum fun j _ =>
        Real.log_le_log (by exact_mod_cast (hn j).1) (hn j).2
      _ = _ := by simp
  have hqlog : (∑ j, Real.log (q j:ℝ))≤(i:ℝ)*Real.log (Q:ℝ) := by
    calc
      _ ≤ ∑ _j : Fin i, Real.log (Q:ℝ) := by
        apply sum_le_sum
        intro j _
        have hqpos : 0<q j := Nat.pos_of_dvd_of_pos (hq j) hQ
        exact Real.log_le_log (by exact_mod_cast hqpos) (by exact_mod_cast Nat.le_of_dvd hQ (hq j))
      _ = _ := by simp
  have hir : (i:ℝ)≤r := by exact_mod_cast hi
  have hdelay : (i:ℝ)*Real.log (logSlackY r K T)+(i:ℝ)*Real.log (Q:ℝ)≤
      (r:ℝ)*Real.log (logSlackY r K T)+(r:ℝ)*Real.log (Q:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hir hlogY0,mul_le_mul_of_nonneg_right hir hlogQ0]
  have hrne : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hscale : (r:ℝ)*Real.log (logSlackY r K T)=T-K*Real.log T := by
    rw [log_logSlackY]
    field_simp
  have hQscale := mul_le_mul_of_nonneg_left hlogQ (Nat.cast_nonneg (α:=ℝ) r)
  rw [hscale] at hdelay
  nlinarith

theorem nativePaletteDrive_eq_free_action (d Q : ℕ) (t : ℝ) :
    nativePaletteDrive d Q t=arithmeticHistoryAction (nativeFreeCoefficients Q) (primeFieldFamily d) t := by
  have hU : integerDriveFamily d=arithmeticHistoryAction (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      (primeFieldFamily d) := by
    funext u
    rw [arithmeticHistoryAction_zeta]
    exact (nativeIntegerTranslateAction_primeField_eq_integerDriveField (sourceFamily_supported d) u).symm
  rw [nativePaletteDrive,hU,arithmeticHistoryAction_mul _ _ (fun _ hu => primeFieldFamily_zero_before d hu),
    paletteDivisor_mul_zeta]

theorem nativePaletteDrive_actual_inverse (d Q : ℕ) (t : ℝ) :
    arithmeticHistoryAction (nativeInverseCoefficients Q) (nativePaletteDrive d Q) t=primeFieldFamily d t := by
  have heq : nativePaletteDrive d Q=arithmeticHistoryAction (nativeFreeCoefficients Q) (primeFieldFamily d) :=
    funext (nativePaletteDrive_eq_free_action d Q)
  rw [heq,arithmeticHistoryAction_mul _ _ (fun _ hu => primeFieldFamily_zero_before d hu),
    native_coefficients_moebius_inverse,arithmeticHistoryAction_one]

/-- Exact literal physical decomposition, before selecting any asymptotic window. -/
theorem native_balanced_physical_identity (d r Q : ℕ) (hr : 2≤r) (Y : ℝ) (hY : 1≤Y) (t : ℝ) :
    primeFieldFamily d t=typeIField d r Q Y t+balancedField d r Q Y t := by
  have hid := (native_binomial_inverse_identity Q Y hY r hr).1
  rw [←nativePaletteDrive_actual_inverse d Q t,hid,
    arithmeticHistoryAction_add _ _ (fun _ hu => nativePaletteDrive_zero_before d Q hu)]
  rfl

def paletteForwardKernel (d ell Q : ℕ) : ℝ → ℝ :=
  arithmeticHistoryAction (paletteDivisorCoefficients Q^(ell+1)) (forwardKernel d ell)

theorem paletteForwardKernel_zero_before (d ell Q : ℕ) {t : ℝ} (ht : t<nativeCausalGap) :
    paletteForwardKernel d ell Q t=0 :=
  arithmeticHistoryAction_zero_before _ (fun _ hu => forwardKernel_zero_before d ell hu) ht

theorem zeta_power_action_forwardKernel (d ell : ℕ) (t : ℝ) :
    arithmeticHistoryAction ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^ell) (integerDriveFamily d) t=
      forwardKernel d ell t := by
  induction ell generalizing t with
  | zero => rw [pow_zero,arithmeticHistoryAction_one]; rfl
  | succ ell ih =>
    rw [pow_succ',←arithmeticHistoryAction_mul _ _ (fun _ hu => integerDriveFamily_zero_before d hu)]
    have heq : arithmeticHistoryAction ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^ell)
        (integerDriveFamily d)=forwardKernel d ell := funext ih
    rw [heq,arithmeticHistoryAction_zeta]
    rfl

theorem free_power_action_paletteForward (d ell Q : ℕ) (t : ℝ) :
    arithmeticHistoryAction (nativeFreeCoefficients Q^ell) (nativePaletteDrive d Q) t=
      paletteForwardKernel d ell Q t := by
  rw [nativePaletteDrive,arithmeticHistoryAction_mul _ _ (fun _ hu => integerDriveFamily_zero_before d hu)]
  have hcoeff : nativeFreeCoefficients Q^ell*paletteDivisorCoefficients Q=
      paletteDivisorCoefficients Q^(ell+1)*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)^ell := by
    rw [←paletteDivisor_mul_zeta,mul_pow,pow_succ]
    ring
  rw [hcoeff,←arithmeticHistoryAction_mul _ _ (fun _ hu => integerDriveFamily_zero_before d hu)]
  have heq : arithmeticHistoryAction ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^ell)
      (integerDriveFamily d)=forwardKernel d ell := funext (zeta_power_action_forwardKernel d ell)
  rw [heq]
  rfl

theorem balancedField_absorbed (d r Q : ℕ) (Y : ℝ) (t : ℝ) :
    balancedField d r Q Y t=
      arithmeticHistoryAction (nativeLargeCoefficients Q Y^r) (paletteForwardKernel d (r-1) Q) t := by
  change arithmeticHistoryAction (nativeLargeCoefficients Q Y^r*nativeFreeCoefficients Q^(r-1))
    (nativePaletteDrive d Q) t=_
  rw [←arithmeticHistoryAction_mul _ _ (fun _ hu => nativePaletteDrive_zero_before d Q hu)]
  have heq : arithmeticHistoryAction (nativeFreeCoefficients Q^(r-1)) (nativePaletteDrive d Q)=
      paletteForwardKernel d (r-1) Q := funext (free_power_action_paletteForward d (r-1) Q)
  rw [heq]

theorem logSlack_corridor_product (r : ℕ) (hr : 1≤r) (K T : ℝ) :
    logSlackZ r K T*logSlackY r K T^(r-1)=Real.exp (T-nativeCausalGap) := by
  have hrne : (r:ℝ)≠0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hr)
  have hcast : ((r-1:ℕ):ℝ)=(r:ℝ)-1 := by rw [Nat.cast_sub hr,Nat.cast_one]
  rw [logSlackY,logSlackZ,←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  rw [hcast]
  field_simp
  ring

theorem logSlack_tuple_upper_bound (r : ℕ) (hr : 1≤r) (K T : ℝ)
    (_hY : 1≤logSlackY r K T) (w : Fin r → ℕ)
    (hw : ∀ i, logSlackY r K T<(w i:ℝ))
    (hprod : (∏ i, (w i:ℝ))≤Real.exp (T-nativeCausalGap)) (j : Fin r) :
    (w j:ℝ)≤logSlackZ r K T := by
  have hother : logSlackY r K T^(r-1)≤∏ i∈(univ.erase j), (w i:ℝ) := by
    calc
      _ = ∏ _i∈(univ.erase j), logSlackY r K T := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => (logSlackY_pos r K T).le) (fun i _ => (hw i).le)
  have hfactor : (w j:ℝ)*logSlackY r K T^(r-1)≤∏ i, (w i:ℝ) := by
    calc
      _ ≤ (w j:ℝ)*(∏ i∈univ.erase j, (w i:ℝ)) :=
        mul_le_mul_of_nonneg_left hother (Nat.cast_nonneg _)
      _ = _ := by rw [mul_comm,Finset.prod_erase_mul _ _ (mem_univ j)]
  apply (mul_le_mul_iff_left₀ (pow_pos (logSlackY_pos r K T) (r-1))).mp
  exact hfactor.trans (hprod.trans_eq (logSlack_corridor_product r hr K T).symm)

theorem arithmeticHistoryAction_palette_finite (Q : ℕ) (hQ : 0<Q)
    (f : ℝ → ℝ) (t : ℝ) :
    arithmeticHistoryAction (paletteDivisorCoefficients Q) f t=
      ∑ n∈Q.divisors, moebiusPaletteCoefficient n*f (t-Real.log n) := by
  calc
    _ = ∑ n∈Q.divisors, paletteDivisorCoefficients Q n/Real.sqrt (n:ℝ)*f (t-Real.log n) := by
      apply tsum_eq_sum
      intro n hn
      have hnd : ¬n∣Q := by
        intro hdiv
        exact hn (Nat.mem_divisors.mpr ⟨hdiv,hQ.ne'⟩)
      simp [paletteDivisorCoefficients,hnd]
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      simp [paletteDivisorCoefficients,Nat.dvd_of_mem_divisors hn,moebiusPaletteCoefficient]

theorem moebiusPaletteCoefficient_abs_le_one (n : ℕ) (hn : 0<n) :
    |moebiusPaletteCoefficient n|≤1 := by
  have hmu : |(ArithmeticFunction.moebius n:ℝ)|≤1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hnreal : (1:ℝ)≤n := by exact_mod_cast hn
  have hsqrt : 1≤Real.sqrt (n:ℝ) := by simpa using Real.sqrt_le_sqrt hnreal
  rw [moebiusPaletteCoefficient,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hn))).mpr
  simpa using hmu.trans hsqrt

theorem palette_absolute_mass_le (Q : ℕ) :
    (∑ n∈Q.divisors, |moebiusPaletteCoefficient n|)≤(Q:ℝ) := by
  have hsub : Q.divisors⊆Finset.Icc 1 Q := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hn,Nat.divisor_le hn⟩
  have hcard : (Q.divisors.card:ℝ)≤Q := by
    exact_mod_cast (show Q.divisors.card≤Q by simpa using Finset.card_le_card hsub)
  calc
    _ ≤ ∑ _n∈Q.divisors, (1:ℝ) := sum_le_sum fun n hn =>
      moebiusPaletteCoefficient_abs_le_one n (Nat.pos_of_mem_divisors hn)
    _ = (Q.divisors.card:ℝ) := by simp
    _ ≤ _ := hcard

theorem squarefreePaletteCost_le (Q : ℕ) (hQ : Squarefree Q) : squarefreePaletteCost Q≤(Q:ℝ) := by
  rw [←squarefree_palette_absolute_cost Q hQ]
  exact palette_absolute_mass_le Q

def balancedTupleHistory (d r Q : ℕ) (Y Z T t : ℝ) : ℝ :=
  ∑ n∈range (Nat.floor (Real.exp (T-nativeCausalGap))+1),
    ∑ w∈(Nat.finMulAntidiag r n).filter (fun w =>
      ∀ i, Y<(w i:ℝ) ∧ (w i:ℝ)≤Z ∧ Nat.Coprime (w i) Q),
      (∏ i, (ArithmeticFunction.moebius (w i):ℝ))/Real.sqrt (n:ℝ)*
        paletteForwardKernel d (r-1) Q (t-Real.log n)

theorem large_coefficient_coprime (Q : ℕ) (Y : ℝ) (n : ℕ)
    (hn : nativeLargeCoefficients Q Y n≠0) : Nat.Coprime n Q := by
  by_contra h
  apply hn
  simp [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,h]

theorem balancedField_eq_tuple_history (d r Q : ℕ) (hr : 1≤r) (K T : ℝ)
    (hY : 1≤logSlackY r K T) {t : ℝ} (ht : t≤T) :
    balancedField d r Q (logSlackY r K T) t=
      balancedTupleHistory d r Q (logSlackY r K T) (logSlackZ r K T) T t := by
  rw [balancedField_absorbed,arithmeticHistoryAction_history _
    (fun _ hu => paletteForwardKernel_zero_before d (r-1) Q hu) ht]
  apply sum_congr rfl
  intro n hn
  rw [dirichlet_power_tuple_expansion,Finset.sum_div,Finset.sum_mul]
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro w hw
  by_cases hgood : ∀ i, logSlackY r K T<(w i:ℝ) ∧
      (w i:ℝ)≤logSlackZ r K T ∧ Nat.Coprime (w i) Q
  · rw [if_pos hgood]
    congr 2
    apply prod_congr rfl
    intro i _
    simp [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,(hgood i).1,(hgood i).2.2]
  · rw [if_neg hgood]
    have hpzero : (∏ i, nativeLargeCoefficients Q (logSlackY r K T) (w i))=0 := by
      by_contra hp
      have hcoord (i : Fin r) : nativeLargeCoefficients Q (logSlackY r K T) (w i)≠0 :=
        prod_ne_zero_iff.mp hp i (mem_univ _)
      have hlarge (i : Fin r) : logSlackY r K T<(w i:ℝ) :=
        large_coefficients_support Q _ _ (hcoord i)
      have hnle : (n:ℝ)≤Real.exp (T-nativeCausalGap) := by
        have hn' : n≤Nat.floor (Real.exp (T-nativeCausalGap)) := by
          have := Finset.mem_range.mp hn
          omega
        have hcast : (n:ℝ)≤Nat.floor (Real.exp (T-nativeCausalGap)) := by exact_mod_cast hn'
        exact hcast.trans (Nat.floor_le (Real.exp_nonneg _))
      have hprod : (∏ i, (w i:ℝ))≤Real.exp (T-nativeCausalGap) := by
        rw [←Nat.cast_prod,Nat.prod_eq_of_mem_finMulAntidiag hw]
        exact hnle
      apply hgood
      intro i
      exact ⟨hlarge i,logSlack_tuple_upper_bound r hr K T hY w hlarge hprod i,
        large_coefficient_coprime Q _ _ (hcoord i)⟩
    rw [hpzero,zero_div,zero_mul]

theorem arithmeticHistoryAction_smul (c : ℝ) (a : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    {g : ℝ} (hf : ∀ u<g, f u=0) (t : ℝ) :
    arithmeticHistoryAction (c•a) f t=c*arithmeticHistoryAction a f t := by
  rw [arithmeticHistoryAction_history _ hf le_rfl,arithmeticHistoryAction_history _ hf le_rfl,mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [ArithmeticFunction.smul_map,smul_eq_mul]
  ring

theorem arithmeticHistoryAction_sum {ι : Type*} (s : Finset ι) (a : ι → ArithmeticFunction ℝ)
    {f : ℝ → ℝ} {g : ℝ} (hf : ∀ u<g, f u=0) (t : ℝ) :
    arithmeticHistoryAction (∑ i∈s, a i) f t=∑ i∈s, arithmeticHistoryAction (a i) f t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [arithmeticHistoryAction,realWeightedLogTranslate]
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,
      arithmeticHistoryAction_add _ _ hf,ih]

theorem typeIField_expansion (d r Q : ℕ) (Y t : ℝ) :
    typeIField d r Q Y t=
      ∑ i∈range r, ((-1:ℝ)^i*(r.choose (i+1):ℝ))*
        arithmeticHistoryAction (nativeSmallCoefficients Q Y^(i+1)) (paletteForwardKernel d i Q) t := by
  rw [typeIField,typeICoefficients,nativeSieveCoefficients,
    arithmeticHistoryAction_sum _ _ (fun _ hu => nativePaletteDrive_zero_before d Q hu)]
  apply sum_congr rfl
  intro i _
  rw [arithmeticHistoryAction_smul _ _ (fun _ hu => nativePaletteDrive_zero_before d Q hu)]
  congr 1
  rw [←arithmeticHistoryAction_mul _ _ (fun _ hu => nativePaletteDrive_zero_before d Q hu)]
  have heq : arithmeticHistoryAction (nativeFreeCoefficients Q^i) (nativePaletteDrive d Q)=
      paletteForwardKernel d i Q := funext (free_power_action_paletteForward d i Q)
  rw [heq]

theorem logSlackY_eventually_ge_one (r : ℕ) (hr : 0<r) (K : ℝ) :
    ∀ᶠ T : ℝ in atTop, 1≤logSlackY r K T := by
  have hlog : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hlim := hlog.const_mul K
  have hsmall : ∀ᶠ T : ℝ in atTop, K*(Real.log T/T)<1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with T hK hT
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hrpos : (0:ℝ)<r := by exact_mod_cast hr
  have hKT : K*Real.log T<T := by
    rw [←mul_div_assoc] at hK
    simpa only [one_mul] using (div_lt_iff₀ hTpos).mp hK
  dsimp [logSlackY]
  apply Real.one_le_exp_iff.mpr
  have hdiv : T/(r:ℝ)-(K/(r:ℝ))*Real.log T=(T-K*Real.log T)/(r:ℝ) := by ring
  rw [hdiv]
  exact div_nonneg (sub_nonneg.mpr hKT.le) hrpos.le

/-- The exact product constraint is obtained from the actual causal forward
kernel; it is not an additional selection assumption. -/
theorem balanced_tuple_nonzero_product_bound (d r Q n : ℕ) (t : ℝ)
    (w : Fin r → ℕ) (hw : w∈Nat.finMulAntidiag r n)
    (hterm : (∏ i, (ArithmeticFunction.moebius (w i):ℝ))/Real.sqrt (n:ℝ)*
      paletteForwardKernel d (r-1) Q (t-Real.log n)≠0) :
    (∏ i, (w i:ℝ))≤Real.exp (t-nativeCausalGap) := by
  rw [←Nat.cast_prod,Nat.prod_eq_of_mem_finMulAntidiag hw]
  by_contra h
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_finMulAntidiag.mp hw).2
  have hlog : t-nativeCausalGap<Real.log (n:ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).mpr (lt_of_not_ge h)
  apply hterm
  rw [paletteForwardKernel_zero_before d (r-1) Q (by linarith),mul_zero]

/-- The full real-cutoff logarithmic-slack decomposition. The palette is
quantified after the horizon and is frozen throughout its entire window. -/
theorem log_slack_native_decomposition (r d : ℕ) (hr : 2≤r) (_hd : r-1≤d)
    (C eta K : ℝ) (_hC : 1<C) (_heta : 0≤eta)
    (_hK : C+(r:ℝ)*eta+2*(r:ℝ)<K) :
    ∃ T0 : ℝ, 1≤T0 ∧ ∀ T : ℝ, T0≤T → ∀ Q : ℕ, Squarefree Q → (Q:ℝ)≤T^eta →
      ∀ t∈Icc (T-C*Real.log T) T,
        primeFieldFamily d t=typeIField d r Q (logSlackY r K T) t+
          balancedField d r Q (logSlackY r K T) t ∧
        balancedField d r Q (logSlackY r K T) t=
          balancedTupleHistory d r Q (logSlackY r K T) (logSlackZ r K T) T t ∧
        (∀ n : ℕ, ∀ w∈Nat.finMulAntidiag r n,
          (∏ i, (ArithmeticFunction.moebius (w i):ℝ))/Real.sqrt (n:ℝ)*
            paletteForwardKernel d (r-1) Q (t-Real.log n)≠0 →
          (∏ i, (w i:ℝ))≤Real.exp (t-nativeCausalGap)) := by
  obtain ⟨T0,hT0⟩ := eventually_atTop.1 (logSlackY_eventually_ge_one r (by omega) K)
  refine ⟨max 1 T0,le_max_left _ _,fun T hT Q _ _ t ht => ?_⟩
  have hY := hT0 T ((le_max_right 1 T0).trans hT)
  exact ⟨native_balanced_physical_identity d r Q hr _ hY t,
    balancedField_eq_tuple_history d r Q (by omega) K T hY ht.2,
    fun n w hw hterm => balanced_tuple_nonzero_product_bound d r Q n t w hw hterm⟩

def finiteLogTranslate (s : Finset ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n∈s, c n*f (t-Real.log n)

def finiteLogTranslateIterate (s : Finset ℕ) (c : ℕ → ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0,f => f
  | i+1,f => finiteLogTranslate s c (finiteLogTranslateIterate s c i f)

/-- A finite-delay estimate. Its only inputs describe the finite operator and
the original source on a lower half-line; every iterate's estimate is proved. -/
theorem finiteLogTranslateIterate_bound (s : Finset ℕ) (c : ℕ → ℝ)
    (L M : ℝ) (hM : 0≤M) (hdelay : ∀ n∈s, Real.log (n:ℝ)≤L)
    (hmass : (∑ n∈s, |c n|)≤M) (f : ℝ → ℝ) (S B : ℝ) (hB : 0≤B)
    (hf : ∀ u : ℝ, S≤u → |f u|≤B) (i : ℕ) (t : ℝ)
    (ht : S+(i:ℝ)*L≤t) : |finiteLogTranslateIterate s c i f t|≤M^i*B := by
  induction i generalizing t with
  | zero => simpa [finiteLogTranslateIterate] using hf t (by simpa using ht)
  | succ i ih =>
    change |∑ n∈s, c n*finiteLogTranslateIterate s c i f (t-Real.log n)|≤M^(i+1)*B
    calc
      _ ≤ ∑ n∈s, |c n*finiteLogTranslateIterate s c i f (t-Real.log n)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n∈s, |c n| *(M^i*B) := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left (ih _ ?_) (abs_nonneg _)
        have hd := hdelay n hn
        push_cast at ht
        nlinarith
      _ = (∑ n∈s, |c n|)*(M^i*B) := (sum_mul _ _ _).symm
      _ ≤ M*(M^i*B) := mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem arithmeticHistoryAction_small_finite (Q : ℕ) {Y : ℝ} (_hY : 1≤Y)
    (f : ℝ → ℝ) (t : ℝ) :
    arithmeticHistoryAction (nativeSmallCoefficients Q Y) f t=
      finiteLogTranslate (Finset.Icc 1 (Nat.floor Y))
        (fun n => nativeSmallCoefficients Q Y n/Real.sqrt (n:ℝ)) f t := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n=0
  · subst n; simp
  have hncast : Y<(n:ℝ) := by
    have hfloor : Nat.floor Y<n := by
      have hcases := not_and_or.mp (show ¬(1≤n ∧ n≤Nat.floor Y) by simpa only [Finset.mem_Icc] using hn)
      rcases hcases with h1 | h2
      · exact False.elim (h1 (Nat.one_le_iff_ne_zero.mpr hn0))
      · omega
    exact Nat.lt_of_floor_lt hfloor
  simp [nativeSmallCoefficients,not_le_of_gt hncast]

theorem nativeSmallCoefficients_abs_le_one (Q : ℕ) (Y : ℝ) (n : ℕ) :
    |nativeSmallCoefficients Q Y n|≤1 := by
  change |if (n:ℝ)≤Y then (if Nat.Coprime n Q then (ArithmeticFunction.moebius n:ℝ) else 0) else 0|≤1
  by_cases hn : (n:ℝ)≤Y
  · rw [if_pos hn]
    by_cases hQ : Nat.Coprime n Q
    · rw [if_pos hQ]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    · simp [hQ]
  · simp [hn]

theorem small_coefficient_absolute_mass_le (Q : ℕ) {Y : ℝ} (hY : 1≤Y) :
    (∑ n∈Finset.Icc 1 (Nat.floor Y), |nativeSmallCoefficients Q Y n/Real.sqrt (n:ℝ)|)≤
      2*Real.sqrt Y := by
  calc
    _ ≤ ∑ n∈Finset.Icc 1 (Nat.floor Y), (Real.sqrt (n:ℝ))⁻¹ := by
      apply sum_le_sum
      intro n _
      rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _),←one_div]
      exact div_le_div_of_nonneg_right (nativeSmallCoefficients_abs_le_one Q Y n) (Real.sqrt_nonneg _)
    _ ≤ 2*Real.sqrt (Nat.floor Y:ℝ) := inverse_sqrt_partial_sum_le _
    _ ≤ _ := by gcongr; exact Nat.floor_le (by linarith)

theorem arithmeticHistoryAction_small_power_iterate (Q : ℕ) {Y : ℝ} (hY : 1≤Y)
    {f : ℝ → ℝ} {g : ℝ} (hf : ∀ u<g, f u=0) (i : ℕ) (t : ℝ) :
    arithmeticHistoryAction (nativeSmallCoefficients Q Y^i) f t=
      finiteLogTranslateIterate (Finset.Icc 1 (Nat.floor Y))
        (fun n => nativeSmallCoefficients Q Y n/Real.sqrt (n:ℝ)) i f t := by
  induction i generalizing t with
  | zero => rw [pow_zero,arithmeticHistoryAction_one]; rfl
  | succ i ih =>
    rw [pow_succ',←arithmeticHistoryAction_mul _ _ hf]
    rw [show arithmeticHistoryAction (nativeSmallCoefficients Q Y^i) f=
      finiteLogTranslateIterate (Finset.Icc 1 (Nat.floor Y))
        (fun n => nativeSmallCoefficients Q Y n/Real.sqrt (n:ℝ)) i f from funext ih]
    exact arithmeticHistoryAction_small_finite Q hY _ _

theorem arithmeticHistoryAction_palette_power_iterate (Q : ℕ) (hQ : 0<Q)
    {f : ℝ → ℝ} {g : ℝ} (hf : ∀ u<g, f u=0) (i : ℕ) (t : ℝ) :
    arithmeticHistoryAction (paletteDivisorCoefficients Q^i) f t=
      finiteLogTranslateIterate Q.divisors moebiusPaletteCoefficient i f t := by
  induction i generalizing t with
  | zero => rw [pow_zero,arithmeticHistoryAction_one]; rfl
  | succ i ih =>
    rw [pow_succ',←arithmeticHistoryAction_mul _ _ hf]
    rw [show arithmeticHistoryAction (paletteDivisorCoefficients Q^i) f=
      finiteLogTranslateIterate Q.divisors moebiusPaletteCoefficient i f from funext ih]
    exact arithmeticHistoryAction_palette_finite Q hQ _ _

theorem small_filter_log_delay (_Q : ℕ) {Y : ℝ} (hY : 1≤Y) :
    ∀ n∈Finset.Icc 1 (Nat.floor Y), Real.log (n:ℝ)≤Real.log Y := by
  intro n hn
  obtain ⟨hnpos,hnle⟩ := Finset.mem_Icc.mp hn
  apply Real.log_le_log (by exact_mod_cast hnpos)
  have hcast : (n:ℝ)≤Nat.floor Y := by exact_mod_cast hnle
  exact hcast.trans (Nat.floor_le (by linarith))

theorem palette_filter_log_delay (Q : ℕ) :
    ∀ n∈Q.divisors, Real.log (n:ℝ)≤Real.log (Q:ℝ) := by
  intro n hn
  exact Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors hn)
    (by exact_mod_cast Nat.divisor_le hn)

theorem logSlack_total_delay_bound (r : ℕ) (hr : 0<r) (C eta K T : ℝ)
    (hT : 1≤T) (Q : ℕ) (hQ : 0<Q) (hQbudget : (Q:ℝ)≤T^eta)
    (hY : 1≤logSlackY r K T) (i : ℕ) (hi : i≤r)
    (t : ℝ) (ht : T-C*Real.log T≤t) :
    (K-C-(r:ℝ)*eta)*Real.log T+
      (i:ℝ)*Real.log (Q:ℝ)+(i:ℝ)*Real.log (logSlackY r K T)≤t := by
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hQpos : (0:ℝ)<Q := by exact_mod_cast hQ
  have hlogQ : Real.log (Q:ℝ)≤eta*Real.log T := by
    have h := Real.log_le_log hQpos hQbudget
    rwa [Real.log_rpow hTpos] at h
  have hlogQ0 : 0≤Real.log (Q:ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hlogY0 : 0≤Real.log (logSlackY r K T) := Real.log_nonneg hY
  have hir : (i:ℝ)≤r := by exact_mod_cast hi
  have hdelay : (i:ℝ)*Real.log (logSlackY r K T)+(i:ℝ)*Real.log (Q:ℝ)≤
      (r:ℝ)*Real.log (logSlackY r K T)+(r:ℝ)*Real.log (Q:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hir hlogY0,mul_le_mul_of_nonneg_right hir hlogQ0]
  have hrne : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  have hscale : (r:ℝ)*Real.log (logSlackY r K T)=T-K*Real.log T := by
    rw [log_logSlackY]
    field_simp
  have hQscale := mul_le_mul_of_nonneg_left hlogQ (Nat.cast_nonneg (α:=ℝ) r)
  rw [hscale] at hdelay
  nlinarith

/-!
Quantitative continuation of the actual finite-history decomposition.
The native kernel estimates, palette delays and coefficient masses are
proved below; compiler and independent-consumer evidence is kept separately.
-/

/-- One positive tail budget for finitely many actual fixed-order kernels.
The order r is fixed before A and c are selected. -/
theorem forwardKernel_common_finite_tail (r d : ℕ) (hr : 0 < r)
    (hd : r - 1 ≤ d) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ ell < r, ∀ u : ℝ, 0 ≤ u →
      |forwardKernel d ell u| ≤ A * Real.exp (-c * Real.exp (u / (2 * (r : ℝ)))) := by
  have one_kernel (ell : ℕ) (hell : ell < r) :
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ u : ℝ, 0 ≤ u →
        |forwardKernel d ell u| ≤ A * Real.exp (-c * Real.exp (u / (2 * (r : ℝ)))) := by
    obtain ⟨A,c,hA,hc,hf⟩ := forwardKernel_double_exp_decay d ell 0 (by omega)
    refine ⟨A,c,hA,hc,fun u hu => ?_⟩
    have hden : 2 * ((ell : ℝ) + 1) ≤ 2 * (r : ℝ) := by
      have h : ell + 1 ≤ r := by omega
      exact_mod_cast (Nat.mul_le_mul_left 2 h)
    have hexp : Real.exp (u / (2 * (r : ℝ))) ≤
        Real.exp (u / (2 * ((ell : ℝ) + 1))) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hu (by positivity) hden)
    calc
      _ ≤ A * Real.exp (-c * Real.exp (u / (2 * ((ell : ℝ) + 1)))) := by
        simpa only [iteratedDeriv_zero] using hf u hu
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hexp (neg_nonpos.mpr hc.le))) hA.le
  have finite_family (s : Finset ℕ) : (∀ i ∈ s, i < r) →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ i ∈ s, ∀ u : ℝ, 0 ≤ u →
        |forwardKernel d i u| ≤ A * Real.exp (-c * Real.exp (u / (2 * (r : ℝ)))) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1,1,by norm_num,by norm_num,?_⟩
      simp
    | @insert i s hi ih =>
      intro hs
      obtain ⟨A,c,hA,hc,hf⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
      obtain ⟨Ai,ci,hAi,hci,hfi⟩ := one_kernel i (hs i (Finset.mem_insert_self i s))
      refine ⟨A+Ai,min c ci,add_pos hA hAi,lt_min hc hci,?_⟩
      intro j hj u hu
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        calc
          _ ≤ Ai * Real.exp (-ci * Real.exp (u / (2 * (r : ℝ)))) := hfi u hu
          _ ≤ (A+Ai) * Real.exp (-(min c ci) * Real.exp (u / (2 * (r : ℝ)))) := by
            apply mul_le_mul (by linarith) _ (Real.exp_nonneg _) (by positivity)
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right c ci)) (Real.exp_nonneg _)
      · calc
          _ ≤ A * Real.exp (-c * Real.exp (u / (2 * (r : ℝ)))) := hf j hjs u hu
          _ ≤ (A+Ai) * Real.exp (-(min c ci) * Real.exp (u / (2 * (r : ℝ)))) := by
            apply mul_le_mul (by linarith) _ (Real.exp_nonneg _) (by positivity)
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left c ci)) (Real.exp_nonneg _)
  obtain ⟨A,c,hA,hc,hf⟩ := finite_family (Finset.range r)
    (fun i hi => Finset.mem_range.mp hi)
  exact ⟨A,c,hA,hc,fun ell hell => hf ell (Finset.mem_range.mpr hell)⟩

/-- Both finite filters are estimated on the actual delayed lower half-line.
This general operator helper has a tail premise. The primary theorem below
proves that premise from the actual forward kernel, rather than assuming it. -/
theorem small_palette_block_tail_bound (d ell Q : ℕ) (hQ : 0 < Q)
    {Y : ℝ} (hY : 1 ≤ Y) (S B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ u : ℝ, S ≤ u → |forwardKernel d ell u| ≤ B)
    (t : ℝ) (ht : S + ((ell+1 : ℕ) : ℝ)*Real.log (Q : ℝ) +
      ((ell+1 : ℕ) : ℝ)*Real.log Y ≤ t) :
    |arithmeticHistoryAction (nativeSmallCoefficients Q Y^(ell+1))
      (paletteForwardKernel d ell Q) t| ≤
      (2*Real.sqrt Y)^(ell+1) * ((Q : ℝ)^(ell+1)*B) := by
  have hp (u : ℝ) (hu : S + ((ell+1 : ℕ) : ℝ)*Real.log (Q : ℝ) ≤ u) :
      |paletteForwardKernel d ell Q u| ≤ (Q : ℝ)^(ell+1)*B := by
    rw [paletteForwardKernel,arithmeticHistoryAction_palette_power_iterate Q hQ
      (fun v hv => forwardKernel_zero_before d ell hv)]
    exact finiteLogTranslateIterate_bound Q.divisors moebiusPaletteCoefficient
      (Real.log (Q : ℝ)) (Q : ℝ) (Nat.cast_nonneg Q)
      (palette_filter_log_delay Q) (palette_absolute_mass_le Q)
      (forwardKernel d ell) S B hB hf (ell+1) u hu
  rw [arithmeticHistoryAction_small_power_iterate Q hY
    (fun v hv => paletteForwardKernel_zero_before d ell Q hv)]
  exact finiteLogTranslateIterate_bound (Finset.Icc 1 (Nat.floor Y))
    (fun n => nativeSmallCoefficients Q Y n / Real.sqrt (n : ℝ))
    (Real.log Y) (2*Real.sqrt Y) (by positivity)
    (small_filter_log_delay Q hY) (small_coefficient_absolute_mass_le Q hY)
    (paletteForwardKernel d ell Q)
    (S + ((ell+1 : ℕ) : ℝ)*Real.log (Q : ℝ)) ((Q : ℝ)^(ell+1)*B)
    (by positivity) hp (ell+1) t ht

/-- Full small-factor and palette mass, with real cutoffs. -/
theorem logSlack_filter_mass_bound (r j : ℕ) (hr : 0 < r) (hj : j ≤ r)
    (K T eta : ℝ) (hK : 0 ≤ K) (hT : 1 ≤ T) (Q : ℕ) (hQ : 0 < Q)
    (hQbudget : (Q : ℝ) ≤ T^eta) (hY : 1 ≤ logSlackY r K T) :
    (2*Real.sqrt (logSlackY r K T))^j * (Q : ℝ)^j ≤
      (2 : ℝ)^j * T^((r : ℝ)*eta) * Real.exp (T/2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hsqrtone : 1 ≤ Real.sqrt (logSlackY r K T) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hY
  have hsqrt : Real.sqrt (logSlackY r K T) =
      Real.exp ((T/(r:ℝ)-(K/(r:ℝ))*Real.log T)/2) := by
    unfold logSlackY
    rw [show Real.exp (T/(r:ℝ)-(K/(r:ℝ))*Real.log T) =
      Real.exp ((T/(r:ℝ)-(K/(r:ℝ))*Real.log T)/2) *
      Real.exp ((T/(r:ℝ)-(K/(r:ℝ))*Real.log T)/2) by
        rw [← Real.exp_add]; congr 1; ring,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  have hYpow : Real.sqrt (logSlackY r K T)^j ≤ Real.exp (T/2) := by
    calc
      _ ≤ Real.sqrt (logSlackY r K T)^r := pow_le_pow_right₀ hsqrtone hj
      _ = Real.exp ((T-K*Real.log T)/2) := by
        rw [hsqrt,← Real.exp_nat_mul]
        congr 1
        field_simp [hrne]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hK (Real.log_nonneg hT)])
  have hQpow : (Q : ℝ)^j ≤ T^((r : ℝ)*eta) := by
    calc
      _ ≤ (Q : ℝ)^r := pow_le_pow_right₀ hQone hj
      _ ≤ (T^eta)^r := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQbudget r
      _ = _ := by
        simp only [Real.rpow_def_of_pos hTpos,← Real.exp_nat_mul]
        congr 1
        ring
  calc
    _ = (2 : ℝ)^j * (Real.sqrt (logSlackY r K T)^j * (Q : ℝ)^j) := by rw [mul_pow]; ring
    _ ≤ (2 : ℝ)^j * (Real.exp (T/2) * T^((r : ℝ)*eta)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hYpow hQpow (by positivity) (Real.exp_nonneg _)
    _ = _ := by ring

/-- Full original Type I target. The witnesses are chosen before T and Q.
The native forward bound, both filter costs and the complete palette delay
are discharged internally; no native estimate is added as a premise. -/
theorem log_slack_typeI_error (r d : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d)
    (C eta K : ℝ) (hC : 1 < C) (heta : 0 ≤ eta)
    (hK : C+(r:ℝ)*eta+2*(r:ℝ) < K) :
    ∃ C1 c T0 : ℝ, 0 < C1 ∧ 0 < c ∧ 1 ≤ T0 ∧
      1 < (K-C-(r:ℝ)*eta)/(2*(r:ℝ)) ∧
      ∀ T : ℝ, T0 ≤ T → ∀ Q : ℕ, Squarefree Q → (Q:ℝ) ≤ T^eta →
        ∀ t ∈ Icc (T-C*Real.log T) T,
          |typeIField d r Q (logSlackY r K T) t| ≤
            C1 * T^((r:ℝ)*eta) *
              Real.exp (T/2-c*T^((K-C-(r:ℝ)*eta)/(2*(r:ℝ)))) := by
  classical
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hKpos : 0 < K := by nlinarith [mul_nonneg hrpos.le heta]
  have hW : 0 < K-C-(r:ℝ)*eta := by linarith
  have hp : 1 < (K-C-(r:ℝ)*eta)/(2*(r:ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨A,c,hA,hc,hkernel⟩ := forwardKernel_common_finite_tail r d (by omega) hd
  let Wsum : ℝ := ∑ i ∈ Finset.range r, (r.choose (i+1):ℝ)*(2:ℝ)^(i+1)
  have hWsum : 0 ≤ Wsum := Finset.sum_nonneg (fun i hi => by positivity)
  obtain ⟨Ty,hTy⟩ := eventually_atTop.1 (logSlackY_eventually_ge_one r (by omega) K)
  refine ⟨1+A*Wsum,c,max 1 Ty,by positivity,hc,le_max_left _ _,hp,?_⟩
  intro T hT Q hQsf hQbudget t ht
  have hT1 : 1 ≤ T := (le_max_left 1 Ty).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hY : 1 ≤ logSlackY r K T := hTy T ((le_max_right 1 Ty).trans hT)
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQsf.ne_zero
  let S : ℝ := (K-C-(r:ℝ)*eta)*Real.log T
  let p : ℝ := (K-C-(r:ℝ)*eta)/(2*(r:ℝ))
  let B : ℝ := A*Real.exp (-c*T^p)
  have hS : 0 ≤ S := mul_nonneg hW.le (Real.log_nonneg hT1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpower : Real.exp (S/(2*(r:ℝ))) = T^p := by
    rw [Real.rpow_def_of_pos hTpos]
    congr 1
    dsimp [S,p]
    ring
  have htail (i : ℕ) (hi : i < r) : ∀ u : ℝ, S ≤ u → |forwardKernel d i u| ≤ B := by
    intro u hu
    have hexp : T^p ≤ Real.exp (u/(2*(r:ℝ))) := by
      rw [←hpower]
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right hu (by positivity)
    calc
      _ ≤ A*Real.exp (-c*Real.exp (u/(2*(r:ℝ)))) := hkernel i hi u (hS.trans hu)
      _ ≤ B := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hexp (neg_nonpos.mpr hc.le))) hA.le
  have hblock (i : ℕ) (hi : i ∈ Finset.range r) :
      |arithmeticHistoryAction (nativeSmallCoefficients Q (logSlackY r K T)^(i+1))
        (paletteForwardKernel d i Q) t| ≤
        (2:ℝ)^(i+1) * T^((r:ℝ)*eta) * Real.exp (T/2) * B := by
    have hil : i < r := Finset.mem_range.mp hi
    have hdelay := logSlack_total_delay_bound r (by omega) C eta K T hT1 Q hQpos
      hQbudget hY (i+1) (by omega) t ht.1
    have hfirst := small_palette_block_tail_bound d i Q hQpos hY S B hB (htail i hil) t hdelay
    have hmass := logSlack_filter_mass_bound r (i+1) (by omega) (by omega)
      K T eta hKpos.le hT1 Q hQpos hQbudget hY
    calc
      _ ≤ (2*Real.sqrt (logSlackY r K T))^(i+1)*((Q:ℝ)^(i+1)*B) := hfirst
      _ = ((2*Real.sqrt (logSlackY r K T))^(i+1)*(Q:ℝ)^(i+1))*B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hB
  rw [typeIField_expansion d r Q (logSlackY r K T) t]
  calc
    _ ≤ ∑ i ∈ Finset.range r,
        |((-1:ℝ)^i*(r.choose (i+1):ℝ))*
          arithmeticHistoryAction (nativeSmallCoefficients Q (logSlackY r K T)^(i+1))
            (paletteForwardKernel d i Q) t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range r, (r.choose (i+1):ℝ)*
        ((2:ℝ)^(i+1)*T^((r:ℝ)*eta)*Real.exp (T/2)*B) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (r.choose (i+1)))]
      exact mul_le_mul_of_nonneg_left (hblock i hi) (Nat.cast_nonneg _)
    _ = A*Wsum*T^((r:ℝ)*eta)*Real.exp (T/2-c*T^p) := by
      have he (i : ℕ) :
          (r.choose (i+1):ℝ)*((2:ℝ)^(i+1)*T^((r:ℝ)*eta)*Real.exp (T/2)*B) =
          ((r.choose (i+1):ℝ)*(2:ℝ)^(i+1))*
            (A*T^((r:ℝ)*eta)*Real.exp (T/2-c*T^p)) := by
        have hexp : Real.exp (T/2) * Real.exp (-c*T^p) =
            Real.exp (T/2-c*T^p) := by
          rw [← Real.exp_add]
          congr 1
          ring
        dsimp [B]
        calc
          _ = ((r.choose (i+1):ℝ)*(2:ℝ)^(i+1)) *
              (A*T^((r:ℝ)*eta)*(Real.exp (T/2)*Real.exp (-c*T^p))) := by ring
          _ = _ := by rw [hexp]
      simp_rw [he]
      rw [←Finset.sum_mul]
      dsimp [Wsum]
      ring
    _ ≤ (1+A*Wsum)*T^((r:ℝ)*eta)*Real.exp (T/2-c*T^p) := by
      gcongr
      linarith

/-- The fixed two-factor instance uses the actual order-one source Pj.
The real cutoff identities, signed tuple representation, causal product
restriction and complete window error are all retained. -/
theorem fixed_two_factor_preparation :
    ∃ C1 c T0 : ℝ, 0 < C1 ∧ 0 < c ∧ 1 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ t ∈ Icc (T-2*Real.log T) T,
        logSlackY 2 8 T = Real.exp (T/2)*T^(-4:ℝ) ∧
        logSlackZ 2 8 T = Real.exp (T/2-nativeCausalGap)*T^(4:ℝ) ∧
        primeFieldFamily 1 t = typeIField 1 2 1 (logSlackY 2 8 T) t +
          balancedField 1 2 1 (logSlackY 2 8 T) t ∧
        balancedField 1 2 1 (logSlackY 2 8 T) t =
          balancedTupleHistory 1 2 1 (logSlackY 2 8 T) (logSlackZ 2 8 T) T t ∧
        |typeIField 1 2 1 (logSlackY 2 8 T) t| ≤
          C1*Real.exp (T/2-c*T^(3/2:ℝ)) ∧
        (∀ n : ℕ, ∀ w ∈ Nat.finMulAntidiag 2 n,
          (∏ i, (ArithmeticFunction.moebius (w i):ℝ))/Real.sqrt (n:ℝ)*
            paletteForwardKernel 1 1 1 (t-Real.log n) ≠ 0 →
          (∏ i, (w i:ℝ)) ≤ Real.exp (t-nativeCausalGap)) := by
  obtain ⟨C1,c,Te,hC1,hc,hTe,_hp,herr⟩ :=
    log_slack_typeI_error 2 1 (by norm_num) (by norm_num)
      2 0 8 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Td,_hTd,hdec⟩ :=
    log_slack_native_decomposition 2 1 (by norm_num) (by norm_num)
      2 0 8 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C1,c,max Te Td,hC1,hc,hTe.trans (le_max_left _ _),?_⟩
  intro T hT t ht
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one
    (hTe.trans ((le_max_left Te Td).trans hT))
  have hq : ((1:ℕ):ℝ) ≤ T^(0:ℝ) := by simp
  have hdecT := hdec T ((le_max_right Te Td).trans hT) 1 (by simp) hq t ht
  have herrT := herr T ((le_max_left Te Td).trans hT) 1 (by simp) hq t ht
  have hY : logSlackY 2 8 T = Real.exp (T/2)*T^(-4:ℝ) := by
    convert logSlackY_eq_paper 2 8 hTpos using 1; norm_num
  have hZ : logSlackZ 2 8 T = Real.exp (T/2-nativeCausalGap)*T^(4:ℝ) := by
    convert logSlackZ_eq_paper 2 8 hTpos using 1; norm_num
  norm_num at herrT
  exact ⟨hY,hZ,hdecT.1,hdecT.2.1,herrT,hdecT.2.2⟩

end Zeta23.OPICAFollowup
