import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.L2Space
import Zeta23.OPICAFollowup.LogSlackBalance
import Zeta23.OPICAFollowup.NormFirstTransfer
import Zeta23.OPICA.DivisorMask

/-!
Native mask supporting continuation. The actual finite mask bounds and exact
regrouping are supporting lemmas. Neither of this module's full primary roots
is claimed: the scheduled logarithmic-budget and L2/rate consumers remain
unfinished. In particular there is no Theta hypothesis here. Convolution
powers are explicitly typed as arithmetic functions before coercing to fields.
-/

set_option maxHeartbeats 800000

noncomputable section
open Finset Set MeasureTheory Filter
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA Zeta23.CCM

/-- Actual global bound, including the negative half-line via the positive
native causal gap. This is selected from the proved source theorem. -/
theorem forwardKernel_actual_bounded (d ell : ℕ) (hd : ell ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, |forwardKernel d ell t| ≤ A := by
  obtain ⟨A,c,hA,hc,hdecay⟩ := forwardKernel_double_exp_decay d ell 0 hd
  refine ⟨A,hA,fun t => ?_⟩
  by_cases ht : 0 ≤ t
  · have he : Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hc.le) (Real.exp_nonneg _))
    calc
      _ ≤ A*Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) := by
        simpa only [iteratedDeriv_zero] using hdecay t ht
      _ ≤ A := mul_le_of_le_one_right hA.le he
  · rw [forwardKernel_zero_before d ell (by linarith [nativeCausalGap_pos]),abs_zero]
    exact hA.le

def nativeForwardBoundedDrive (d ell : ℕ) (hd : ell ≤ d) : BoundedCausalDrive where
  toFun := forwardKernel d ell
  continuous := (forwardKernel_contDiff d ell).continuous
  gap := nativeCausalGap
  gap_pos := nativeCausalGap_pos
  zero_before := fun _ ht => forwardKernel_zero_before d ell ht
  bound := Classical.choose (forwardKernel_actual_bounded d ell hd)
  bound_nonneg := (Classical.choose_spec (forwardKernel_actual_bounded d ell hd)).1.le
  abs_le := (Classical.choose_spec (forwardKernel_actual_bounded d ell hd)).2

@[simp] theorem nativeForwardBoundedDrive_apply (d ell : ℕ) (hd : ell ≤ d) (t : ℝ) :
    nativeForwardBoundedDrive d ell hd t = forwardKernel d ell t := rfl

/-- Each iteration retains the actual divisor palette, including its complete
absolute mass. The index j will be 1 on the raw side and r on the absorbed side. -/
def nativePaletteDriveIterate (U : BoundedCausalDrive) (Q : ℕ) : ℕ → BoundedCausalDrive
  | 0 => U
  | j+1 => squarefreePaletteDrive (nativePaletteDriveIterate U Q j) Q

theorem nativePaletteDriveIterate_apply (U : BoundedCausalDrive) (Q j : ℕ) (t : ℝ) :
    nativePaletteDriveIterate U Q j t =
      finiteLogTranslateIterate Q.divisors moebiusPaletteCoefficient j U t := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    change (∑ n ∈ Q.divisors, moebiusPaletteCoefficient n*
      nativePaletteDriveIterate U Q j (t-Real.log n)) = _
    simp_rw [ih]
    rfl

theorem nativePaletteDriveIterate_bound (U : BoundedCausalDrive) (Q j : ℕ) :
    (nativePaletteDriveIterate U Q j).bound ≤ (Q:ℝ)^j * U.bound := by
  induction j with
  | zero => simp [nativePaletteDriveIterate]
  | succ j ih =>
    change (∑ n ∈ Q.divisors, |moebiusPaletteCoefficient n|) *
      (nativePaletteDriveIterate U Q j).bound ≤ (Q:ℝ)^(j+1)*U.bound
    calc
      _ ≤ (Q:ℝ)*((Q:ℝ)^j*U.bound) := mul_le_mul
        (palette_absolute_mass_le Q) ih
        (nativePaletteDriveIterate U Q j).bound_nonneg (Nat.cast_nonneg Q)
      _ = _ := by rw [pow_succ]; ring

def nativeRawPaletteDrive (d Q : ℕ) : BoundedCausalDrive :=
  nativePaletteDriveIterate (nativeForwardBoundedDrive d 0 (Nat.zero_le d)) Q 1

def nativeAbsorbedPaletteDrive (d r Q : ℕ) (hd : r-1 ≤ d) : BoundedCausalDrive :=
  nativePaletteDriveIterate (nativeForwardBoundedDrive d (r-1) hd) Q r

theorem nativeRawPaletteDrive_apply (d Q : ℕ) (hQ : 0 < Q) (t : ℝ) :
    nativeRawPaletteDrive d Q t = nativePaletteDrive d Q t := by
  rw [nativeRawPaletteDrive,nativePaletteDriveIterate_apply]
  rw [nativePaletteDrive,arithmeticHistoryAction_palette_finite Q hQ]
  rfl

theorem nativeAbsorbedPaletteDrive_apply (d r Q : ℕ) (hr : 1 ≤ r)
    (hd : r-1 ≤ d) (hQ : 0 < Q) (t : ℝ) :
    nativeAbsorbedPaletteDrive d r Q hd t = paletteForwardKernel d (r-1) Q t := by
  rw [nativeAbsorbedPaletteDrive,nativePaletteDriveIterate_apply,paletteForwardKernel,
    arithmeticHistoryAction_palette_power_iterate Q hQ
      (fun u hu => forwardKernel_zero_before d (r-1) hu),
    show r-1+1=r by omega]
  rfl

/-- Absorbed coefficients have their own actual r-fold divisor envelope.
This uses the public tuple identity, not inaccessible private helpers. -/
theorem nativeLargeCoefficients_power_abs_le_divisor (Q r n : ℕ) (Y : ℝ) :
    |((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) n| ≤ (divisorCount r n : ℝ) := by
  have habs (j : ℕ) : |nativeLargeCoefficients Q Y j| ≤ 1 := by
    change |if Y < (j:ℝ) then nativeInverseCoefficients Q j else 0| ≤ 1
    split_ifs with hj
    · change |if Nat.Coprime j Q then (ArithmeticFunction.moebius j:ℝ) else 0| ≤ 1
      split_ifs <;> try norm_num
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j)
    · norm_num
  rw [dirichlet_power_tuple_expansion]
  calc
    _ ≤ ∑ w ∈ Nat.finMulAntidiag r n, |∏ i, nativeLargeCoefficients Q Y (w i)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ Nat.finMulAntidiag r n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro w _
      rw [Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun i _ => abs_nonneg _)
        (fun i _ => habs (w i))
    _ = _ := by simp [divisorCount]

/-- The finite observation is precisely the native arithmetic history on the
whole horizon, including index zero and the real log delays. -/
theorem arithmeticHistoryAction_eq_finiteDrive (a : ArithmeticFunction ℝ)
    (U : BoundedCausalDrive) {T t : ℝ} (ht : t ≤ T) :
    arithmeticHistoryAction a U t = finiteDriveField U (driveIndexBound T) a t := by
  have he : arithmeticHistoryAction a U t = ∑' n : ℕ, a n*translatedDrive U n t := by
    apply tsum_congr
    intro n
    dsimp [translatedDrive]
    ring
  rw [he,drive_sum_eq_finite U a ht]
  rfl

theorem native_balanced_two_realizations (r d Q : ℕ) (hr : 2 ≤ r)
    (hd : r-1 ≤ d) (hQ : 0 < Q) (Y : ℝ) {T t : ℝ} (ht : t ≤ T) :
    finiteDriveField (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) t = balancedField d r Q Y t ∧
    finiteDriveField (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) t = balancedField d r Q Y t := by
  constructor
  · rw [←arithmeticHistoryAction_eq_finiteDrive _ _ ht]
    change arithmeticHistoryAction (balancedInverseCoefficients Q Y r)
      (fun u => nativeRawPaletteDrive d Q u) t = _
    simp_rw [nativeRawPaletteDrive_apply d Q hQ]
    rfl
  · rw [←arithmeticHistoryAction_eq_finiteDrive _ _ ht,
      balancedField_absorbed d r Q Y t]
    congr 1
    funext u
    exact nativeAbsorbedPaletteDrive_apply d r Q (by omega) hd hQ u

def nativeMovingPrimitiveCutoff (t : ℝ) : ℝ := Real.exp (Real.sqrt t)

theorem nativeMovingPrimitiveCutoff_measurable : Measurable nativeMovingPrimitiveCutoff := by
  unfold nativeMovingPrimitiveCutoff
  fun_prop

theorem nativeMovingPrimitiveCutoff_le {t T : ℝ} (ht : t ≤ T) :
    nativeMovingPrimitiveCutoff t ≤ Real.exp (Real.sqrt T) :=
  Real.exp_le_exp.mpr (Real.sqrt_le_sqrt ht)

/-- Two source-specific low-form inequalities, derived separately. They retain
all real cutoffs, actual gcd masks (including the diagonal), and full palette
mass. No equality between the two low masks is asserted. -/
theorem native_balanced_low_masks_explicit (r d Q : ℕ) (hr : 2 ≤ r)
    (hd : r-1 ≤ d) (Y H T : ℝ) (hY : 1 ≤ Y) (hT : 0 ≤ T) (hHT : H ≤ T) :
    (IntegrableOn (finiteLowPair (nativeRawPaletteDrive d Q) (driveIndexBound T)
      (balancedInverseCoefficients Q Y r) (balancedInverseCoefficients Q Y r)
      nativeMovingPrimitiveCutoff) (Icc H T) ∧
     |lowPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
       (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T)| ≤
       4*(T-H)*((Q:ℝ)*(nativeForwardBoundedDrive d 0 (Nat.zero_le d)).bound)^2 *
       Real.exp (Real.sqrt T)*(1+Real.sqrt T)^(2*(2*r-1)-2)*(1+T)^((2*r-1)*(2*r-1))) ∧
    (IntegrableOn (finiteLowPair (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
      ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ))
      nativeMovingPrimitiveCutoff) (Icc H T) ∧
     |lowPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
       ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T)| ≤
       4*(T-H)*((Q:ℝ)^r*(nativeForwardBoundedDrive d (r-1) hd).bound)^2 *
       Real.exp (Real.sqrt T)*(1+Real.sqrt T)^(2*r-2)*(1+T)^(r*r)) := by
  have hB : 1 ≤ Real.exp (Real.sqrt T) := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg T)
  have hmask : ∀ t ∈ Icc H T, nativeMovingPrimitiveCutoff t ≤ Real.exp (Real.sqrt T) :=
    fun t ht => nativeMovingPrimitiveCutoff_le ht.2
  have hx (n : ℕ) (_hn : 0 < n) :
      |balancedInverseCoefficients Q Y r n| ≤ 1*(divisorCount (2*r-1) n : ℝ) := by
    simpa only [one_mul] using (balanced_coeff_divisor_bound Q Y hY r hr n).1
  have hy (n : ℕ) (_hn : 0 < n) :
      |((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) n| ≤ 1*(divisorCount r n : ℝ) := by
    simpa only [one_mul] using nativeLargeCoefficients_power_abs_le_divisor Q r n Y
  have hU := nativePaletteDriveIterate_bound (nativeForwardBoundedDrive d 0 (Nat.zero_le d)) Q 1
  have hV := nativePaletteDriveIterate_bound (nativeForwardBoundedDrive d (r-1) hd) Q r
  simp only [pow_one] at hU
  constructor
  · constructor
    · exact finiteLowPair_integrableOn _ (2*r-1) (by omega) _ _ 1 1 _ H T
        (by norm_num) (by norm_num) hB hT hx hx _ nativeMovingPrimitiveCutoff_measurable hmask
    · have h := low_primitive_bilinear_bound (nativeRawPaletteDrive d Q)
        (2*r-1) (by omega) _ _ 1 1 _ H T (by norm_num) (by norm_num)
        hB hT hHT hx hx _ hmask
      simp only [one_mul,Real.log_exp] at h
      apply h.trans
      gcongr
      · exact (nativeRawPaletteDrive d Q).bound_nonneg
      · exact hU
  · constructor
    · exact finiteLowPair_integrableOn _ r (by omega) _ _ 1 1 _ H T
        (by norm_num) (by norm_num) hB hT hy hy _ nativeMovingPrimitiveCutoff_measurable hmask
    · have h := low_primitive_bilinear_bound (nativeAbsorbedPaletteDrive d r Q hd)
        r (by omega) _ _ 1 1 _ H T (by norm_num) (by norm_num)
        hB hT hHT hy hy _ hmask
      simp only [one_mul,Real.log_exp] at h
      apply h.trans
      gcongr
      · exact (nativeAbsorbedPaletteDrive d r Q hd).bound_nonneg
      · exact hV

/-- Exact error allocation between the two different high masks. The premise
identifying their scalar fields is discharged from the actual native actions. -/
theorem native_balanced_mask_regrouping (r d Q : ℕ) (hr : 2 ≤ r)
    (hd : r-1 ≤ d) (hQ : 0 < Q) (Y H T : ℝ)
    (hY : 1 ≤ Y) (hT : 0 ≤ T) (hHT : H ≤ T) :
    highPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T) -
      highPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T) =
    lowPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T) -
      lowPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T) := by
  obtain ⟨⟨hUL,_⟩,⟨hVL,_⟩⟩ := native_balanced_low_masks_explicit r d Q hr hd Y H T hY hT hHT
  apply mask_regrouping_difference _ _ _ _ _ _ _ _ _ measurableSet_Icc ?_
    hUL (finiteHighPair_integrableOn _ _ _ _ _ H T hUL)
    hVL (finiteHighPair_integrableOn _ _ _ _ _ H T hVL)
  intro t ht
  obtain ⟨hU,hV⟩ := native_balanced_two_realizations r d Q hr hd hQ Y ht.2
  exact hU.trans hV.symm


/-!
## Scheduled native observations (continuation at 9b6a9a3)

UNCHECKED: these new declarations have not been run through Lean in the
current environment.  Every palette remains an argument of the actual drive
at its own horizon; no fixed-drive rate theorem is used for moving palettes.
-/

/-- The literal real logarithmic window; a short initial window is allowed
and its restricted L2 space is still constructed. -/
def nativeLogWindow (C T : ℝ) : Set ℝ := Icc (T-C*Real.log T) T

def nativeRawLow (d r Q : ℕ) (Y C T : ℝ) : ℝ :=
  lowPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
    (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (nativeLogWindow C T)

def nativeAbsorbedLow (d r Q : ℕ) (hd : r-1≤d) (Y C T : ℝ) : ℝ :=
  lowPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
    ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ))
    nativeMovingPrimitiveCutoff (nativeLogWindow C T)

def nativeRawHigh (d r Q : ℕ) (Y C T : ℝ) : ℝ :=
  highPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
    (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (nativeLogWindow C T)

def nativeAbsorbedHigh (d r Q : ℕ) (hd : r-1≤d) (Y C T : ℝ) : ℝ :=
  highPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
    ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ))
    nativeMovingPrimitiveCutoff (nativeLogWindow C T)

def nativePhysicalWindowEnergy (d : ℕ) (C T : ℝ) : ℝ :=
  ∫ t in nativeLogWindow C T, (primeFieldFamily d t)^2

lemma nativeLogWindow_volume {C T : ℝ} (hC : 0≤C) (hT : 1≤T) :
    volume.real (nativeLogWindow C T)=C*Real.log T := by
  have hlen : 0≤C*Real.log T := mul_nonneg hC (Real.log_nonneg hT)
  unfold nativeLogWindow
  rw [Real.volume_real_Icc_of_le (sub_le_self _ hlen)]
  ring

lemma scheduled_log_div_time (τ : HorizonSchedule) :
    Tendsto (fun n => Real.log (τ.time n)/(τ.time n)) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  exact h.comp τ.cofinal

lemma scheduled_sqrt_div_time (τ : HorizonSchedule) :
    Tendsto (fun n => Real.sqrt (τ.time n)/(τ.time n)) atTop (𝓝 0) := by
  have h := (Real.tendsto_sqrt_atTop.comp τ.cofinal).inv_tendsto_atTop
  apply h.congr
  intro n
  have hs := Real.sqrt_pos.2 (τ.positive n)
  have hsq := Real.sq_sqrt (τ.positive n).le
  change (Real.sqrt (τ.time n))⁻¹ = Real.sqrt (τ.time n) / τ.time n
  field_simp [hs.ne', (τ.positive n).ne']
  nlinarith

lemma subexpAlong_of_eventual_log_budget (τ : HorizonSchedule) (u : ℕ→ℝ)
    (a b : ℝ)
    (hbudget : ∀ᶠ n in atTop,
      Real.log (1+|u n|) ≤ a+Real.sqrt (τ.time n)+b*Real.log (τ.time n)) :
    SubexpAlong τ u := by
  have hc : Tendsto (fun n => a/(2*τ.time n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (τ.cofinal.const_mul_atTop (by norm_num))
  have hs : Tendsto (fun n => Real.sqrt (τ.time n)/(2*τ.time n)) atTop (𝓝 0) := by
    convert (scheduled_sqrt_div_time τ).const_mul (1/2:ℝ) using 1 <;> field_simp <;> ring
  have hl : Tendsto (fun n => b*Real.log (τ.time n)/(2*τ.time n)) atTop (𝓝 0) := by
    convert (scheduled_log_div_time τ).const_mul (b/2) using 1 <;> field_simp <;> ring
  have hsum := (hc.add hs).add hl
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    magnitudeRate_nonneg τ u (fun _ => norm_nonneg _) n)) ?_ (by simpa using hsum)
  filter_upwards [hbudget] with n hn
  have hp : 0<2*τ.time n := by nlinarith [τ.positive n]
  simpa only [magnitudeRate, Real.norm_eq_abs, add_div] using
    div_le_div_of_nonneg_right hn hp.le

/-- A fixed power of T and exp(sqrt T) has an explicit logarithmic budget.
The envelope is proved by each native caller, not inserted into a native root. -/
lemma log_sqrt_power_envelope {T D b x : ℝ} (hT : 1≤T) (hD : 0≤D)
    (hb : 0≤b) (hx : |x|≤D*Real.exp (Real.sqrt T)*T^b) :
    Real.log (1+|x|) ≤ Real.log (1+D)+Real.sqrt T+b*Real.log T := by
  have hTp : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hE : 1≤Real.exp (Real.sqrt T)*T^b := by
    simpa only [one_mul] using mul_le_mul
      (Real.one_le_exp_iff.mpr (Real.sqrt_nonneg T))
      (Real.one_le_rpow hT hb) (by norm_num : (0:ℝ)≤1) (Real.exp_nonneg _)
  have hbig : 1+|x|≤(1+D)*(Real.exp (Real.sqrt T)*T^b) := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0<1+|x|) hbig
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos hTp b).ne',
    Real.log_exp, Real.log_rpow hTp] at hlog
  linarith

lemma palette_nat_power_le {Q j : ℕ} {T eta : ℝ} (hT : 0<T)
    (hQ : (Q:ℝ)≤T^eta) : (Q:ℝ)^j≤T^((j:ℝ)*eta) := by
  calc
    _ ≤ (T^eta)^j := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
    _ = _ := by
      simp only [Real.rpow_def_of_pos hT, ←Real.exp_nat_mul]
      congr 1
      ring

/-- Convert the finite low-mask budget to a common explicit polynomial
budget without discarding any Q-dependent amplitude.  The exponent is a
harmless overestimate; its coefficient of sqrt T remains exactly one. -/
lemma finite_low_budget_polynomial (C A eta : ℝ) (j a b Q : ℕ) {T : ℝ}
    (hC : 0≤C) (hA : 0≤A) (heta : 0≤eta) (hT : 1≤T)
    (hQ : (Q:ℝ)≤T^eta) :
    4*(T-(T-C*Real.log T))*((Q:ℝ)^j*A)^2*Real.exp (Real.sqrt T)*
      (1+Real.sqrt T)^a*(1+T)^b ≤
      (4*C*A^2*(2:ℝ)^(a+b))*Real.exp (Real.sqrt T)*
        T^(1+2*(j:ℝ)*eta+(a:ℝ)+(b:ℝ)) := by
  have hTp : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hsqrt : Real.sqrt T≤T := by
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hlog : Real.log T≤T := (Real.log_le_sub_one_of_pos hTp).trans (by linarith)
  have hpoly : 4*(C*Real.log T)*((Q:ℝ)^j*A)^2*Real.exp (Real.sqrt T)*
      (1+Real.sqrt T)^a*(1+T)^b ≤
      4*(C*T)*(T^((j:ℝ)*eta)*A)^2*Real.exp (Real.sqrt T)*(2*T)^a*(2*T)^b := by
    have hpalette := palette_nat_power_le (j := j) hTp hQ
    have hs : 1+Real.sqrt T≤2*T := by linarith
    have ht : 1+T≤2*T := by linarith
    gcongr <;> first | exact hlog | exact hpalette | exact hs | exact ht | positivity
  rw [show T-(T-C*Real.log T)=C*Real.log T by ring]
  apply hpoly.trans_eq
  simp only [mul_pow, ←pow_add]
  have hpow : T * (T^((j:ℝ)*eta))^2 * T^a * T^b =
      T^(1+2*(j:ℝ)*eta+(a:ℝ)+(b:ℝ)) := by
    calc
      _ = Real.exp (Real.log (T*(T^((j:ℝ)*eta))^2*T^a*T^b)) :=
        (Real.exp_log (by positivity)).symm
      _ = Real.exp ((1+2*(j:ℝ)*eta+(a:ℝ)+(b:ℝ))*Real.log T) := by
        congr 1
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),Real.log_pow,
          Real.log_rpow hTp,Real.log_pow,Real.log_pow]
        ring
      _ = _ := by rw [Real.rpow_def_of_pos hTp]; congr 1; ring

  calc
    _ = (4*C*A^2*(2:ℝ)^(a+b))*Real.exp (Real.sqrt T)*
      (T*(T^((j:ℝ)*eta))^2*T^a*T^b) := by ring
    _ = _ := by rw [hpow]

/-- Full fixed-order low-mask theorem. All four logarithmic constants and the
initial real threshold are selected BEFORE any horizon, palette or cofinal
schedule. The second clause transfers the same constants to arbitrary allowed
moving palettes. Both actual coefficient/drive realizations are retained. -/
theorem log_slack_both_low_masks_subexp
    (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
    (C eta K : ℝ) (hC : 1<C) (heta : 0≤eta) :
    Measurable nativeMovingPrimitiveCutoff ∧
    ∃ a₀ b₀ a₁ b₁ T₀ : ℝ, 0≤b₀ ∧ 0≤b₁ ∧ 1≤T₀ ∧
      (∀ T : ℝ, T₀≤T → ∀ Q : ℕ, Squarefree Q → (Q:ℝ)≤T^eta →
        Real.log (1+|nativeRawLow d r Q (logSlackY r K T) C T|)
          ≤ a₀+Real.sqrt T+b₀*Real.log T ∧
        Real.log (1+|nativeAbsorbedLow d r Q hd (logSlackY r K T) C T|)
          ≤ a₁+Real.sqrt T+b₁*Real.log T) ∧
      (∀ (τ : HorizonSchedule) (Q : ℕ→ℕ), (∀ n, Squarefree (Q n)) →
        (∀ᶠ n in atTop, (Q n:ℝ)≤(τ.time n)^eta) →
        SubexpAlong τ (fun n => nativeRawLow d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n)) ∧
        SubexpAlong τ (fun n => nativeAbsorbedLow d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n)) ∧
        (∀ᶠ n in atTop,
          nativeRawHigh d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n) -
            nativeAbsorbedHigh d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n) =
          nativeAbsorbedLow d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n) -
            nativeRawLow d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n))) := by
  let A₀ := (nativeForwardBoundedDrive d 0 (Nat.zero_le d)).bound
  let A₁ := (nativeForwardBoundedDrive d (r-1) hd).bound
  let a₀ : ℕ := 2*(2*r-1)-2
  let b₀ : ℕ := (2*r-1)*(2*r-1)
  let a₁ : ℕ := 2*r-2
  let b₁ : ℕ := r*r
  let D₀ := 4*C*A₀^2*(2:ℝ)^(a₀+b₀)
  let D₁ := 4*C*A₁^2*(2:ℝ)^(a₁+b₁)
  let M₀ : ℝ := 1+2*eta+a₀+b₀
  let M₁ : ℝ := 1+2*(r:ℝ)*eta+a₁+b₁
  have hC0 : 0≤C := by linarith
  have hA₀ : 0≤A₀ := (nativeForwardBoundedDrive d 0 (Nat.zero_le d)).bound_nonneg
  have hA₁ : 0≤A₁ := (nativeForwardBoundedDrive d (r-1) hd).bound_nonneg
  have hD₀ : 0≤D₀ := by dsimp [D₀]; positivity
  have hD₁ : 0≤D₁ := by dsimp [D₁]; positivity
  have hM₀ : 0≤M₀ := by dsimp [M₀]; positivity
  have hM₁ : 0≤M₁ := by dsimp [M₁]; positivity
  obtain ⟨Ty,hTy⟩ := eventually_atTop.1 (logSlackY_eventually_ge_one r (by omega) K)
  let T₀ : ℝ := max 1 Ty
  have hT₀ : 1≤T₀ := le_max_left _ _
  have hlogs (T : ℝ) (hT : T₀≤T) (Q : ℕ) (_hQ : Squarefree Q)
      (hQbudget : (Q:ℝ)≤T^eta) :
      Real.log (1+|nativeRawLow d r Q (logSlackY r K T) C T|)
        ≤ Real.log (1+D₀)+Real.sqrt T+M₀*Real.log T ∧
      Real.log (1+|nativeAbsorbedLow d r Q hd (logSlackY r K T) C T|)
        ≤ Real.log (1+D₁)+Real.sqrt T+M₁*Real.log T := by
    have hT1 : 1≤T := hT₀.trans hT
    have hY : 1≤logSlackY r K T := hTy T ((le_max_right 1 Ty).trans hT)
    have hHT : T-C*Real.log T≤T := sub_le_self _ (mul_nonneg hC0 (Real.log_nonneg hT1))
    obtain ⟨⟨_,hraw⟩,⟨_,habs⟩⟩ := native_balanced_low_masks_explicit r d Q hr hd
      (logSlackY r K T) (T-C*Real.log T) T hY (by linarith) hHT
    constructor
    · apply log_sqrt_power_envelope hT1 hD₀ hM₀
      exact hraw.trans (by
        simpa [D₀,M₀,A₀,a₀,b₀] using
          finite_low_budget_polynomial C A₀ eta 1 a₀ b₀ Q hC0 hA₀ heta hT1 hQbudget)
    · apply log_sqrt_power_envelope hT1 hD₁ hM₁
      exact habs.trans (by
        simpa [D₁,M₁,A₁,a₁,b₁] using
          finite_low_budget_polynomial C A₁ eta r a₁ b₁ Q hC0 hA₁ heta hT1 hQbudget)
  refine ⟨nativeMovingPrimitiveCutoff_measurable,
    Real.log (1+D₀),M₀,Real.log (1+D₁),M₁,T₀,hM₀,hM₁,hT₀,hlogs,?_⟩
  intro τ Q hQsf hQbudget
  have hevent : ∀ᶠ n in atTop, T₀≤τ.time n ∧ (Q n:ℝ)≤(τ.time n)^eta :=
    (τ.cofinal.eventually (eventually_ge_atTop T₀)).and hQbudget
  have hscheduled := hevent.mono (fun n hn => hlogs (τ.time n) hn.1 (Q n) (hQsf n) hn.2)
  refine ⟨subexpAlong_of_eventual_log_budget τ _ _ _ (hscheduled.mono (fun _ h => h.1)),
    subexpAlong_of_eventual_log_budget τ _ _ _ (hscheduled.mono (fun _ h => h.2)),?_⟩
  filter_upwards [hevent] with n hn
  have hT1 : 1≤τ.time n := hT₀.trans hn.1
  have hY : 1≤logSlackY r K (τ.time n) := hTy _ ((le_max_right 1 Ty).trans hn.1)
  exact native_balanced_mask_regrouping r d (Q n) hr hd
    (Nat.pos_of_ne_zero (hQsf n).ne_zero) _ _ _ hY (by linarith)
    (sub_le_self _ (mul_nonneg hC0 (Real.log_nonneg hT1)))

/-- A fixed superlinear negative exponent beats the complete polynomial cost.
This is not a moving-order assertion. -/
lemma superlinear_decay_tendsto (A b c p : ℝ) (hA : 0≤A) (hc : 0<c) (hp : 1<p) :
    Tendsto (fun T : ℝ => A*T^b*Real.exp (T/2-c*T^p)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun T : ℝ => T^(p-1)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hsmall : ∀ᶠ T : ℝ in atTop, T/2-c*T^p≤-T := by
    filter_upwards [hpow.eventually (eventually_ge_atTop (3/(2*c))),
      eventually_gt_atTop (0:ℝ)] with T hT hTp
    have hm := mul_le_mul_of_nonneg_left hT (mul_nonneg hc.le hTp.le)
    have hpoweq : T*T^(p-1)=T^p := by
      calc
        _ = T^(1:ℝ)*T^(p-1) := by rw [Real.rpow_one]
        _ = T^(1+(p-1)) := (Real.rpow_add hTp _ _).symm
        _ = T^p := by congr 1; ring
    rw [show c*T*T^(p-1)=c*(T*T^(p-1)) by ring,hpoweq] at hm
    have hleft : c*T*(3/(2*c))=3*T/2 := by field_simp <;> ring
    rw [hleft] at hm
    linarith
  have hlim : Tendsto (fun T : ℝ => A*T^b*Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [neg_mul, one_mul, mul_zero, mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b 1 (by norm_num)).const_mul A
  apply squeeze_zero' (g := fun T : ℝ => A*T^b*Real.exp (-T)) ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hT b)) (Real.exp_nonneg _)
  · filter_upwards [hsmall,eventually_ge_atTop (0:ℝ)] with T hT hTp
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hT)
      (mul_nonneg hA (Real.rpow_nonneg hTp b))

/-- Actual full-line L2 realization of a continuous field restricted to the
window. It allows a horizon-dependent source, coefficients and palette. -/
def nativeWindowFunction (f : ℝ→ℝ) (C T : ℝ) : ℝ→ℝ :=
  (nativeLogWindow C T).indicator f

lemma nativeWindowFunction_memLp (f : ℝ→ℝ) (hf : Continuous f) (C T : ℝ) :
    MemLp (nativeWindowFunction f C T) 2 volume := by
  have hm : AEStronglyMeasurable (nativeWindowFunction f C T) volume :=
    hf.aestronglyMeasurable.indicator measurableSet_Icc
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hcompact : IntegrableOn (fun t : ℝ => ‖f t‖^2)
      (nativeLogWindow C T) (volume : Measure ℝ) := (hf.norm.pow 2).integrableOn_Icc
  have hi := hcompact.integrable_indicator measurableSet_Icc
  apply hi.congr
  filter_upwards with t
  by_cases ht : t∈nativeLogWindow C T <;> simp [nativeWindowFunction, ht]

def nativeWindowVector (f : ℝ→ℝ) (hf : Continuous f) (C T : ℝ) : Lp (α := ℝ) ℝ 2 (volume : Measure ℝ) :=
  (nativeWindowFunction_memLp f hf C T).toLp (nativeWindowFunction f C T)

lemma nativeWindowVector_coe (f : ℝ→ℝ) (hf : Continuous f) (C T : ℝ) :
    nativeWindowVector f hf C T =ᵐ[volume] nativeWindowFunction f C T :=
  (nativeWindowFunction_memLp f hf C T).coeFn_toLp

lemma nativeWindowVector_norm_sq (f : ℝ→ℝ) (hf : Continuous f) (C T : ℝ) :
    ‖nativeWindowVector f hf C T‖^2 = ∫ t in nativeLogWindow C T, (f t)^2 := by
  rw [←real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ t : ℝ, (nativeLogWindow C T).indicator (fun t => (f t)^2) t := by
      apply integral_congr_ae
      filter_upwards [nativeWindowVector_coe f hf C T] with t ht
      rw [real_inner_self_eq_norm_sq, ht]
      by_cases hmem : t∈nativeLogWindow C T <;>
        simp [nativeWindowFunction, hmem, Real.norm_eq_abs]
    _ = _ := integral_indicator measurableSet_Icc

lemma nativeWindowVector_sub (f g : ℝ→ℝ) (hf : Continuous f) (hg : Continuous g) (C T : ℝ) :
    nativeWindowVector f hf C T-nativeWindowVector g hg C T =
      nativeWindowVector (f-g) (hf.sub hg) C T := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (nativeWindowVector f hf C T) (nativeWindowVector g hg C T),
    nativeWindowVector_coe f hf C T,nativeWindowVector_coe g hg C T,
    nativeWindowVector_coe (f-g) (hf.sub hg) C T] with t hsub hF hG hFG
  rw [hsub, Pi.sub_apply, hF, hG, hFG]
  by_cases ht : t∈nativeLogWindow C T <;> simp [nativeWindowFunction,ht]

lemma nativeWindowVector_norm_le (f : ℝ→ℝ) (hf : Continuous f)
    {C T M : ℝ} (hC : 0≤C) (hT : 1≤T) (hM : 0≤M)
    (hb : ∀ t∈nativeLogWindow C T, |f t|≤M) :
    ‖nativeWindowVector f hf C T‖≤Real.sqrt (C*Real.log T)*M := by
  have hs : ‖nativeWindowVector f hf C T‖^2≤(C*Real.log T)*M^2 := by
    rw [nativeWindowVector_norm_sq]
    have h := window_integral_abs_le (f := fun t : ℝ => (f t)^2) (T-C*Real.log T) T
      (sub_le_self _ (mul_nonneg hC (Real.log_nonneg hT))) (M^2)
      (fun t ht => by simpa only [abs_pow] using
        pow_le_pow_left₀ (abs_nonneg (f t)) (hb t ht) 2)
    have hpos : 0≤∫ t in nativeLogWindow C T, (f t)^2 := integral_nonneg (fun t => sq_nonneg _)
    have h' := (le_abs_self (∫ t in nativeLogWindow C T, (f t)^2)).trans h
    simpa only [nativeLogWindow, sub_sub_cancel] using h'
  have hsqrt := Real.sq_sqrt (mul_nonneg hC (Real.log_nonneg hT))
  nlinarith [norm_nonneg (nativeWindowVector f hf C T),Real.sqrt_nonneg (C*Real.log T),
    mul_nonneg (Real.sqrt_nonneg (C*Real.log T)) hM]

def nativePrimeWindowVector (d : ℕ) (C T : ℝ) : Lp (α := ℝ) ℝ 2 (volume : Measure ℝ) :=
  nativeWindowVector (primeFieldFamily d) (primeFieldFamily_contDiff d).continuous C T

def nativeBalancedWindowVector (d r Q : ℕ) (Y C T : ℝ) : Lp (α := ℝ) ℝ 2 (volume : Measure ℝ) :=
  nativeWindowVector (finiteDriveField (nativeRawPaletteDrive d Q) (driveIndexBound T)
    (balancedInverseCoefficients Q Y r))
    (finiteDriveField_continuous _ _ _) C T

def nativeTypeIWindowVector (d r Q : ℕ) (Y C T : ℝ) : Lp (α := ℝ) ℝ 2 (volume : Measure ℝ) :=
  nativePrimeWindowVector d C T-nativeBalancedWindowVector d r Q Y C T

lemma nativePrimeWindowVector_norm_sq (d : ℕ) (C T : ℝ) :
    ‖nativePrimeWindowVector d C T‖^2=nativePhysicalWindowEnergy d C T :=
  nativeWindowVector_norm_sq _ _ _ _

lemma nativeBalancedWindowVector_high_partition (d r Q : ℕ) (hr : 2≤r)
    (hd : r-1≤d) (hQ : 0<Q) (Y C T : ℝ) (hY : 1≤Y) (hC : 0≤C) (hT : 1≤T) :
    nativeRawHigh d r Q Y C T = ‖nativeBalancedWindowVector d r Q Y C T‖^2-nativeRawLow d r Q Y C T ∧
    nativeAbsorbedHigh d r Q hd Y C T =
      ‖nativeBalancedWindowVector d r Q Y C T‖^2-nativeAbsorbedLow d r Q hd Y C T := by
  have hHT : T-C*Real.log T≤T := sub_le_self _ (mul_nonneg hC (Real.log_nonneg hT))
  obtain ⟨⟨hUL,_⟩,⟨hVL,_⟩⟩ := native_balanced_low_masks_explicit r d Q hr hd Y
    (T-C*Real.log T) T hY (by linarith) hHT
  have hraw := integral_pair_partition (nativeRawPaletteDrive d Q) (driveIndexBound T)
    (balancedInverseCoefficients Q Y r) (balancedInverseCoefficients Q Y r)
    nativeMovingPrimitiveCutoff (nativeLogWindow C T) hUL
    (finiteHighPair_integrableOn _ _ _ _ _ _ _ hUL)
  have hraw' : nativeRawHigh d r Q Y C T =
      ‖nativeBalancedWindowVector d r Q Y C T‖^2-nativeRawLow d r Q Y C T := by
    unfold nativeBalancedWindowVector
    rw [nativeWindowVector_norm_sq]
    simpa only [nativeRawHigh, nativeRawLow, highPairObservation, lowPairObservation,
      pow_two] using hraw
  refine ⟨hraw',?_⟩
  have hreg := native_balanced_mask_regrouping r d Q hr hd hQ Y (T-C*Real.log T) T
    hY (by linarith) hHT
  change nativeRawHigh d r Q Y C T-nativeAbsorbedHigh d r Q hd Y C T =
    nativeAbsorbedLow d r Q hd Y C T-nativeRawLow d r Q Y C T at hreg
  linarith

lemma nativeTypeIWindowVector_bound (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
    (C eta K : ℝ) (hC : 1<C) (heta : 0≤eta) (hK : C+(r:ℝ)*eta+2*r<K) :
    ∃ A c T₀ : ℝ, 0<A ∧ 0<c ∧ 1≤T₀ ∧
      1<(K-C-(r:ℝ)*eta)/(2*r) ∧
      ∀ T≥T₀, ∀ Q : ℕ, Squarefree Q → (Q:ℝ)≤T^eta →
      ‖nativeTypeIWindowVector d r Q (logSlackY r K T) C T‖ ≤
        (Real.sqrt C+1)*A*T^((r:ℝ)*eta+1)*
          Real.exp (T/2-c*T^((K-C-(r:ℝ)*eta)/(2*r))) := by
  obtain ⟨A,c,T₀,hA,hc,hT₀,hp,herr⟩ := log_slack_typeI_error r d hr hd C eta K hC heta hK
  obtain ⟨Ty,hTy⟩ := eventually_atTop.1 (logSlackY_eventually_ge_one r (by omega) K)
  refine ⟨A,c,max T₀ Ty,hA,hc,hT₀.trans (le_max_left _ _),hp,?_⟩
  intro T hT Q hQsf hQb
  have hTbase : T₀≤T := (le_max_left _ _).trans hT
  have hT1 : 1≤T := hT₀.trans hTbase
  have hY : 1≤logSlackY r K T := hTy T ((le_max_right _ _).trans hT)
  let G := finiteDriveField (nativeRawPaletteDrive d Q) (driveIndexBound T)
    (balancedInverseCoefficients Q (logSlackY r K T) r)
  have hG : Continuous G := finiteDriveField_continuous _ _ _
  let M := A*T^((r:ℝ)*eta)*Real.exp (T/2-c*T^((K-C-(r:ℝ)*eta)/(2*r)))
  have hM : 0≤M := by dsimp [M]; positivity
  have hb : ∀ t∈nativeLogWindow C T, |primeFieldFamily d t-G t|≤M := by
    intro t ht
    have hfield := (native_balanced_two_realizations r d Q hr hd
      (Nat.pos_of_ne_zero hQsf.ne_zero) (logSlackY r K T) ht.2).1
    have hpartition := native_balanced_physical_identity d r Q hr (logSlackY r K T) hY t
    have heq : primeFieldFamily d t-G t=typeIField d r Q (logSlackY r K T) t := by
      change finiteDriveField _ _ _ t=balancedField _ _ _ _ t at hfield
      dsimp [G]
      linarith
    rw [heq]
    exact herr T hTbase Q hQsf hQb t ht
  have hv := nativeWindowVector_norm_le (primeFieldFamily d-G)
    ((primeFieldFamily_contDiff d).continuous.sub hG) (by linarith : 0≤C) hT1 hM hb
  have hs : Real.sqrt (C*Real.log T)≤(Real.sqrt C+1)*T := by
    have hlog : Real.log T≤T^2 := by
      have h := Real.log_le_sub_one_of_pos (by linarith : 0<T)
      nlinarith
    have hC0 : 0≤C := by linarith
    have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hC0)
    rw [Real.sqrt_mul hC0, Real.sqrt_mul hC0,
      Real.sqrt_sq (by linarith : 0≤T)] at hsq
    rw [Real.sqrt_mul hC0]
    nlinarith [Real.sqrt_nonneg C]
  rw [nativeTypeIWindowVector,nativePrimeWindowVector,nativeBalancedWindowVector,
    nativeWindowVector_sub] 
  apply hv.trans
  have hpower : T^((r:ℝ)*eta+1)=T^((r:ℝ)*eta)*T := by
    rw [Real.rpow_add (by linarith : 0<T),Real.rpow_one]
  rw [hpower]
  calc
    _ ≤ ((Real.sqrt C+1)*T)*M := mul_le_mul_of_nonneg_right hs hM
    _ = _ := by dsimp [M]; ring

lemma nativeTypeIWindowVector_tendsto_zero (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
    (C eta K : ℝ) (hC : 1<C) (heta : 0≤eta) (hK : C+(r:ℝ)*eta+2*r<K)
    (τ : HorizonSchedule) (Q : ℕ→ℕ) (hQsf : ∀ n, Squarefree (Q n))
    (hQbudget : ∀ᶠ n in atTop, (Q n:ℝ)≤(τ.time n)^eta) :
    Tendsto (fun n => ‖nativeTypeIWindowVector d r (Q n)
      (logSlackY r K (τ.time n)) C (τ.time n)‖) atTop (𝓝 0) := by
  obtain ⟨A,c,T₀,hA,hc,hT₀,hp,hbound⟩ := nativeTypeIWindowVector_bound r d hr hd C eta K hC heta hK
  have hlim := (superlinear_decay_tendsto ((Real.sqrt C+1)*A) ((r:ℝ)*eta+1) c _
    (by positivity) hc hp).comp τ.cofinal
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hlim
  filter_upwards [τ.cofinal.eventually (eventually_ge_atTop T₀),hQbudget] with n hn hq
  exact hbound (τ.time n) hn (Q n) (hQsf n) hq

/-- Full scheduled rate-difference consumer. The L2 vectors and both native
high observations are constructed inside the proof and may vary with n.
Neither native rate is assumed equal to Theta. -/
theorem log_slack_full_minus_masked_energy_rate_difference
    (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
    (C eta K : ℝ) (hC : 1<C) (heta : 0≤eta) (hK : C+(r:ℝ)*eta+2*r<K)
    (τ : HorizonSchedule) (Q : ℕ→ℕ) (hQsf : ∀ n, Squarefree (Q n))
    (hQbudget : ∀ᶠ n in atTop, (Q n:ℝ)≤(τ.time n)^eta) :
    Tendsto (fun n =>
      Real.log (1+nativePhysicalWindowEnergy d C (τ.time n))/(2*τ.time n) -
        positiveRate τ (fun j => nativeRawHigh d r (Q j)
          (logSlackY r K (τ.time j)) C (τ.time j)) n) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      Real.log (1+nativePhysicalWindowEnergy d C (τ.time n))/(2*τ.time n) -
        positiveRate τ (fun j => nativeAbsorbedHigh d r (Q j) hd
          (logSlackY r K (τ.time j)) C (τ.time j)) n) atTop (𝓝 0) := by
  let F := fun n => nativePrimeWindowVector d C (τ.time n)
  let B := fun n => nativeBalancedWindowVector d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n)
  let S := fun n => nativeTypeIWindowVector d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n)
  have hS0 := nativeTypeIWindowVector_tendsto_zero r d hr hd C eta K hC heta hK τ Q hQsf hQbudget
  have hS : SubexpAlong τ S := by
    have hS0' : Tendsto (fun n => ‖S n‖) atTop (𝓝 0) := hS0
    have hplus : Tendsto (fun n => 1+‖S n‖) atTop (𝓝 (1:ℝ)) := by
      simpa only [add_zero] using hS0'.const_add 1
    have hl : Tendsto (fun n => Real.log (1+‖S n‖)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using
        (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hplus
    exact hl.div_atTop (τ.cofinal.const_mul_atTop (by norm_num))
  obtain ⟨_,a₀,b₀,a₁,b₁,T₀,_,_,_,_,hscheduled⟩ :=
    log_slack_both_low_masks_subexp r d hr hd C eta K hC heta
  obtain ⟨hL₀,hL₁,_⟩ := hscheduled τ Q hQsf hQbudget
  have hevent : ∀ᶠ n in atTop, 1≤τ.time n ∧ 1≤logSlackY r K (τ.time n) :=
    (τ.cofinal.eventually (eventually_ge_atTop 1)).and
      (τ.cofinal.eventually (logSlackY_eventually_ge_one r (by omega) K))
  have hF (n : ℕ) : F n=S n+B n := by dsimp [F,S,B,nativeTypeIWindowVector]; abel
  have one_side (q l : ℕ→ℝ) (hl : SubexpAlong τ l)
      (hq : ∀ᶠ n in atTop, q n=‖B n‖^2-l n) :
      Tendsto (fun n => Real.log (1+nativePhysicalWindowEnergy d C (τ.time n))/(2*τ.time n)-
        positiveRate τ q n) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => 2*magnitudeRate τ S n+magnitudeRate τ l n)
        atTop (𝓝 0) := by simpa using (hS.const_mul 2).add hl
    apply squeeze_zero_norm' ?_ hupper
    filter_upwards [hq] with n hn
    have hp : 0<2*τ.time n := by nlinarith [τ.positive n]
    have h := div_le_div_of_nonneg_right
      (norm_first_log_comparison (F n) (S n) (B n) (q n) (l n) (hF n) hn) hp.le
    have hFn : ‖F n‖^2=nativePhysicalWindowEnergy d C (τ.time n) :=
      nativePrimeWindowVector_norm_sq d C (τ.time n)
    simpa only [hFn,Real.norm_eq_abs,positiveRate,magnitudeRate,←sub_div,
      abs_div,abs_of_pos hp,add_div,mul_div_assoc] using h
  constructor
  · apply one_side _ _ hL₀
    filter_upwards [hevent] with n hn
    exact (nativeBalancedWindowVector_high_partition d r (Q n) hr hd
      (Nat.pos_of_ne_zero (hQsf n).ne_zero) _ C _ hn.2 (by linarith) hn.1).1
  · apply one_side _ _ hL₁
    filter_upwards [hevent] with n hn
    exact (nativeBalancedWindowVector_high_partition d r (Q n) hr hd
      (Nat.pos_of_ne_zero (hQsf n).ne_zero) _ C _ hn.2 (by linarith) hn.1).2

/-- Required orientation: retained positive-part energy minus the complete
native physical window energy. Both genuine masks and moving palettes remain. -/
theorem log_slack_masked_energy_rate_difference
    (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
    (C eta K : ℝ) (hC : 1<C) (heta : 0≤eta) (hK : C+(r:ℝ)*eta+2*r<K)
    (τ : HorizonSchedule) (Q : ℕ→ℕ) (hQsf : ∀ n, Squarefree (Q n))
    (hQbudget : ∀ᶠ n in atTop, (Q n:ℝ)≤(τ.time n)^eta) :
    Tendsto (fun n => positiveRate τ (fun j => nativeRawHigh d r (Q j)
      (logSlackY r K (τ.time j)) C (τ.time j)) n -
      Real.log (1+nativePhysicalWindowEnergy d C (τ.time n))/(2*τ.time n)) atTop (𝓝 0) ∧
    Tendsto (fun n => positiveRate τ (fun j => nativeAbsorbedHigh d r (Q j) hd
      (logSlackY r K (τ.time j)) C (τ.time j)) n -
      Real.log (1+nativePhysicalWindowEnergy d C (τ.time n))/(2*τ.time n)) atTop (𝓝 0) := by
  obtain ⟨h₀,h₁⟩ := log_slack_full_minus_masked_energy_rate_difference
    r d hr hd C eta K hC heta hK τ Q hQsf hQbudget
  exact ⟨by simpa only [neg_sub, neg_zero] using h₀.neg,
    by simpa only [neg_sub, neg_zero] using h₁.neg⟩

end Zeta23.OPICAFollowup
