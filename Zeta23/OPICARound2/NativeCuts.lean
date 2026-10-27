import Zeta23.OPICAFollowup.Consumers
import Zeta23.OPICAFollowup.MovingSourceWindowRate
import Zeta23.RvM.MainTerm
import Zeta23.GammaFacts.Complete

/-!
# Actual native damping cuts

These are logical-strength and abscissa consequences of the actual native
envelope/rate theorems. No independent quietness, range, or RH premise is
constructed here. The original completed input is not the new probe target.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICAFollowup

namespace Zeta23.OPICARound2

def nativeDampedFamily (d : ℕ) (epsilon t : ℝ) : ℂ :=
  ((Real.exp (-epsilon*t)*primeFieldFamily d t : ℝ) : ℂ)

theorem nativeDampedFamily_continuous (d : ℕ) (epsilon : ℝ) :
    Continuous (nativeDampedFamily d epsilon) := by
  unfold nativeDampedFamily
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (primeFieldFamily_contDiff d).continuous)

theorem nativeDampedFamily_norm_sq (d : ℕ) (epsilon t : ℝ) :
    ‖nativeDampedFamily d epsilon t‖^2 =
      Real.exp (-2*epsilon*t)*|primeFieldFamily d t|^2 := by
  rw [nativeDampedFamily,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_pos (Real.exp_pos _),mul_pow]
  have he : Real.exp (-epsilon*t)^2=Real.exp (-2*epsilon*t) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he]

theorem nativeDampedFamily_zero_of_neg (d : ℕ) (epsilon : ℝ) {t : ℝ}
    (ht : t<0) : nativeDampedFamily d epsilon t=0 := by
  rw [nativeDampedFamily,primeFieldFamily_zero_before d (ht.trans nativeCausalGap_pos)]
  simp

/-- Upper half of the positive-damping abscissa, for every actual fixed order.
No statement of boundary integrability is made. -/
theorem nativeDampedFamily_memLp_of_theta_lt (d : ℕ) {epsilon : ℝ}
    (hepsilon : nativeZeroDisplacementSup<epsilon) :
    MemLp (nativeDampedFamily d epsilon) 2 volume := by
  obtain ⟨A,hA,hEnv⟩ := native_field_theta_envelope
  let K := nativeFieldOrderConstant d
  have hK : 0<K := (hEnv d).1
  have hDom : Integrable ((Ici (0:ℝ)).indicator
      (fun t : ℝ => K^2*Real.exp (-2*(epsilon-nativeZeroDisplacementSup)*t))) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi
        (by linarith : -2*(epsilon-nativeZeroDisplacementSup)<0) 0).const_mul (K^2))).integrable_indicator
          measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm
    (nativeDampedFamily_continuous d epsilon).aestronglyMeasurable).mpr
  apply hDom.mono' ((nativeDampedFamily_continuous d epsilon).aestronglyMeasurable.norm.pow 2)
  filter_upwards with t
  change ‖‖nativeDampedFamily d epsilon t‖^2‖≤_
  by_cases ht : 0≤t
  · have htmem : t ∈ Ici (0:ℝ) := ht
    rw [indicator_of_mem htmem,Real.norm_of_nonneg (sq_nonneg _),nativeDampedFamily_norm_sq]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) ((hEnv d).2.1 t ht) 2
    calc
      _ ≤ Real.exp (-2*epsilon*t)*(K*Real.exp (nativeZeroDisplacementSup*t))^2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg _)
      _ = K^2*Real.exp (-2*(epsilon-nativeZeroDisplacementSup)*t) := by
        have hpow : Real.exp (nativeZeroDisplacementSup*t)^2=
            Real.exp (2*nativeZeroDisplacementSup*t) := by
          rw [pow_two,←Real.exp_add]
          congr 1
          ring
        rw [mul_pow,hpow]
        calc
          _ = K^2*(Real.exp (-2*epsilon*t)*Real.exp (2*nativeZeroDisplacementSup*t)) := by ring
          _ = _ := by
            rw [←Real.exp_add]
            congr 1
            ring
  · have htmem : t ∉ Ici (0:ℝ) := ht
    rw [indicator_of_notMem htmem,nativeDampedFamily_zero_of_neg d epsilon (lt_of_not_ge ht)]
    simp

theorem native_theta_zero_of_rh (hRH : RiemannHypothesis) :
    nativeZeroDisplacementSup=0 := by
  apply le_antisymm ?_ native_zero_sup_bounds.1
  apply csSup_le (show nativeZeroDisplacementSet.Nonempty from
    ⟨0,Set.mem_insert _ _⟩)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · rw [hx]
  · obtain ⟨rho,rfl⟩ := hx
    have hrho : (rho:ℂ).re=1/2 := RH_implies_on_line hRH rho.property
    norm_num [hrho]

theorem native_rh_iff_theta_zero :
    RiemannHypothesis ↔ nativeZeroDisplacementSup=0 := by
  constructor
  · exact native_theta_zero_of_rh
  · intro hTheta
    exact riemannHypothesis_of_originalPrimeField_allDampedL2
      (originalPrimeField_allDampedL2_of_native_theta_zero hTheta)

theorem native_actual_cuts_equivalent :
    (NativeOriginalPrimeFieldAllDampedL2 ↔ RiemannHypothesis) ∧
    (NativeInputAllRangeClosure ↔ RiemannHypothesis) ∧
    (NativeOriginalPrimeFieldAllDampedIntegral ↔ RiemannHypothesis) := by
  have hX : RiemannHypothesis → NativeOriginalPrimeFieldAllDampedL2 := fun hRH =>
    originalPrimeField_allDampedL2_of_native_theta_zero (native_theta_zero_of_rh hRH)
  refine ⟨⟨riemannHypothesis_of_originalPrimeField_allDampedL2,hX⟩,
    ⟨riemannHypothesis_of_nativeInput_allRangeClosure,fun hRH =>
      nativeInput_allRangeClosure_of_originalPrimeField_allDampedL2 (hX hRH)⟩,?_
    ⟩
  exact ⟨riemannHypothesis_of_originalPrimeField_allDampedIntegral,fun hRH =>
    nativeOriginalPrimeField_allDampedL2_iff_integral.mp (hX hRH)⟩

def nativeCompleteObservationQuiet (time : ℕ→ℝ) : Prop :=
  (∀ epsilon : ℝ, 0<epsilon → ∀ᶠ n : ℕ in atTop,
    Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)
      /(2*time n)≤epsilon) ∨
  (∀ epsilon : ℝ, 0<epsilon → ∀ᶠ n : ℕ in atTop,
    Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
      (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n)≤epsilon)

theorem native_complete_quiet_iff_theta_zero (time : ℕ→ℝ)
    (cofinal : Tendsto time atTop atTop) :
    nativeCompleteObservationQuiet time ↔ nativeZeroDisplacementSup=0 := by
  constructor
  · intro quiet
    exact (quiet_balanced_observation_implies_native_cut time cofinal quiet).1
  · intro hTheta
    left
    intro epsilon hepsilon
    have h := (tendsto_order.1
      (fixed_two_factor_mask_rate_theta.1.comp cofinal)).2 epsilon
        (by simpa only [hTheta] using hepsilon)
    filter_upwards [h] with n hn
    exact le_of_lt hn

/-- The registered MS1 condition is retained exactly, including order zero.
It is not an unrestricted growing-source theorem. -/
theorem native_cut_slow_source_rate (time : ℕ→ℝ)
    (cofinal : Tendsto time atTop atTop) (d : ℕ→ℕ)
    (slow : Tendsto (fun n => (d n:ℝ)*Real.log ((d n:ℝ)+2)/time n) atTop (𝓝 0))
    (C : ℝ) (hC : 1<C) :
    Tendsto (fun n =>
      Real.log (1+(∫ t : ℝ in Icc (time n-C*Real.log (time n)) (time n),
        |primeFieldFamily (d n) t|^2))/(2*time n)) atTop (𝓝 nativeZeroDisplacementSup) :=
  native_slow_source_window_rate time cofinal d slow C hC

/-- The literal nonnegative half-line energy; infinity is not totalized away. -/
def nativeDampingEnergy (d : ℕ) (epsilon : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
    (Real.exp (-2*epsilon*t)*|primeFieldFamily d t|^2)

theorem nativeDampedFamily_memLp_iff_energy (d : ℕ) (epsilon : ℝ) :
    MemLp (nativeDampedFamily d epsilon) 2 volume ↔ nativeDampingEnergy d epsilon<∞ := by
  let W : ℝ→ℝ := fun t => Real.exp (-2*epsilon*t)*|primeFieldFamily d t|^2
  have hW : Continuous W := by
    dsimp [W]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (((primeFieldFamily_contDiff d).continuous.abs).pow 2)
  have hWnonneg : ∀ t, 0≤W t := fun t =>
    mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hfinite : nativeDampingEnergy d epsilon<∞ ↔ IntegrableOn W (Ici 0) := by
    unfold nativeDampingEnergy
    rw [lt_top_iff_ne_top]
    exact lintegral_ofReal_ne_top_iff_integrable hW.aestronglyMeasurable
      (Eventually.of_forall hWnonneg)
  rw [memLp_two_iff_integrable_sq_norm
    (nativeDampedFamily_continuous d epsilon).aestronglyMeasurable,hfinite]
  constructor
  · intro h
    exact h.integrableOn.congr_fun
      (fun t _ => nativeDampedFamily_norm_sq d epsilon t) measurableSet_Ici
  · intro h
    rw [←integrableOn_univ,←@Iio_union_Ici _ _ (0:ℝ),integrableOn_union]
    refine ⟨?_,?_⟩
    · exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Iio 0)).congr_fun
        (g := fun t : ℝ => ‖nativeDampedFamily d epsilon t‖^2)
        (fun t ht => by
          change 0 = ‖nativeDampedFamily d epsilon t‖^2
          rw [nativeDampedFamily_zero_of_neg d epsilon ht]
          simp)
        measurableSet_Iio
    · exact h.congr_fun (fun t _ => (nativeDampedFamily_norm_sq d epsilon t).symm)
        measurableSet_Ici

theorem nativeWindowEnergy_le_damped_total (d : ℕ) {epsilon T : ℝ}
    (hepsilon : 0≤epsilon) (hL2 : MemLp (nativeDampedFamily d epsilon) 2 volume) :
    nativeWindowEnergy d 2 T ≤ Real.exp (2*epsilon*T)*
      (∫ t : ℝ, ‖nativeDampedFamily d epsilon t‖^2) := by
  let I := Icc (T-2*Real.log T) T
  let G : ℝ→ℝ := fun t => ‖nativeDampedFamily d epsilon t‖^2
  have hG : Integrable G := (memLp_two_iff_integrable_sq_norm
    (nativeDampedFamily_continuous d epsilon).aestronglyMeasurable).mp hL2
  have hidentity (t : ℝ) : |primeFieldFamily d t|^2=Real.exp (2*epsilon*t)*G t := by
    dsimp [G]
    rw [nativeDampedFamily_norm_sq,←mul_assoc,←Real.exp_add]
    simp only [show 2*epsilon*t+ -2*epsilon*t=0 by ring,Real.exp_zero,one_mul]
  have hpoint : ∀ t ∈ I, |primeFieldFamily d t|^2≤Real.exp (2*epsilon*T)*G t := by
    intro t ht
    rw [hidentity]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤2*epsilon)))
      (sq_nonneg _)
  calc
    nativeWindowEnergy d 2 T ≤ ∫ t : ℝ in I, Real.exp (2*epsilon*T)*G t :=
      setIntegral_mono_on (nativeWindowEnergy_integrable d 2 T)
        (hG.integrableOn.const_mul _) measurableSet_Icc hpoint
    _ = Real.exp (2*epsilon*T)*(∫ t : ℝ in I, G t) := integral_const_mul _ _
    _ ≤ Real.exp (2*epsilon*T)*(∫ t : ℝ, G t) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hG (Eventually.of_forall fun t => sq_nonneg _))
        (Real.exp_nonneg _)

/-- Necessity is obtained from the actual full window rate, not a supplied
rate for a synthetic field or a greatest-displacement zero. -/
theorem native_theta_le_of_damped_memLp (d : ℕ) {epsilon : ℝ}
    (hepsilon : 0≤epsilon) (hL2 : MemLp (nativeDampedFamily d epsilon) 2 volume) :
    nativeZeroDisplacementSup≤epsilon := by
  let B : ℝ := ∫ t : ℝ, ‖nativeDampedFamily d epsilon t‖^2
  have hB : 0≤B := integral_nonneg fun _ => sq_nonneg _
  have hRate := native_fixed_source_window_rate d 2 (by norm_num)
  have hError : Tendsto (fun T : ℝ => epsilon+(Real.log (1+B)/2)/T) atTop (𝓝 epsilon) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)))
  apply le_of_tendsto_of_tendsto hRate hError
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have hTp : 0<T := by linarith
  have hE := nativeWindowEnergy_le_damped_total d hepsilon hL2 (T:=T)
  have hExp : 1≤Real.exp (2*epsilon*T) :=
    Real.one_le_exp (by positivity)
  have hMajor : 1+nativeWindowEnergy d 2 T≤Real.exp (2*epsilon*T)*(1+B) := by
    dsimp [B] at *
    nlinarith
  have hLog := Real.log_le_log
    (by linarith [nativeWindowEnergy_nonneg d 2 T] : 0<1+nativeWindowEnergy d 2 T) hMajor
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (by positivity : 1+B≠0),Real.log_exp] at hLog
  apply (div_le_iff₀ (by positivity : 0<2*T)).mpr
  calc
    _ ≤ 2*epsilon*T+Real.log (1+B) := hLog
    _ = (epsilon+(Real.log (1+B)/2)/T)*(2*T) := by field_simp

theorem nativeDampingEnergy_finite_of_theta_lt (d : ℕ) {epsilon : ℝ}
    (hepsilon : nativeZeroDisplacementSup<epsilon) : nativeDampingEnergy d epsilon<∞ :=
  (nativeDampedFamily_memLp_iff_energy d epsilon).mp
    (nativeDampedFamily_memLp_of_theta_lt d hepsilon)

theorem nativeDampingEnergy_infinite_below_theta (d : ℕ) {epsilon : ℝ}
    (hepsilon : 0<epsilon) (hlt : epsilon<nativeZeroDisplacementSup) :
    nativeDampingEnergy d epsilon=∞ := by
  by_contra hne
  have hLp := (nativeDampedFamily_memLp_iff_energy d epsilon).mpr
    (lt_top_iff_ne_top.mpr hne)
  exact (not_le.mpr hlt) (native_theta_le_of_damped_memLp d hepsilon.le hLp)

def nativePositiveDampingDomain (d : ℕ) : Set ℝ :=
  {epsilon | 0<epsilon ∧ nativeDampingEnergy d epsilon<∞}

theorem native_positive_damping_abscissa (d : ℕ) :
    sInf (nativePositiveDampingDomain d)=nativeZeroDisplacementSup := by
  have hNonempty : (nativePositiveDampingDomain d).Nonempty := by
    refine ⟨nativeZeroDisplacementSup+1,?_,?_⟩
    · linarith [native_zero_sup_bounds.1]
    · exact nativeDampingEnergy_finite_of_theta_lt d (by linarith)
  have hBdd : BddBelow (nativePositiveDampingDomain d) :=
    ⟨0,fun epsilon hepsilon => hepsilon.1.le⟩
  apply le_antisymm
  · by_contra hNot
    have hlt : nativeZeroDisplacementSup<sInf (nativePositiveDampingDomain d) :=
      lt_of_not_ge hNot
    let epsilon := (nativeZeroDisplacementSup+sInf (nativePositiveDampingDomain d))/2
    have hTheta : nativeZeroDisplacementSup<epsilon := by dsimp [epsilon]; linarith
    have hUpper : epsilon<sInf (nativePositiveDampingDomain d) := by dsimp [epsilon]; linarith
    have hMem : epsilon∈nativePositiveDampingDomain d :=
      ⟨lt_of_le_of_lt native_zero_sup_bounds.1 hTheta,
        nativeDampingEnergy_finite_of_theta_lt d hTheta⟩
    exact (not_le.mpr hUpper) (csInf_le hBdd hMem)
  · apply le_csInf hNonempty
    intro epsilon hepsilon
    exact native_theta_le_of_damped_memLp d hepsilon.1.le
      ((nativeDampedFamily_memLp_iff_energy d epsilon).mpr hepsilon.2)

/-- Complete S11 logical-strength bundle. Every closing condition is an
equivalent proposition, not an independently discharged native estimate. -/
theorem native_damping_abscissa_and_cut_equivalence :
    (∀ d : ℕ, ∀ epsilon : ℝ, nativeZeroDisplacementSup<epsilon →
      nativeDampingEnergy d epsilon<∞) ∧
    (∀ d : ℕ, ∀ epsilon : ℝ, 0<epsilon → epsilon<nativeZeroDisplacementSup →
      nativeDampingEnergy d epsilon=∞) ∧
    (∀ d : ℕ, sInf (nativePositiveDampingDomain d)=nativeZeroDisplacementSup) ∧
    (nativeZeroDisplacementSup=0 ↔ NativeOriginalPrimeFieldAllDampedL2) ∧
    (NativeOriginalPrimeFieldAllDampedL2 ↔ NativeInputAllRangeClosure) ∧
    (NativeInputAllRangeClosure ↔ RiemannHypothesis) ∧
    (∀ time : ℕ→ℝ, Tendsto time atTop atTop →
      (nativeCompleteObservationQuiet time ↔ nativeZeroDisplacementSup=0)) := by
  refine ⟨fun d _ he => nativeDampingEnergy_finite_of_theta_lt d he,
    fun d _ he ht => nativeDampingEnergy_infinite_below_theta d he ht,
    native_positive_damping_abscissa,?_,?_,native_actual_cuts_equivalent.2.1,
    native_complete_quiet_iff_theta_zero⟩
  · exact native_rh_iff_theta_zero.symm.trans native_actual_cuts_equivalent.1.symm
  · exact native_actual_cuts_equivalent.1.trans native_actual_cuts_equivalent.2.1.symm

/-- Actual zeta multiplicities eventually exceed every linear bound. The
Gamma facts are discharged by their native proof, not supplied as a premise.
This is the counting side of the compact-source nonrange comparison. -/
theorem native_zeta_zero_count_superlinear (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C*T<(zetaZeroConfig.N T (2*T):ℝ) := by
  obtain ⟨E,T₀,hRvM⟩ := RvM.rvM_main gammaFacts
  have hEll : Tendsto ell1 atTop atTop := by
    have hLog : Tendsto (fun T : ℝ => Real.log (T/(2*Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Tendsto.atTop_div_const (by positivity) tendsto_id)
    apply tendsto_atTop.2
    intro B
    filter_upwards [(tendsto_atTop.1 hLog) (B-2*Real.log 2+1)] with T hT
    dsimp [ell1,l]
    linarith
  have hLarge := (tendsto_atTop.1 hEll) (2*Real.pi*(C+|E|+1))
  filter_upwards [eventually_ge_atTop T₀,eventually_ge_atTop (1:ℝ),hLarge]
    with T hT₀ hT1 hTlarge
  have hT : 0<T := by linarith
  have hlog : 0≤Real.log T := Real.log_nonneg hT1
  have hlogT : Real.log T≤T := (Real.log_le_sub_one_of_pos hT).trans (by linarith)
  have herror : E*Real.log T≤|E| * T :=
    (mul_le_mul_of_nonneg_right (le_abs_self E) hlog).trans
      (mul_le_mul_of_nonneg_left hlogT (abs_nonneg E))
  have hLower := (abs_le.mp (hRvM T hT₀)).1
  have hCross : (C+|E|+1)*T≤T/(2*Real.pi)*ell1 T := by
    calc
      _ = T/(2*Real.pi)*(2*Real.pi*(C+|E|+1)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hTlarge (by positivity)
  linarith

end Zeta23.OPICARound2
