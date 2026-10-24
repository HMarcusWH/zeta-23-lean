import Zeta23.OPICAFollowup.MultiplicityTail
import Zeta23.OPICA.EnergyRate
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Native fixed-source logarithmic windows

The actual source, all-multiplicity residual, exact A6 and the priced uniform
completion/source costs prove the full continuous fixed-source window rate.
The shared uniform helper also supports the separate MS1 root. The energy and
elementary definitions below retain their earlier statements and proofs.
RH and Step 4 remain OPEN: no independent closing upper bound is asserted.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup

/-- The open interval of completion-rate parameters is nonempty exactly
when the chosen actual right zero has sufficient displacement.  This is
the strict feasibility calculation in the J5.2 terminal-memory argument;
the right zero and constants are chosen BEFORE a varying horizon. -/
theorem nativeWindow_rate_parameter_interval {C Theta delta b : ℝ}
    (hC : 1 < C) (hdelta : Theta + (C - 1) * b < C * delta) :
    ∃ xi : ℝ, (Theta - delta) / (C - 1) < xi ∧ xi < delta - b := by
  have hden : 0 < C - 1 := by linarith
  have hstrict : (Theta - delta) / (C - 1) < delta - b := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [hdelta]
  refine ⟨((Theta - delta) / (C - 1) + (delta - b)) / 2, ?_, ?_⟩
  · linarith
  · linarith

/-- The two strict exponential separations: early memory decays relative to
the completed terminal witness, and that witness exceeds the test rate b.
This does NOT assume the missing analytic memory estimate as an input. -/
theorem nativeWindow_rate_exponent_margin {C Theta delta b xi : ℝ}
    (hC : 1 < C)
    (hlow : (Theta - delta) / (C - 1) < xi)
    (hhigh : xi < delta - b) :
    Theta - C * xi < delta - xi ∧ b < delta - xi := by
  have hden : 0 < C - 1 := by linarith
  have hstrict := (div_lt_iff₀ hden).mp hlow
  constructor
  · nlinarith [hstrict]
  · linarith

/-- Physical energy of the actual d-th native prime field on the literal
terminal interval [T-C log T,T]. No integer-horizon replacement is made. -/
def nativeWindowEnergy (d : ℕ) (C T : ℝ) : ℝ :=
  ∫ t : ℝ in Icc (T - C * Real.log T) T, |primeFieldFamily d t| ^ 2

/-- The physical integrand is integrable on every terminal window, including
degenerate and initially reversed intervals. -/
theorem nativeWindowEnergy_integrable (d : ℕ) (C T : ℝ) :
    IntegrableOn (fun t : ℝ => |primeFieldFamily d t| ^ 2)
      (Icc (T - C * Real.log T) T) := by
  have hc : Continuous (fun t : ℝ => |primeFieldFamily d t| ^ 2) :=
    ((primeFieldFamily_contDiff d).continuous.abs).pow 2
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

theorem nativeWindowEnergy_nonneg (d : ℕ) (C T : ℝ) :
    0 ≤ nativeWindowEnergy d C T := by
  unfold nativeWindowEnergy
  exact integral_nonneg (fun t => sq_nonneg _)

/-- A window ending before the actual causal prime gap contains no signal.
This uses the source-bound primeFieldFamily, not a prescribed zero field. -/
theorem nativeWindowEnergy_zero_before_causal_gap (d : ℕ) (C T : ℝ)
    (hT : T < nativeCausalGap) : nativeWindowEnergy d C T = 0 := by
  unfold nativeWindowEnergy
  have hz : ∀ t ∈ Icc (T - C * Real.log T) T,
      |primeFieldFamily d t| ^ 2 = (0 : ℝ) := by
    intro t ht
    rw [primeFieldFamily_zero_before d (lt_of_le_of_lt ht.2 hT)]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Icc hz]
  simp

/-- The normalised literal rate used in the unfinished J5.2 theorem. -/
def nativeWindowLogRate (d : ℕ) (C T : ℝ) : ℝ :=
  Real.log (1 + nativeWindowEnergy d C T) / (2 * T)

theorem nativeWindowLogRate_nonneg (d : ℕ) (C T : ℝ) (hT : 0 < T) :
    0 ≤ nativeWindowLogRate d C T := by
  unfold nativeWindowLogRate
  apply div_nonneg
  · exact Real.log_nonneg (by linarith [nativeWindowEnergy_nonneg d C T])
  · positivity

end Zeta23.OPICAFollowup


/-! RateSourceCosts supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
open Zeta23.CCM
open Zeta23.ExceptionalZero
namespace Zeta23.OPICAFollowup.NativeWindowProof

/-- Both signs of the literal source transform logarithm have linear order
cost at every actual right zero. No source coefficient estimate is a premise. -/
theorem sourceFactor_abs_log_bound (rho : zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ d : ℕ,
      |Real.log ‖sourceFamilyLaplace d ((rho : ℂ)-1/2)‖| ≤ Cp*((d : ℝ)+1) := by
  let p : ℂ := (rho : ℂ)-1/2
  let A : ℝ := |Real.log ‖p^2-1/4‖|
  let B : ℝ := |Real.log ‖nativeOriginalSourceLaplace p‖|
  have hp : p^2-1/4 ≠ 0 := right_zero_source_factor_ne_zero rho hright
  have hJ : nativeOriginalSourceLaplace p ≠ 0 :=
    nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho (ne_of_gt hright)
  refine ⟨A+B+1, by dsimp [A,B]; positivity, fun d => ?_⟩
  rw [sourceFamilyLaplace_factor, norm_mul, norm_pow,
    Real.log_mul (pow_ne_zero d (norm_ne_zero_iff.mpr hp)) (norm_ne_zero_iff.mpr hJ),
    Real.log_pow]
  have htri := abs_add_le ((d : ℝ)*Real.log ‖p^2-1/4‖)
    (Real.log ‖nativeOriginalSourceLaplace p‖)
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)] at htri
  change |(d : ℝ)*Real.log ‖p^2-1/4‖+Real.log ‖nativeOriginalSourceLaplace p‖| ≤ _
  apply htri.trans
  change (d : ℝ)*A+B ≤ (A+B+1)*((d : ℝ)+1)
  nlinarith [abs_nonneg (Real.log ‖p^2-1/4‖),
    abs_nonneg (Real.log ‖nativeOriginalSourceLaplace p‖), Nat.cast_nonneg (α := ℝ) d]

/-- The zero order costs log 2. It cannot be discarded by silently replacing
the MS1 hypothesis d log(d+2) by (d+1) log(d+2). -/
theorem sourceOrderCost_le_twice (d : ℕ) :
    ((d : ℝ)+1)*Real.log ((d : ℝ)+2) ≤
      2*((d : ℝ)*Real.log ((d : ℝ)+2))+Real.log 2 := by
  by_cases hd : d=0
  · subst d; norm_num
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    have hlog : 0 ≤ Real.log ((d : ℝ)+2) := Real.log_nonneg (by linarith)
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

theorem sourceOrder_div_time_tendsto_zero (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n)
      atTop (𝓝 0)) :
    Tendsto (fun n => (d n : ℝ)/T.time n) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu := hd.const_mul (Real.log 2)⁻¹
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (T.positive n).le) _
    (by simpa using hu)
  intro n
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ)<2)
    (by linarith [Nat.cast_nonneg (α := ℝ) (d n)] : (2 : ℝ) ≤ (d n : ℝ)+2)
  have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (d n))
  have hnum : (d n : ℝ) ≤ (Real.log 2)⁻¹*((d n : ℝ)*Real.log ((d n : ℝ)+2)) := by
    calc
      (d n : ℝ) = (Real.log 2)⁻¹*((d n : ℝ)*Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hlog2.le)
  exact (div_le_div_of_nonneg_right hnum (T.positive n).le).trans_eq (by ring)

theorem fullSourceOrderCost_div_time_tendsto_zero (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n)
      atTop (𝓝 0)) :
    Tendsto (fun n => ((d n : ℝ)+1)*Real.log ((d n : ℝ)+2)/T.time n)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun n => Real.log 2/T.time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop T.cofinal
  have hu := (hd.const_mul 2).add hc
  apply squeeze_zero (fun n => div_nonneg (mul_nonneg (by positivity)
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (d n)]))) (T.positive n).le) _
    (by simpa [add_div] using hu)
  intro n
  exact (div_le_div_of_nonneg_right (sourceOrderCost_le_twice (d n)) (T.positive n).le).trans_eq (by ring)

/-- Both upper and lower literal transform costs are sublinear under precisely
the original MS1 order condition, including d=0 and bounded order schedules. -/
theorem sourceFactor_log_div_time_tendsto_zero (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n)
      atTop (𝓝 0)) (rho : zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    Tendsto (fun n => Real.log ‖sourceFamilyLaplace (d n) ((rho : ℂ)-1/2)‖/T.time n)
      atTop (𝓝 0) := by
  obtain ⟨Cp,hCp,hcost⟩ := sourceFactor_abs_log_bound rho hright
  have hc : Tendsto (fun n => (1 : ℝ)/T.time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop T.cofinal
  have hu := ((sourceOrder_div_time_tendsto_zero T d hd).add hc).const_mul Cp
  apply squeeze_zero_norm _ (by simpa [add_div] using hu)
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (T.positive n)]
  exact (div_le_div_of_nonneg_right (hcost (d n)) (T.positive n).le).trans_eq (by ring)

/-- The actual field envelope's order constant has zero rate under MS1.
This prices the already proved actual envelope; it assumes no window rate. -/
theorem fieldEnvelope_log_div_time_tendsto_zero (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n)
      atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (1+nativeFieldOrderConstant (d n))/T.time n)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := native_field_theta_envelope
  have hu := (fullSourceOrderCost_div_time_tendsto_zero T d hd).const_mul C
  apply squeeze_zero (fun n => div_nonneg
    (Real.log_nonneg (by linarith [(hbound (d n)).1])) (T.positive n).le) _
    (by simpa using hu)
  intro n
  exact (div_le_div_of_nonneg_right (hbound (d n)).2.2 (T.positive n).le).trans_eq (by ring)

end Zeta23.OPICAFollowup.NativeWindowProof

/-! RateCompletionIndex supporting proofs. -/
noncomputable section
open Filter
open scoped Topology
namespace Zeta23.OPICAFollowup.NativeWindowProof

/-- The paper's completion index, with a real continuous horizon. -/
def completionIndex (xi T : ℝ) : ℕ := max 1 (Nat.floor (xi*T/Real.log T))

theorem completionIndex_one_le (xi T : ℝ) : 1 ≤ completionIndex xi T := le_max_left _ _

theorem completionIndex_rounding_bound {xi T : ℝ} (hxi : 0 ≤ xi) (hT : 1 < T) :
    |(completionIndex xi T : ℝ)-xi*T/Real.log T| ≤ 1 := by
  have hTp : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos hT
  have hx : 0 ≤ xi*T/Real.log T := div_nonneg (mul_nonneg hxi hTp.le) hl.le
  have hf := Nat.floor_le hx
  have hg := Nat.lt_floor_add_one (xi*T/Real.log T)
  rw [completionIndex, Nat.cast_max, Nat.cast_one]
  apply abs_le.mpr
  constructor
  · have hm := le_max_right (1 : ℝ) (Nat.floor (xi*T/Real.log T) : ℝ)
    linarith
  · apply sub_le_iff_le_add.mpr
    apply max_le
    · linarith
    · linarith

theorem completionIndex_scaled_error {xi T : ℝ} (hxi : 0 ≤ xi) (hT : 1 < T) :
    |(completionIndex xi T : ℝ)*Real.log T/T-xi| ≤ Real.log T/T := by
  have hTp : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos hT
  have he : (completionIndex xi T : ℝ)*Real.log T/T-xi =
      ((completionIndex xi T : ℝ)-xi*T/Real.log T)*Real.log T/T := by
    field_simp [hTp.ne',hl.ne']
  rw [he,abs_div,abs_mul,abs_of_pos hTp,abs_of_pos hl]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (completionIndex_rounding_bound hxi hT) hl.le)
    hTp.le).trans_eq (by ring)

/-- The damping parameter's logarithmic-window exponent has exactly the
paper's rate xi at continuous horizons, with the max/floor convention retained. -/
theorem completionIndex_log_scale_tendsto (xi : ℝ) (hxi : 0 ≤ xi) :
    Tendsto (fun T : ℝ => (completionIndex xi T : ℝ)*Real.log T/T) atTop (𝓝 xi) := by
  have hl : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have he : Tendsto (fun T : ℝ => (completionIndex xi T : ℝ)*Real.log T/T-xi)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hl
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs] using completionIndex_scaled_error hxi hT
  simpa only [sub_add_cancel,zero_add] using he.add_const xi

theorem actualCompletionAlpha_log_scale_tendsto (xi : ℝ) (hxi : 0 ≤ xi) :
    Tendsto (fun T : ℝ => auxCompletionAlpha (completionIndex xi T)*Real.log T/T)
      atTop (𝓝 xi) := by
  have hl : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have h := (completionIndex_log_scale_tendsto xi hxi).add (hl.const_mul (1/2 : ℝ))
  convert h using 1
  · ext T
    dsimp [auxCompletionAlpha]
    ring
  · simp

theorem completionIndex_div_time_tendsto_zero (xi : ℝ) (hxi : 0 ≤ xi) :
    Tendsto (fun T : ℝ => (completionIndex xi T : ℝ)/T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => xi/Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h2 : Tendsto (fun T : ℝ => (1 : ℝ)/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' _ _ (by simpa using h1.add h2)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hTp : 0 < T := by linarith
    have hl : 0 < Real.log T := Real.log_pos hT
    have hb := (abs_le.mp (completionIndex_rounding_bound hxi hT)).2
    have hnum : (completionIndex xi T : ℝ) ≤ xi*T/Real.log T+1 := by linarith
    exact (div_le_div_of_nonneg_right hnum hTp.le).trans_eq (by field_simp)

/-- A5 only needs this upper asymptotic bound. It avoids introducing the
unnecessary exact log(k+1)/log T asymptotic as a separate dependency. -/
theorem completionCost_eventually_lt (xi Cp : ℝ) (hxi : 0 ≤ xi) {eps : ℝ}
    (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop,
      ((completionIndex xi T : ℝ)*Real.log ((completionIndex xi T : ℝ)+1)+
        Cp*((completionIndex xi T : ℝ)+1))/T < xi+eps := by
  have hk := completionIndex_div_time_tendsto_zero xi hxi
  have hu : Tendsto (fun T : ℝ =>
      (completionIndex xi T : ℝ)*Real.log T/T+
        (Real.log 2+Cp)*((completionIndex xi T : ℝ)/T)+Cp/T) atTop (𝓝 xi) := by
    have hCp : Tendsto (fun T : ℝ => Cp/T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using ((completionIndex_log_scale_tendsto xi hxi).add (hk.const_mul (Real.log 2+Cp))).add hCp
  have hsmall : ∀ᶠ T : ℝ in atTop, (completionIndex xi T : ℝ)/T < 1 :=
    (tendsto_order.1 hk).2 1 (by norm_num)
  have hupper : ∀ᶠ T : ℝ in atTop,
      (completionIndex xi T : ℝ)*Real.log T/T+
        (Real.log 2+Cp)*((completionIndex xi T : ℝ)/T)+Cp/T < xi+eps :=
    (tendsto_order.1 hu).2 (xi+eps) (by linarith)
  filter_upwards [hsmall,hupper,eventually_gt_atTop (1 : ℝ)] with T hs hu hT
  have hTp : 0 < T := by linarith
  have hkT : (completionIndex xi T : ℝ) < T := by
    simpa only [one_mul] using (div_lt_iff₀ hTp).mp hs
  have hlog : Real.log ((completionIndex xi T : ℝ)+1) ≤ Real.log (2*T) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) hTp.ne'] at hlog
  have hnum := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (completionIndex xi T))
  have hbound : ((completionIndex xi T : ℝ)*Real.log ((completionIndex xi T : ℝ)+1)+
      Cp*((completionIndex xi T : ℝ)+1))/T ≤
      (completionIndex xi T : ℝ)*Real.log T/T+
        (Real.log 2+Cp)*((completionIndex xi T : ℝ)/T)+Cp/T := by
    calc
      _ ≤ ((completionIndex xi T : ℝ)*(Real.log 2+Real.log T)+
          Cp*((completionIndex xi T : ℝ)+1))/T :=
        div_le_div_of_nonneg_right (by linarith [hnum]) hTp.le
      _ = _ := by ring
  exact hbound.trans_lt hu

end Zeta23.OPICAFollowup.NativeWindowProof

/-! RateWindowBounds supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.CCM
namespace Zeta23.OPICAFollowup.NativeWindowProof

/-- The literal window energy has the sharp theta envelope, at every source
order and every real horizon whose window begins after zero. -/
theorem nativeWindowEnergy_upper (d : ℕ) {C T : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hstart : 0 ≤ T-C*Real.log T) :
    nativeWindowEnergy d C T ≤ C*Real.log T*(nativeFieldOrderConstant d)^2*
      Real.exp (2*nativeZeroDisplacementSup*T) := by
  obtain ⟨A,hA,henv⟩ := native_field_theta_envelope
  have htheta : 0 ≤ nativeZeroDisplacementSup := native_zero_sup_bounds.1
  have hCT : 0 ≤ C*Real.log T := mul_nonneg hC (Real.log_nonneg hT)
  have hlen : T-C*Real.log T ≤ T := by linarith
  let B := (nativeFieldOrderConstant d)^2*Real.exp (2*nativeZeroDisplacementSup*T)
  have hi : nativeWindowEnergy d C T ≤ ∫ _t : ℝ in Icc (T-C*Real.log T) T, B := by
    apply setIntegral_mono_on (nativeWindowEnergy_integrable d C T)
      ((continuous_const : Continuous (fun _ : ℝ => B)).continuousOn.integrableOn_compact isCompact_Icc)
      measurableSet_Icc
    intro t ht
    have hp := (henv d).2.1 t (hstart.trans ht.1)
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 htheta)
    have hK := (henv d).1
    have hbound := hp.trans (mul_le_mul_of_nonneg_left he hK.le)
    have hsquare := pow_le_pow_left₀ (abs_nonneg (primeFieldFamily d t)) hbound 2
    calc
      |primeFieldFamily d t|^2 ≤
        (nativeFieldOrderConstant d*Real.exp (nativeZeroDisplacementSup*T))^2 := hsquare
      _ = B := by dsimp [B]; rw [mul_pow, ← Real.exp_nat_mul]; congr 2 <;> ring
  calc
    nativeWindowEnergy d C T ≤ ∫ _t : ℝ in Icc (T-C*Real.log T) T, B := hi
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le hlen, smul_eq_mul]
      dsimp [B]
      ring

/-- Polynomially weaker than the paper's inverse-alpha prefactor, but with
the same required exponential separation. The actual early prime-field memory
is used; its envelope is discharged internally. -/
theorem native_oldMemory_upper (d : ℕ) {alpha C T : ℝ} (ha : 0 ≤ alpha)
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hstart : 0 ≤ T-C*Real.log T) :
    (∫ s : ℝ in Icc 0 (T-C*Real.log T),
      Real.exp (-alpha*(T-s))*|primeFieldFamily d s|) ≤
      T*nativeFieldOrderConstant d*
        Real.exp (nativeZeroDisplacementSup*T-(alpha+nativeZeroDisplacementSup)*C*Real.log T) := by
  obtain ⟨A,hA,henv⟩ := native_field_theta_envelope
  have htheta : 0 ≤ nativeZeroDisplacementSup := native_zero_sup_bounds.1
  have hCT : 0 ≤ C*Real.log T := mul_nonneg hC (Real.log_nonneg hT)
  have hecont : Continuous (fun s : ℝ => Real.exp (-alpha*(T-s))) := by fun_prop
  have hcont : Continuous (fun s : ℝ =>
      Real.exp (-alpha*(T-s))*|primeFieldFamily d s|) :=
    hecont.mul (primeFieldFamily_contDiff d).continuous.abs
  let B := nativeFieldOrderConstant d*
    Real.exp (nativeZeroDisplacementSup*T-(alpha+nativeZeroDisplacementSup)*C*Real.log T)
  have hi : (∫ s : ℝ in Icc 0 (T-C*Real.log T),
      Real.exp (-alpha*(T-s))*|primeFieldFamily d s|) ≤
      ∫ _s : ℝ in Icc 0 (T-C*Real.log T), B := by
    apply setIntegral_mono_on (hcont.continuousOn.integrableOn_compact isCompact_Icc)
      ((continuous_const : Continuous (fun _ : ℝ => B)).continuousOn.integrableOn_compact isCompact_Icc)
      measurableSet_Icc
    intro s hs
    have hp := mul_le_mul_of_nonneg_left ((henv d).2.1 s hs.1) (Real.exp_nonneg (-alpha*(T-s)))
    have hex : -alpha*(T-s)+nativeZeroDisplacementSup*s ≤
        nativeZeroDisplacementSup*T-(alpha+nativeZeroDisplacementSup)*C*Real.log T := by
      nlinarith [mul_le_mul_of_nonneg_left hs.2 (add_nonneg ha htheta)]
    calc
      _ ≤ Real.exp (-alpha*(T-s))*(nativeFieldOrderConstant d*Real.exp (nativeZeroDisplacementSup*s)) := hp
      _ = nativeFieldOrderConstant d*Real.exp (-alpha*(T-s)+nativeZeroDisplacementSup*s) := by
        rw [Real.exp_add]; ring
      _ ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (henv d).1.le
  calc
    _ ≤ ∫ _s : ℝ in Icc 0 (T-C*Real.log T), B := hi
    _ = (T-C*Real.log T)*nativeFieldOrderConstant d*
        Real.exp (nativeZeroDisplacementSup*T-(alpha+nativeZeroDisplacementSup)*C*Real.log T) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le hstart, sub_zero, smul_eq_mul]
      dsimp [B]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (henv d).1.le
      linarith

end Zeta23.OPICAFollowup.NativeWindowProof

/-! RateMemoryWindow supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup.NativeWindowProof

theorem tailMemory_split (d : ℕ) (alpha C T : ℝ) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hstart : 0 ≤ T-C*Real.log T) :
    tailMemory alpha d T =
      (∫ s : ℝ in Icc 0 (T-C*Real.log T), Real.exp (-alpha*(T-s))*|primeFieldFamily d s|)+
      (∫ s : ℝ in Icc (T-C*Real.log T) T, Real.exp (-alpha*(T-s))*|primeFieldFamily d s|) := by
  let f : ℝ → ℝ := fun s => Real.exp (-alpha*(T-s))*|primeFieldFamily d s|
  have he : Continuous (fun s : ℝ => Real.exp (-alpha*(T-s))) := by fun_prop
  have hf : Continuous f := he.mul (primeFieldFamily_contDiff d).continuous.abs
  have hLT : T-C*Real.log T ≤ T := sub_le_self _ (mul_nonneg hC (Real.log_nonneg hT))
  have h0T : 0 ≤ T := by linarith
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 (T-C*Real.log T)) (hf.intervalIntegrable (T-C*Real.log T) T)
  rw [intervalIntegral.integral_of_le hstart, intervalIntegral.integral_of_le hLT,
    intervalIntegral.integral_of_le h0T] at h
  simpa only [tailMemory, integral_Icc_eq_integral_Ioc, f] using h.symm

/-- A direct Cauchy–Schwarz bridge from actual terminal memory to the literal
energy. Its logarithmic-window prefactor is sufficient for a rate theorem. -/
theorem native_terminalMemory_sq_le_windowEnergy (d : ℕ) {alpha C T : ℝ}
    (ha : 0 ≤ alpha) (hC : 0 ≤ C) (hT : 1 ≤ T) :
    (∫ s : ℝ in Icc (T-C*Real.log T) T,
      Real.exp (-alpha*(T-s))*|primeFieldFamily d s|)^2 ≤
      C*Real.log T*nativeWindowEnergy d C T := by
  let I := Icc (T-C*Real.log T) T
  let mu : Measure ℝ := volume.restrict I
  have hlen : 0 ≤ C*Real.log T := mul_nonneg hC (Real.log_nonneg hT)
  have hLT : T-C*Real.log T ≤ T := by linarith
  have hFcont : Continuous (fun s : ℝ => |primeFieldFamily d s|) :=
    (primeFieldFamily_contDiff d).continuous.abs
  have hFmeas : AEStronglyMeasurable (fun s : ℝ => |primeFieldFamily d s|) mu :=
    hFcont.aestronglyMeasurable
  have hF2 : Integrable (fun s : ℝ => |primeFieldFamily d s|^2) mu :=
    nativeWindowEnergy_integrable d C T
  have h1meas : AEStronglyMeasurable (fun _s : ℝ => (1 : ℝ)) mu :=
    stronglyMeasurable_const.aestronglyMeasurable
  have h12 : Integrable (fun _s : ℝ => (1 : ℝ)^2) mu :=
    (continuous_const : Continuous (fun _s : ℝ => (1 : ℝ)^2)).continuousOn.integrableOn_compact isCompact_Icc
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall (fun _s : ℝ => zero_le_one))
    (Eventually.of_forall (fun s : ℝ => abs_nonneg (primeFieldFamily d s)))
    (by simpa using (memLp_two_iff_integrable_sq h1meas).mpr h12)
    (by simpa using (memLp_two_iff_integrable_sq hFmeas).mpr hF2)
  have hCS : (∫ s : ℝ in I, |primeFieldFamily d s|) ≤
      Real.sqrt (C*Real.log T)*Real.sqrt (nativeWindowEnergy d C T) := by
    simpa only [one_mul,Real.rpow_two,Real.sqrt_eq_rpow,one_pow,
      mu,I,nativeWindowEnergy,setIntegral_const,Real.volume_real_Icc_of_le hLT,
      smul_eq_mul,mul_one,sub_sub_cancel] using hHolder
  have hecont : Continuous (fun s : ℝ => Real.exp (-alpha*(T-s))) := by fun_prop
  have hweightcont : Continuous (fun s : ℝ => Real.exp (-alpha*(T-s))*|primeFieldFamily d s|) :=
    hecont.mul hFcont
  have hdrop : (∫ s : ℝ in I, Real.exp (-alpha*(T-s))*|primeFieldFamily d s|) ≤
      ∫ s : ℝ in I, |primeFieldFamily d s| := by
    apply setIntegral_mono_on
      (hweightcont.continuousOn.integrableOn_compact isCompact_Icc)
      (hFcont.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
    intro s hs
    have hExp : Real.exp (-alpha*(T-s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sub_nonneg.mpr hs.2))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hExp (abs_nonneg (primeFieldFamily d s))
  have hmem : 0 ≤ ∫ s : ℝ in I, Real.exp (-alpha*(T-s))*|primeFieldFamily d s| :=
    integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  calc
    _ ≤ (Real.sqrt (C*Real.log T)*Real.sqrt (nativeWindowEnergy d C T))^2 :=
      pow_le_pow_left₀ hmem (hdrop.trans hCS) 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hlen,Real.sq_sqrt (nativeWindowEnergy_nonneg d C T)]

/-- A source-specific finite-horizon obstruction from an actual right zero,
with its full multiplicity. Every coefficient, subtraction and old-memory
cost is discharged from the existing native constructions. -/
theorem native_window_energy_multiplicity_barrier (k d : ℕ) (hk : 1 ≤ k)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T) (hstart : 0 ≤ T-C*Real.log T) :
    let alpha := auxCompletionAlpha k
    let lower := Real.sqrt (2*alpha)/auxCompletionBound k*
      max (nativeMultiplicityTailConstant d rho*‖auxRationalFactor k ((rho : ℂ)-1/2)‖*
        Real.exp (((rho : ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖) 0
    let old := T*nativeFieldOrderConstant d*
      Real.exp (nativeZeroDisplacementSup*T-(alpha+nativeZeroDisplacementSup)*C*Real.log T)
    (max (lower-old) 0)^2 ≤ C*Real.log T*nativeWindowEnergy d C T := by
  dsimp only
  have ha : 0 ≤ auxCompletionAlpha k := by dsimp [auxCompletionAlpha]; positivity
  have hLower := native_terminal_memory_lower k d hk rho hright T
  have hOld := native_oldMemory_upper d ha hC hT hstart
  have hSplit := tailMemory_split d (auxCompletionAlpha k) C T hC hT hstart
  have hWin0 : 0 ≤ ∫ s : ℝ in Icc (T-C*Real.log T) T,
      Real.exp (-auxCompletionAlpha k*(T-s))*|primeFieldFamily d s| :=
    integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  have hBarrier : max
      (Real.sqrt (2*auxCompletionAlpha k)/auxCompletionBound k*
        max (nativeMultiplicityTailConstant d rho*‖auxRationalFactor k ((rho : ℂ)-1/2)‖*
          Real.exp (((rho : ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖) 0-
        T*nativeFieldOrderConstant d*
          Real.exp (nativeZeroDisplacementSup*T-(auxCompletionAlpha k+nativeZeroDisplacementSup)*C*Real.log T)) 0 ≤
      ∫ s : ℝ in Icc (T-C*Real.log T) T,
        Real.exp (-auxCompletionAlpha k*(T-s))*|primeFieldFamily d s| := by
    apply max_le _ hWin0
    linarith
  exact (pow_le_pow_left₀ (le_max_right _ _) hBarrier 2).trans
    (native_terminalMemory_sq_le_windowEnergy d ha hC hT)

end Zeta23.OPICAFollowup.NativeWindowProof

/-! NativeAsymptoticCosts supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem multiplicityTailConstant_source_factor (d : ℕ) (rho : zetaZeroConfig.carrier) :
    nativeMultiplicityTailConstant d rho =
      ‖((rho : ℂ)-1/2)^2-1/4‖^d*nativeMultiplicityTailConstant 0 rho := by
  dsimp [nativeMultiplicityTailConstant]
  rw [sourceFamilyLaplace_factor,sourceFamilyLaplace_factor]
  simp only [pow_zero,one_mul,norm_mul,norm_pow]
  ring

theorem multiplicityTailConstant_log_div_time_tendsto_zero
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    (rho : zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re) :
    Tendsto (fun n => Real.log (nativeMultiplicityTailConstant (d n) rho)/T.time n)
      atTop (𝓝 0) := by
  let p : ℂ := (rho : ℂ)-1/2
  have hp := norm_ne_zero_iff.mpr (right_zero_source_factor_ne_zero rho hright)
  have hJ := norm_ne_zero_iff.mpr
    (nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho (ne_of_gt hright))
  have hD := (nativeMultiplicityTailConstant_pos 0 rho hright).ne'
  have he (n : ℕ) : Real.log (nativeMultiplicityTailConstant (d n) rho)/T.time n =
      Real.log ‖sourceFamilyLaplace (d n) p‖/T.time n+
        (Real.log (nativeMultiplicityTailConstant 0 rho)-Real.log ‖nativeOriginalSourceLaplace p‖)/T.time n := by
    rw [multiplicityTailConstant_source_factor,sourceFamilyLaplace_factor,norm_mul,norm_pow,
      Real.log_mul (pow_ne_zero (d n) hp) hD,Real.log_mul (pow_ne_zero (d n) hp) hJ,
      Real.log_pow]
    dsimp [p]
    ring
  have hc : Tendsto (fun n =>
      (Real.log (nativeMultiplicityTailConstant 0 rho)-Real.log ‖nativeOriginalSourceLaplace p‖)/T.time n)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop T.cofinal
  have h := (sourceFactor_log_div_time_tendsto_zero T d hd rho hright).add hc
  simpa only [add_zero] using h.congr (fun n => (he n).symm)

theorem auxiliaryDriveCausalVector_norm_eq (d : ℕ) :
    ‖auxiliaryDriveCausalVector d‖ = ‖integerDriveFamilyL2 d‖ := by
  have hc : (auxiliaryDriveCausalVector d : NativeCompletionL2) =ᵐ[volume]
      (fun t : ℝ => (integerDriveFamily d t : ℂ)) :=
    (auxiliaryDrive_complex_memLp_two d).coeFn_toLp
  have hnorm : ‖(auxiliaryDriveCausalVector d : NativeCompletionL2)‖^2 =
      ∫ t : ℝ, |integerDriveFamily d t|^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc] with t ht
    simp only [ht,real_inner_self_eq_norm_sq,Complex.norm_real,Real.norm_eq_abs]
  have hreal : ‖integerDriveFamilyL2 d‖^2 = ∫ t : ℝ, |integerDriveFamily d t|^2 := by
    rw [integerDriveFamilyL2_norm_eq,Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hnorm.trans hreal.symm)

theorem actualInput_div_rational_bound (rho : zetaZeroConfig.carrier)
    (hright : 1/2 < (rho : ℂ).re) :
    ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧ ∀ k d : ℕ, 1 ≤ k →
      ‖nativeAuxiliaryStableVector k d‖/‖auxRationalFactor k ((rho : ℂ)-1/2)‖ ≤
        Real.exp (Cp*((k : ℝ)+1)+Cs*((d : ℝ)+1)*Real.log ((d : ℝ)+2)) := by
  obtain ⟨Cp,hCp,hp⟩ := aux_completion_ratio_bounds rho hright
  obtain ⟨Cs,hCs,hs⟩ := source_order_uniform_norms
  refine ⟨Cp,Cs,hCp,hCs,fun k d hk => ?_⟩
  have hd := (hs d).2.2.1
  have hnorm : ‖auxiliaryDriveCausalVector d‖ ≤ Real.exp (Cs*((d : ℝ)+1)*Real.log ((d : ℝ)+2)) := by
    rw [auxiliaryDriveCausalVector_norm_eq]
    exact hd
  calc
    _ ≤ ((∫ s : ℝ, ‖auxCompletionFilter k s‖)*‖auxiliaryDriveCausalVector d‖)/
        ‖auxRationalFactor k ((rho : ℂ)-1/2)‖ :=
      div_le_div_of_nonneg_right (nativeAuxiliaryStableVector_norm_le k d) (norm_nonneg _)
    _ = ((∫ s : ℝ, ‖auxCompletionFilter k s‖)/‖auxRationalFactor k ((rho : ℂ)-1/2)‖)*
        ‖auxiliaryDriveCausalVector d‖ := by ring
    _ ≤ Real.exp (Cp*((k : ℝ)+1))*Real.exp (Cs*((d : ℝ)+1)*Real.log ((d : ℝ)+2)) :=
      mul_le_mul (hp k hk).2.1 hnorm (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeWindowUpperRate supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem windowStart_eventually_nonneg (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 0 ≤ T-C*Real.log T := by
  have hl : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hs : ∀ᶠ T : ℝ in atTop, C*(Real.log T/T)<1 :=
    (tendsto_order.1 (hl.const_mul C)).2 1 (by norm_num)
  filter_upwards [hs,eventually_ge_atTop (1 : ℝ)] with T hs hT
  refine ⟨hT,?_⟩
  have hTp : 0 < T := by linarith
  have hCT : C*Real.log T<T := by
    rw [←mul_div_assoc] at hs
    simpa only [one_mul] using (div_lt_iff₀ hTp).mp hs
  linarith

theorem nativeWindowLogRate_upper_bound (d : ℕ) {C T : ℝ} (hC : 0 ≤ C)
    (hT : 1 ≤ T) (hstart : 0 ≤ T-C*Real.log T) :
    nativeWindowLogRate d C T ≤ nativeZeroDisplacementSup+
      (Real.log (1+C)+Real.log T+2*Real.log (1+nativeFieldOrderConstant d))/(2*T) := by
  obtain ⟨A,hA,hEnv⟩ := native_field_theta_envelope
  let K := nativeFieldOrderConstant d
  let L := C*Real.log T
  let B := 2*nativeZeroDisplacementSup*T
  have hK : 0 < K := (hEnv d).1
  have hL : 0 ≤ L := mul_nonneg hC (Real.log_nonneg hT)
  have hTp : 0 < T := by linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [native_zero_sup_bounds.1]
  have he : 1 ≤ Real.exp B := Real.one_le_exp hB
  have hEnergy := nativeWindowEnergy_upper d hC hT hstart
  have hFactor : 1+nativeWindowEnergy d C T ≤ Real.exp B*((1+L)*(1+K)^2) := by
    have h1 : 1+nativeWindowEnergy d C T ≤ Real.exp B*(1+L*K^2) := by
      dsimp [B,L,K] at *
      nlinarith
    have h2 : 1+L*K^2 ≤ (1+L)*(1+K)^2 := by
      nlinarith [mul_nonneg hL hK.le,sq_nonneg K]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _))
  have hLog := Real.log_le_log (by linarith [nativeWindowEnergy_nonneg d C T]) hFactor
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_pow] at hLog
  have hLogT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hTp).trans (by linarith)
  have hSpan : 1+L ≤ (1+C)*T := by
    dsimp [L]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hLogT)]
  have hLogSpan := Real.log_le_log (by positivity : 0 < 1+L) hSpan
  rw [Real.log_mul (by positivity) hTp.ne'] at hLogSpan
  have hAll : Real.log (1+nativeWindowEnergy d C T) ≤
      2*nativeZeroDisplacementSup*T+Real.log (1+C)+Real.log T+2*Real.log (1+nativeFieldOrderConstant d) := by
    dsimp [B,K] at hLog
    norm_num only [Nat.cast_ofNat] at hLog
    linarith
  unfold nativeWindowLogRate
  calc
    _ ≤ (2*nativeZeroDisplacementSup*T+Real.log (1+C)+Real.log T+
        2*Real.log (1+nativeFieldOrderConstant d))/(2*T) :=
      div_le_div_of_nonneg_right hAll (by positivity)
    _ = _ := by field_simp; ring

theorem slowSource_upper_error_tendsto_zero (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0)) (C : ℝ) :
    Tendsto (fun n => (Real.log (1+C)+Real.log (T.time n)+
      2*Real.log (1+nativeFieldOrderConstant (d n)))/(2*T.time n)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => Real.log (1+C)/T.time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop T.cofinal
  have hl : Tendsto (fun n => Real.log (T.time n)/T.time n) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => Real.log t/t) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    exact h.comp T.cofinal
  have hk := fieldEnvelope_log_div_time_tendsto_zero T d hd
  have h := ((hc.add hl).add (hk.const_mul 2)).div_const 2
  convert h using 1
  · ext n; ring
  · norm_num

theorem slowSource_window_rate_eventually_lt_theta_add
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, nativeWindowLogRate (d n) C (T.time n) < nativeZeroDisplacementSup+epsilon := by
  have hs := T.cofinal.eventually (windowStart_eventually_nonneg C)
  have he := (tendsto_order.1 (slowSource_upper_error_tendsto_zero T d hd C)).2 epsilon hepsilon
  filter_upwards [hs,he] with n hs he
  exact (nativeWindowLogRate_upper_bound (d n) hC hs.1 hs.2).trans_lt (by linarith)

theorem slowSource_window_rate_tendsto_zero_of_theta_zero
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (hTheta : nativeZeroDisplacementSup = 0) :
    Tendsto (fun n => nativeWindowLogRate (d n) C (T.time n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => nativeWindowLogRate_nonneg (d n) C (T.time n) (T.positive n)) _
    (slowSource_upper_error_tendsto_zero T d hd C)
  filter_upwards [T.cofinal.eventually (windowStart_eventually_nonneg C)] with n hn
  simpa only [hTheta,zero_add] using nativeWindowLogRate_upper_bound (d n) hC hn.1 hn.2

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeInputRate supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem actualInput_rational_ratio_log_rate_zero (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    (rho : zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re)
    (xi : ℝ) (hxi : 0 ≤ xi) :
    Tendsto (fun n => Real.log (1+
      ‖nativeAuxiliaryStableVector (completionIndex xi (T.time n)) (d n)‖/
        ‖auxRationalFactor (completionIndex xi (T.time n)) ((rho : ℂ)-1/2)‖)/T.time n)
      atTop (𝓝 0) := by
  obtain ⟨Cp,Cs,hCp,hCs,hbound⟩ := actualInput_div_rational_bound rho hright
  have hk := (completionIndex_div_time_tendsto_zero xi hxi).comp T.cofinal
  have h1 : Tendsto (fun n => (1 : ℝ)/T.time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop T.cofinal
  have hlog2 : Tendsto (fun n => Real.log 2/T.time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop T.cofinal
  have horder := fullSourceOrderCost_div_time_tendsto_zero T d hd
  have hu : Tendsto (fun n => Real.log 2/T.time n+
      Cp*((completionIndex xi (T.time n) : ℝ)/T.time n+1/T.time n)+
      Cs*(((d n : ℝ)+1)*Real.log ((d n : ℝ)+2)/T.time n)) atTop (𝓝 0) := by
    simpa using (hlog2.add ((hk.add h1).const_mul Cp)).add (horder.const_mul Cs)
  apply squeeze_zero (fun n => div_nonneg (Real.log_nonneg (by
    have h : 0 ≤ ‖nativeAuxiliaryStableVector (completionIndex xi (T.time n)) (d n)‖/
        ‖auxRationalFactor (completionIndex xi (T.time n)) ((rho : ℂ)-1/2)‖ :=
      div_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith)) (T.positive n).le) _ hu
  intro n
  let k := completionIndex xi (T.time n)
  let B := Cp*((k : ℝ)+1)+Cs*((d n : ℝ)+1)*Real.log ((d n : ℝ)+2)
  have hB : 0 ≤ B := by
    have hlog : 0 ≤ Real.log ((d n : ℝ)+2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (d n)])
    dsimp [B]
    positivity
  have hb : ‖nativeAuxiliaryStableVector k (d n)‖/‖auxRationalFactor k ((rho : ℂ)-1/2)‖ ≤
      Real.exp B := hbound k (d n) (completionIndex_one_le xi (T.time n))
  have he : 1 ≤ Real.exp B := Real.one_le_exp hB
  have hbig : 1+‖nativeAuxiliaryStableVector k (d n)‖/‖auxRationalFactor k ((rho : ℂ)-1/2)‖ ≤
      2*Real.exp B := by
    linarith
  have hpos : 0 < 1+‖nativeAuxiliaryStableVector k (d n)‖/‖auxRationalFactor k ((rho : ℂ)-1/2)‖ :=
    by positivity
  have hlog := Real.log_le_log hpos hbig
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hlog
  exact (div_le_div_of_nonneg_right hlog (T.positive n).le).trans_eq (by dsimp [B,k]; ring)

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeInputSurvival supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem actual_completed_input_eventually_half_leading (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    (rho : zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re)
    (xi : ℝ) (hxi : 0 ≤ xi) :
    ∀ᶠ n : ℕ in atTop,
      ‖nativeAuxiliaryStableVector (completionIndex xi (T.time n)) (d n)‖ ≤
        nativeMultiplicityTailConstant (d n) rho*
          ‖auxRationalFactor (completionIndex xi (T.time n)) ((rho : ℂ)-1/2)‖*
            Real.exp (((rho : ℂ)-1/2).re*T.time n)/2 := by
  let delta : ℝ := ((rho : ℂ)-1/2).re
  have hdelta : 0 < delta := by
    change 0 < ((rho : ℂ)-1/2).re
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hQ := actualInput_rational_ratio_log_rate_zero T d hd rho hright xi hxi
  have hD := multiplicityTailConstant_log_div_time_tendsto_zero T d hd rho hright
  have hDiff := hQ.sub hD
  have hSmall : ∀ᶠ n : ℕ in atTop,
      (Real.log (1+‖nativeAuxiliaryStableVector (completionIndex xi (T.time n)) (d n)‖/
          ‖auxRationalFactor (completionIndex xi (T.time n)) ((rho : ℂ)-1/2)‖)-
        Real.log (nativeMultiplicityTailConstant (d n) rho))/T.time n < delta/2 := by
    have h := (tendsto_order.1 hDiff).2 (delta/2) (by linarith)
    simpa only [←sub_div,sub_zero] using h
  filter_upwards [hSmall,T.cofinal.eventually_ge_atTop (2*Real.log 2/delta)] with n hn hTime
  let k := completionIndex xi (T.time n)
  let D := nativeMultiplicityTailConstant (d n) rho
  let R := ‖auxRationalFactor k ((rho : ℂ)-1/2)‖
  let Q := ‖nativeAuxiliaryStableVector k (d n)‖/R
  have hDp : 0 < D := nativeMultiplicityTailConstant_pos (d n) rho hright
  have hRp : 0 < R := by
    apply norm_pos_iff.mpr
    apply auxRationalFactor_ne_zero
    · simpa only [delta] using hdelta
    · exact auxiliary_centered_zero_ne_half rho
  have hQp : 0 < 1+Q := by dsimp [Q]; positivity
  have hCost : Real.log (1+Q)-Real.log D < delta/2*T.time n :=
    (div_lt_iff₀ (T.positive n)).mp hn
  have hLog2 : Real.log 2 ≤ delta/2*T.time n := by
    have h := (div_le_iff₀ hdelta).mp hTime
    nlinarith
  have hLog : Real.log (1+Q) ≤ Real.log D+delta*T.time n-Real.log 2 := by linarith
  have he := (Real.log_le_iff_le_exp hQp).mp hLog
  rw [Real.exp_sub,Real.exp_add,Real.exp_log hDp,Real.exp_log (by norm_num : (0 : ℝ)<2)] at he
  have hRatio : Q ≤ D*Real.exp (delta*T.time n)/2 := by linarith
  have hFinal := (div_le_iff₀ hRp).mp hRatio
  exact hFinal.trans_eq (by dsimp [D,R,delta]; ring)

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeMemoryLower supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem actual_terminal_memory_eventually_ge_exp
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    (rho : zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re)
    (xi : ℝ) (hxi : 0 ≤ xi) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((((rho : ℂ)-1/2).re-xi-epsilon)*T.time n) ≤
        tailMemory (auxCompletionAlpha (completionIndex xi (T.time n))) (d n) (T.time n) := by
  obtain ⟨Cp,hCp,hCpBound⟩ := aux_completion_ratio_bounds rho hright
  have hSurvival := actual_completed_input_eventually_half_leading T d hd rho hright xi hxi
  have hD := multiplicityTailConstant_log_div_time_tendsto_zero T d hd rho hright
  have hSmallD := (tendsto_order.1 hD).1 (-epsilon/3) (by linarith)
  have hCost := T.cofinal.eventually
    (completionCost_eventually_lt xi Cp hxi (show 0<epsilon/3 by linarith))
  have hLog2 : Tendsto (fun n => Real.log 2/T.time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop T.cofinal
  have hSmallLog2 := (tendsto_order.1 hLog2).2 (epsilon/3) (by linarith)
  filter_upwards [hSurvival,hSmallD,hCost,hSmallLog2] with n hSurvival hSmallD hCost hSmallLog2
  let k := completionIndex xi (T.time n)
  let D := nativeMultiplicityTailConstant (d n) rho
  let R := ‖auxRationalFactor k ((rho : ℂ)-1/2)‖
  let A := auxCompletionBound k
  let delta := ((rho : ℂ)-1/2).re
  let E := Real.exp (delta*T.time n)
  let cost := (k : ℝ)*Real.log ((k : ℝ)+1)+Cp*((k : ℝ)+1)
  let M := max (D*R*E-‖nativeAuxiliaryStableVector k (d n)‖) 0
  have hk : 1 ≤ k := completionIndex_one_le xi (T.time n)
  have hDp : 0 < D := nativeMultiplicityTailConstant_pos (d n) rho hright
  have hAp : 0 < A := auxCompletionBound_pos k hk
  have hM : 0 ≤ M := le_max_right _ _
  have hhalf : D*R*E/2 ≤ M := by
    have h := le_max_left (D*R*E-‖nativeAuxiliaryStableVector k (d n)‖) 0
    change ‖nativeAuxiliaryStableVector k (d n)‖ ≤ D*R*E/2 at hSurvival
    linarith
  have hsqrt : 1 ≤ Real.sqrt (2*auxCompletionAlpha k) := by
    have hAlpha : (1 : ℝ) ≤ 2*auxCompletionAlpha k := by
      dsimp [auxCompletionAlpha]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hAlpha
  have hNum : D*R*E/2 ≤ Real.sqrt (2*auxCompletionAlpha k)*M :=
    hhalf.trans (le_mul_of_one_le_left hM hsqrt)
  have hNorm : D/2*(R/A)*E ≤ Real.sqrt (2*auxCompletionAlpha k)/A*M := by
    calc
      _ = (D*R*E/2)/A := by ring
      _ ≤ (Real.sqrt (2*auxCompletionAlpha k)*M)/A := div_le_div_of_nonneg_right hNum hAp.le
      _ = _ := by ring
  have hA6 : Real.sqrt (2*auxCompletionAlpha k)/A*M ≤
      tailMemory (auxCompletionAlpha k) (d n) (T.time n) :=
    native_terminal_memory_lower k (d n) hk rho hright (T.time n)
  have hR : Real.exp (-cost) ≤ R/A := by
    convert (hCpBound k hk).2.2 using 1
    congr 1
    dsimp [cost]
    ring
  have hExponent : (delta-xi-epsilon)*T.time n ≤
      Real.log D-Real.log 2+delta*T.time n-cost := by
    have hD' := (lt_div_iff₀ (T.positive n)).mp hSmallD
    have hCost' := (div_lt_iff₀ (T.positive n)).mp hCost
    have hLog2' := (div_lt_iff₀ (T.positive n)).mp hSmallLog2
    change -epsilon/3*T.time n < Real.log D at hD'
    change cost < (xi+epsilon/3)*T.time n at hCost'
    nlinarith
  calc
    _ ≤ Real.exp (Real.log D-Real.log 2+delta*T.time n-cost) := Real.exp_le_exp.mpr hExponent
    _ = D/2*Real.exp (-cost)*E := by
      simp only [Real.exp_sub,Real.exp_add,Real.exp_log hDp,
        Real.exp_log (by norm_num : (0 : ℝ)<2),Real.exp_neg,E]
      ring
    _ ≤ D/2*(R/A)*E := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by positivity)) (Real.exp_nonneg _)
    _ ≤ _ := hNorm.trans hA6

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeOldMemoryRate supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem actual_old_memory_eventually_le_exp
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    (xi : ℝ) (hxi : 0 ≤ xi) {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (∫ s : ℝ in Icc 0 (T.time n-C*Real.log (T.time n)),
        Real.exp (-auxCompletionAlpha (completionIndex xi (T.time n))*(T.time n-s))*
          |primeFieldFamily (d n) s|) ≤
        Real.exp ((nativeZeroDisplacementSup-C*xi+epsilon)*T.time n) := by
  have hlog : Tendsto (fun n => Real.log (T.time n)/T.time n) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => Real.log t/t) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    exact h.comp T.cofinal
  have hK := fieldEnvelope_log_div_time_tendsto_zero T d hd
  have hAlpha := (actualCompletionAlpha_log_scale_tendsto xi hxi).comp T.cofinal
  have hRate : Tendsto (fun n =>
      (Real.log (T.time n)+Real.log (1+nativeFieldOrderConstant (d n))+
        nativeZeroDisplacementSup*T.time n-
        (auxCompletionAlpha (completionIndex xi (T.time n))+nativeZeroDisplacementSup)*C*Real.log (T.time n))/T.time n)
      atTop (𝓝 (nativeZeroDisplacementSup-C*xi)) := by
    have h := ((hlog.add hK).add_const nativeZeroDisplacementSup).sub
      ((hAlpha.add (hlog.const_mul nativeZeroDisplacementSup)).const_mul C)
    convert h using 1
    · ext n
      simp only [Function.comp_apply]
      field_simp [(T.positive n).ne'] <;> ring
    · ring_nf
  have hSmall := (tendsto_order.1 hRate).2 (nativeZeroDisplacementSup-C*xi+epsilon) (by linarith)
  have hStart := T.cofinal.eventually (windowStart_eventually_nonneg C)
  filter_upwards [hSmall,hStart] with n hn hs
  let k := completionIndex xi (T.time n)
  have hAlpha0 : 0 ≤ auxCompletionAlpha k := by dsimp [auxCompletionAlpha]; positivity
  have hNative := native_oldMemory_upper (d n) hAlpha0 hC hs.1 hs.2
  obtain ⟨A,hA,hEnv⟩ := native_field_theta_envelope
  have hKp := (hEnv (d n)).1
  have hExp : Real.log (T.time n)+Real.log (1+nativeFieldOrderConstant (d n))+
      nativeZeroDisplacementSup*T.time n-
      (auxCompletionAlpha k+nativeZeroDisplacementSup)*C*Real.log (T.time n) ≤
      (nativeZeroDisplacementSup-C*xi+epsilon)*T.time n :=
    ((div_lt_iff₀ (T.positive n)).mp hn).le
  calc
    _ ≤ T.time n*nativeFieldOrderConstant (d n)*
        Real.exp (nativeZeroDisplacementSup*T.time n-
          (auxCompletionAlpha k+nativeZeroDisplacementSup)*C*Real.log (T.time n)) := hNative
    _ ≤ T.time n*(1+nativeFieldOrderConstant (d n))*
        Real.exp (nativeZeroDisplacementSup*T.time n-
          (auxCompletionAlpha k+nativeZeroDisplacementSup)*C*Real.log (T.time n)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left (by linarith) (T.positive n).le
    _ = Real.exp (Real.log (T.time n)+Real.log (1+nativeFieldOrderConstant (d n))+
        nativeZeroDisplacementSup*T.time n-
        (auxCompletionAlpha k+nativeZeroDisplacementSup)*C*Real.log (T.time n)) := by
      simp only [Real.exp_sub,Real.exp_add,Real.exp_log (T.positive n),
        Real.exp_log (by linarith : 0 < 1+nativeFieldOrderConstant (d n))]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hExp

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeWindowLowerRate supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem actual_window_rate_eventually_gt_of_right_zero
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    (rho : zetaZeroConfig.carrier) (hright : 1/2 < (rho : ℂ).re)
    (xi : ℝ) (hxi : 0 ≤ xi) {C b : ℝ} (hC : 0 < C)
    (hmargin : nativeZeroDisplacementSup-C*xi < ((rho : ℂ)-1/2).re-xi)
    (hb : b < ((rho : ℂ)-1/2).re-xi) :
    ∀ᶠ n : ℕ in atTop, b < nativeWindowLogRate (d n) C (T.time n) := by
  let delta := ((rho : ℂ)-1/2).re
  let eps := min ((delta-xi-b)/2) ((delta-xi-(nativeZeroDisplacementSup-C*xi))/4)
  change nativeZeroDisplacementSup-C*xi < delta-xi at hmargin
  change b < delta-xi at hb
  have heps : 0 < eps := by
    change 0 < min ((delta-xi-b)/2) ((delta-xi-(nativeZeroDisplacementSup-C*xi))/4)
    exact lt_min (by linarith) (by linarith)
  let L := delta-xi-eps
  let U := nativeZeroDisplacementSup-C*xi+eps
  have hLb : b < L := by
    have h := min_le_left ((delta-xi-b)/2) ((delta-xi-(nativeZeroDisplacementSup-C*xi))/4)
    change eps ≤ (delta-xi-b)/2 at h
    dsimp [L]
    change b < delta-xi at hb
    linarith
  have hUL : U < L := by
    have h := min_le_right ((delta-xi-b)/2) ((delta-xi-(nativeZeroDisplacementSup-C*xi))/4)
    change eps ≤ (delta-xi-(nativeZeroDisplacementSup-C*xi))/4 at h
    change nativeZeroDisplacementSup-C*xi < delta-xi at hmargin
    dsimp [L,U]
    linarith
  have hLower := actual_terminal_memory_eventually_ge_exp T d hd rho hright xi hxi heps
  have hOld := actual_old_memory_eventually_le_exp T d hd xi hxi hC.le heps
  have hStart := T.cofinal.eventually (windowStart_eventually_nonneg C)
  have hTime := T.cofinal.eventually_ge_atTop (Real.log 2/(L-U))
  have hError : Tendsto (fun n => (Real.log (4*C)+Real.log (T.time n))/(2*T.time n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun n => Real.log (4*C)/T.time n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop T.cofinal
    have hl : Tendsto (fun n => Real.log (T.time n)/T.time n) atTop (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => Real.log t/t) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
      exact h.comp T.cofinal
    have h := (hc.add hl).div_const 2
    convert h using 1
    · ext n; ring
    · norm_num
  have hSmallError := (tendsto_order.1 hError).2 (L-b) (by linarith)
  filter_upwards [hLower,hOld,hStart,hTime,hSmallError] with n hLower hOld hs hTime hSmallError
  have hTp := T.positive n
  let k := completionIndex xi (T.time n)
  let W := ∫ s : ℝ in Icc (T.time n-C*Real.log (T.time n)) (T.time n),
    Real.exp (-auxCompletionAlpha k*(T.time n-s))*|primeFieldFamily (d n) s|
  let O := ∫ s : ℝ in Icc 0 (T.time n-C*Real.log (T.time n)),
    Real.exp (-auxCompletionAlpha k*(T.time n-s))*|primeFieldFamily (d n) s|
  have hOldSmall : O ≤ Real.exp (L*T.time n)/2 := by
    have hNum := (div_le_iff₀ (sub_pos.mpr hUL)).mp hTime
    have hExp : U*T.time n ≤ L*T.time n-Real.log 2 := by nlinarith
    calc
      O ≤ Real.exp (U*T.time n) := hOld
      _ ≤ Real.exp (L*T.time n-Real.log 2) := Real.exp_le_exp.mpr hExp
      _ = _ := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  have hSplit := tailMemory_split (d n) (auxCompletionAlpha k) C (T.time n) hC.le hs.1 hs.2
  have hWin : Real.exp (L*T.time n)/2 ≤ W := by
    change Real.exp (L*T.time n) ≤ tailMemory (auxCompletionAlpha k) (d n) (T.time n) at hLower
    change tailMemory (auxCompletionAlpha k) (d n) (T.time n) = O+W at hSplit
    linarith
  have hAlpha : 0 ≤ auxCompletionAlpha k := by dsimp [auxCompletionAlpha]; positivity
  have hCS := native_terminalMemory_sq_le_windowEnergy (d n) hAlpha hC.le hs.1
  have hEnergy : Real.exp (2*L*T.time n)/4 ≤ C*Real.log (T.time n)*nativeWindowEnergy (d n) C (T.time n) := by
    calc
      _ = (Real.exp (L*T.time n)/2)^2 := by
        rw [div_pow,←Real.exp_nat_mul]
        congr 1 <;> ring
      _ ≤ W^2 := pow_le_pow_left₀ (by positivity) hWin 2
      _ ≤ _ := hCS
  have hE0 := nativeWindowEnergy_nonneg (d n) C (T.time n)
  have hlogT : Real.log (T.time n) ≤ T.time n :=
    (Real.log_le_sub_one_of_pos (T.positive n)).trans (by linarith)
  have hSpan := mul_le_mul_of_nonneg_left hlogT hC.le
  have hSpanE := mul_le_mul_of_nonneg_right hSpan hE0
  have hBig : Real.exp (2*L*T.time n) ≤
      (4*C*T.time n)*(1+nativeWindowEnergy (d n) C (T.time n)) := by
    nlinarith [mul_nonneg hC.le (T.positive n).le]
  have hLog := Real.log_le_log (Real.exp_pos _) hBig
  rw [Real.log_exp,Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (T.positive n).ne'] at hLog
  have hRate : L-(Real.log (4*C)+Real.log (T.time n))/(2*T.time n) ≤
      nativeWindowLogRate (d n) C (T.time n) := by
    unfold nativeWindowLogRate
    have h : (2*L*T.time n-(Real.log (4*C)+Real.log (T.time n)))/(2*T.time n) ≤
        Real.log (1+nativeWindowEnergy (d n) C (T.time n))/(2*T.time n) :=
      div_le_div_of_nonneg_right (by linarith [hLog]) (by positivity)
    convert h using 1 <;> field_simp [(T.positive n).ne'] <;> ring
  exact lt_of_lt_of_le (by linarith [hSmallError]) hRate

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

/-! NativeWindowRateComplete supporting proofs. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

theorem slowSourceSchedule_window_rate
    (T : HorizonSchedule) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0))
    {C : ℝ} (hC : 1 < C) :
    Tendsto (fun n => nativeWindowLogRate (d n) C (T.time n)) atTop (𝓝 nativeZeroDisplacementSup) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    by_cases hb0 : b < 0
    · exact Eventually.of_forall fun n => hb0.trans_le
        (nativeWindowLogRate_nonneg (d n) C (T.time n) (T.positive n))
    · have hb0' : 0 ≤ b := le_of_not_gt hb0
      let q := (nativeZeroDisplacementSup+(C-1)*b)/C
      have hC0 : 0 < C := by linarith
      have hq0 : 0 ≤ q := div_nonneg
        (add_nonneg native_zero_sup_bounds.1 (mul_nonneg (by linarith) hb0')) hC0.le
      have hq : q < nativeZeroDisplacementSup := by
        apply (div_lt_iff₀ hC0).mpr
        nlinarith
      obtain ⟨rho,hrho⟩ := native_zero_sup_bounds.2.2.2 q hq0 hq
      have hright : 1/2 < (rho : ℂ).re := by linarith
      let delta := ((rho : ℂ)-1/2).re
      have hdelta_re : delta = (rho : ℂ).re-1/2 := by
        change ((rho : ℂ)-1/2).re = (rho : ℂ).re-1/2
        simp only [Complex.sub_re]
        norm_num
      have hDelta : nativeZeroDisplacementSup+(C-1)*b < C*delta := by
        have h := (div_lt_iff₀ hC0).mp hrho
        rw [hdelta_re]
        nlinarith
      obtain ⟨xi,hLow,hHigh⟩ := nativeWindow_rate_parameter_interval hC hDelta
      have hDeltaTheta : delta ≤ nativeZeroDisplacementSup := by
        rw [hdelta_re]
        exact (le_max_left _ _).trans (native_zero_sup_bounds.2.2.1 rho)
      have hxi : 0 ≤ xi := (div_nonneg (sub_nonneg.mpr hDeltaTheta) (by linarith)).trans hLow.le
      have hMargins := nativeWindow_rate_exponent_margin hC hLow hHigh
      exact actual_window_rate_eventually_gt_of_right_zero T d hd rho hright xi hxi hC0
        hMargins.1 hMargins.2
  · intro b hb
    have h := slowSource_window_rate_eventually_lt_theta_add T d hd
      (show 0 ≤ C by linarith) (show 0 < b-nativeZeroDisplacementSup by linarith)
    exact h.mono fun n hn => by linarith

def normalizedHorizonSchedule (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) : HorizonSchedule where
  time n := max 1 (time n)
  positive n := zero_lt_one.trans_le (le_max_left _ _)
  cofinal := tendsto_atTop.2 (fun b =>
    (cofinal.eventually_ge_atTop b).mono fun n hn => hn.trans (le_max_right _ _))

theorem slowSourceRealHorizons_window_rate
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) (d : ℕ → ℕ)
    (slow : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/time n) atTop (𝓝 0))
    {C : ℝ} (hC : 1 < C) :
    Tendsto (fun n => nativeWindowLogRate (d n) C (time n)) atTop (𝓝 nativeZeroDisplacementSup) := by
  let T := normalizedHorizonSchedule time cofinal
  have hEq : ∀ᶠ n : ℕ in atTop, T.time n=time n :=
    (cofinal.eventually_ge_atTop 1).mono fun n hn => max_eq_right hn
  have hd : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/T.time n) atTop (𝓝 0) := by
    apply slow.congr'
    filter_upwards [hEq] with n hn
    rw [hn]
  have h := slowSourceSchedule_window_rate T d hd hC
  apply h.congr'
  filter_upwards [hEq] with n hn
  rw [hn]

theorem fixedSource_continuous_window_rate (d : ℕ) {C : ℝ} (hC : 1 < C) :
    Tendsto (fun T : ℝ => nativeWindowLogRate d C T) atTop (𝓝 nativeZeroDisplacementSup) := by
  apply tendsto_of_seq_tendsto
  intro time hTime
  have hSlow : Tendsto (fun n => (d : ℝ)*Real.log ((d : ℝ)+2)/time n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hTime
  exact slowSourceRealHorizons_window_rate time hTime (fun _ => d) hSlow hC

end Zeta23.OPICAFollowup.NativeWindowProof.Asymptotic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup

/-- Original J5.2 primary: every fixed native source order, every C>1 and
continuous real horizons, including zero supremum and arbitrary multiplicity. -/
theorem native_fixed_source_window_rate (d : ℕ) (C : ℝ) (hC : 1 < C) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  NativeWindowProof.Asymptotic.fixedSource_continuous_window_rate d hC

#print axioms native_fixed_source_window_rate
end Zeta23.OPICAFollowup
