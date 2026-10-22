import Zeta23.OPICAFollowup.RenormalizedCoPoisson
import Zeta23.OPICA.SignedHeatSeparator
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
UNCHECKED primary candidate at 9b6a9a3. The density is the actual inclusive
finite-power-sum density, not a synthetic negative test. Both signs of gamma
and delta=0 are retained. The measure construction remains a separate root.
-/
noncomputable section
open Set MeasureTheory Filter
open Zeta23.OPICA
open scoped Topology
namespace Zeta23.OPICAFollowup

def firstCellLowerLog (gamma : ℝ) : ℝ := 4*Real.pi/(3*|gamma|)
def firstCellUpperLog (gamma : ℝ) : ℝ := 5*Real.pi/(3*|gamma|)
def firstCellNegativePart (delta gamma x : ℝ) : ℝ :=
  max (-coPoissonRealDensity (coPoissonRho delta gamma) x) 0

def firstCellNegativeMass (delta gamma : ℝ) : ℝ :=
  ∫ x in Real.exp (firstCellLowerLog gamma)..Real.exp (firstCellUpperLog gamma),
    firstCellNegativePart delta gamma x

def firstCellNegativeSincMass (delta gamma : ℝ) : ℝ :=
  ∫ x in Real.exp (firstCellLowerLog gamma)..Real.exp (firstCellUpperLog gamma),
    sincSquared x*firstCellNegativePart delta gamma x

lemma firstCellLog_geometry (gamma : ℝ) (hg : 16≤|gamma|) :
    0<firstCellLowerLog gamma ∧ firstCellLowerLog gamma<firstCellUpperLog gamma ∧
    firstCellUpperLog gamma<1/3 ∧ firstCellUpperLog gamma<Real.log (3/2) ∧
    ∀ u∈Icc (firstCellLowerLog gamma) (firstCellUpperLog gamma),
      0<u ∧ Real.exp u<3/2 ∧ u<Real.log 2 := by
  have hgp : 0<|gamma| := by linarith
  have hpi := Real.pi_lt_d2
  have hlo : 0<firstCellLowerLog gamma := by unfold firstCellLowerLog; positivity
  have hlt : firstCellLowerLog gamma<firstCellUpperLog gamma := by
    unfold firstCellLowerLog firstCellUpperLog
    apply (div_lt_div_iff_of_pos_right (by positivity : 0<3*|gamma|)).mpr
    linarith [Real.pi_pos]
  have hupper : firstCellUpperLog gamma<1/3 := by
    unfold firstCellUpperLog
    apply (div_lt_iff₀ (by positivity : 0<3*|gamma|)).mpr
    nlinarith
  have hlog : (1/3:ℝ)≤Real.log (3/2) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2)
    norm_num at h ⊢
    exact h
  have hlog2 : Real.log (3/2)<Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨hlo,hlt,hupper,hupper.trans_le hlog,?_⟩
  intro u hu
  have hh := hu.2.trans_lt (hupper.trans_le hlog)
  exact ⟨hlo.trans_le hu.1,
    (Real.exp_lt_exp.mpr hh).trans_eq (Real.exp_log (by norm_num)),hh.trans hlog2⟩

lemma firstCell_sine_bound (G u : ℝ) (hG : 0<G)
    (hu : u∈Icc (4*Real.pi/(3*G)) (5*Real.pi/(3*G))) :
    Real.sin (G*u)≤-3/4 := by
  have hangle : 4*Real.pi/3≤G*u ∧ G*u≤5*Real.pi/3 := by
    constructor
    · have h := (div_le_iff₀ (by positivity : 0<3*G)).mp hu.1
      nlinarith
    · have h := (le_div_iff₀ (by positivity : 0<3*G)).mp hu.2
      nlinarith
  let v := G*u-3*Real.pi/2
  have hv : |v|≤Real.pi/6 := by dsimp [v]; apply abs_le.mpr; constructor <;> linarith
  have hv2 : v^2≤(Real.pi/6)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg v) hv 2
  have hcos := Real.one_sub_sq_div_two_le_cos v
  have hpi := Real.pi_lt_d2
  have hsmall : (Real.pi/6)^2<1/2 := by nlinarith [Real.pi_pos]
  have hs : Real.sin (G*u) = -Real.cos v := by
    rw [show G*u=v+(Real.pi+Real.pi/2) by dsimp [v]; ring,
      Real.sin_add,Real.sin_add_pi,Real.cos_add_pi,Real.sin_pi_div_two,Real.cos_pi_div_two]
    ring
  rw [hs]
  nlinarith

lemma sinh_abs_le_exp_abs (x : ℝ) : |Real.sinh x|≤Real.exp |x| := by
  rw [Real.sinh_eq]
  have he1 : Real.exp x≤Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have he2 : Real.exp (-x)≤Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  have ht := abs_sub (Real.exp x) (Real.exp (-x))
  rw [abs_of_pos (Real.exp_pos x),abs_of_pos (Real.exp_pos (-x))] at ht
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  linarith

lemma firstCell_density_upper (delta gamma u : ℝ) (hd : |delta|<1/2)
    (hg : 16≤|gamma|)
    (hu : u∈Icc (firstCellLowerLog gamma) (firstCellUpperLog gamma)) :
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u) ≤
      -|gamma|*Real.exp (-u/2)/2 := by
  have hgp : 0<|gamma| := by linarith
  have hgne : gamma≠0 := abs_pos.mp hgp
  obtain ⟨_,_,hub,_,hgeometry⟩ := firstCellLog_geometry gamma hg
  obtain ⟨hup,hexp,hu2⟩ := hgeometry u hu
  have hu3 : u<1/3 := hu.2.trans_lt hub
  rw [coPoisson_first_cell_gamma_abs delta gamma u hgne hup hu2,
    coPoisson_first_cell_real delta |gamma| u hgp.ne' hup hu2]
  simp only [sq_abs]
  let v : ℝ := 1/(4*(delta^2+gamma^2))
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by
    dsimp [v]
    apply (div_le_iff₀ (by nlinarith [sq_pos_of_ne_zero hgne] : 0<4*(delta^2+gamma^2))).mpr
    have hg2 : (16:ℝ)^2≤gamma^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16) hg 2
    nlinarith [sq_nonneg delta]
  have hδu : |delta*u|<1/6 := by
    rw [abs_mul,abs_of_pos hup]
    nlinarith [abs_nonneg delta]
  have he : Real.exp |delta*u|<3/2 := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2)
    have hlt : |delta*u|<Real.log (3/2) := by norm_num at hl; linarith
    exact (Real.exp_lt_exp.mpr hlt).trans_eq (Real.exp_log (by norm_num))
  have hosc : |delta*(v-1)*Real.sinh (delta*u)*Real.cos (|gamma|*u)|≤1 := by
    have hv : |v-1|≤1 := by apply abs_le.mpr; constructor <;> linarith
    rw [abs_mul,abs_mul,abs_mul]
    have hs := (sinh_abs_le_exp_abs (delta*u)).trans he.le
    have hc := Real.abs_cos_le_one (|gamma|*u)
    calc
      _ ≤ (1/2:ℝ)*1*(3/2)*1 := by gcongr
      _ ≤ 1 := by norm_num
  have hsin : Real.sin (|gamma|*u)≤-3/4 := firstCell_sine_bound |gamma| u hgp hu
  have hcosh : 1≤Real.cosh (delta*u) := Real.one_le_cosh _
  have hcoef : |gamma|≤|gamma|*(1+v)*Real.cosh (delta*u) := by
    nlinarith [mul_nonneg hgp.le hv0,mul_nonneg (mul_nonneg hgp.le (by linarith : 0≤1+v))
      (sub_nonneg.mpr hcosh)]
  have hterm : |gamma|*(1+v)*Real.cosh (delta*u)*Real.sin (|gamma|*u)≤-3*|gamma|/4 := by
    calc
      _ ≤ (|gamma|*(1+v)*Real.cosh (delta*u))*(-3/4) :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      _ ≤ _ := by nlinarith
  have hsum : delta*(v-1)*Real.sinh (delta*u)*Real.cos (|gamma|*u)+
      |gamma|*(1+v)*Real.cosh (delta*u)*Real.sin (|gamma|*u)≤-|gamma|/2 := by
    have := (le_abs_self (delta*(v-1)*Real.sinh (delta*u)*Real.cos (|gamma|*u))).trans hosc
    linarith
  change Real.exp (-u/2)*(_+_)≤_
  simpa only [mul_div_assoc,mul_comm (Real.exp (-u/2))] using
    mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)

lemma coPoissonRealDensity_continuousOn_firstCell (delta gamma : ℝ) (hg : gamma≠0) :
    ContinuousOn (coPoissonRealDensity (coPoissonRho delta gamma)) (Ioo (1:ℝ) 2) := by
  have hlog : ContinuousOn Real.log (Ioo (1:ℝ) 2) :=
    fun x hx => (Real.continuousAt_log (by linarith : x≠0)).continuousWithinAt
  have heq (x : ℝ) (hx : x∈Ioo (1:ℝ) 2) :=
    coPoisson_first_cell_real delta gamma (Real.log x) hg
      (Real.log_pos hx.1) (Real.log_lt_log (by linarith : 0<x) hx.2)
  have hcont : ContinuousOn (fun x : ℝ => Real.exp (-Real.log x/2)*
      (delta*(1/(4*(delta^2+gamma^2))-1)*Real.sinh (delta*Real.log x)*Real.cos (gamma*Real.log x)+
       gamma*(1+1/(4*(delta^2+gamma^2)))*Real.cosh (delta*Real.log x)*Real.sin (gamma*Real.log x)))
      (Ioo (1:ℝ) 2) := by fun_prop
  exact hcont.congr (fun x hx => (by simpa only [Real.exp_log (show 0<x by linarith [hx.1])] using heq x hx).symm)

lemma firstCell_interval_integrable (delta gamma : ℝ) (hg : 16≤|gamma|) :
    IntervalIntegrable (firstCellNegativePart delta gamma) volume
      (Real.exp (firstCellLowerLog gamma)) (Real.exp (firstCellUpperLog gamma)) ∧
    IntervalIntegrable (fun x => sincSquared x*firstCellNegativePart delta gamma x) volume
      (Real.exp (firstCellLowerLog gamma)) (Real.exp (firstCellUpperLog gamma)) := by
  obtain ⟨ha,hab,hb,hblog,hgeometry⟩ := firstCellLog_geometry gamma hg
  have hsub : Icc (Real.exp (firstCellLowerLog gamma)) (Real.exp (firstCellUpperLog gamma))⊆Ioo (1:ℝ) 2 := by
    intro x hx
    have hl := Real.one_lt_exp_iff.mpr ha
    have hu := (hgeometry (firstCellUpperLog gamma) ⟨hab.le,le_rfl⟩).2.1
    constructor <;> linarith
  have hc := (coPoissonRealDensity_continuousOn_firstCell delta gamma (by
    have : 0<|gamma| := by linarith
    exact abs_pos.mp this)).mono hsub
  have hn : ContinuousOn (firstCellNegativePart delta gamma)
      (Icc (Real.exp (firstCellLowerLog gamma)) (Real.exp (firstCellUpperLog gamma))) :=
    hc.neg.max continuousOn_const
  constructor
  · exact hn.intervalIntegrable (Real.exp_le_exp.mpr hab.le)
  · exact (sincSquared_continuous.continuousOn.mul hn).intervalIntegrable (Real.exp_le_exp.mpr hab.le)

lemma firstCell_sinc_lower (gamma u : ℝ) (hg : 16≤|gamma|)
    (hu : u∈Icc (firstCellLowerLog gamma) (firstCellUpperLog gamma)) :
    16/(9*gamma^2)≤sincSquared (Real.exp u) := by
  obtain ⟨ha,hab,hb,hblog,hgeometry⟩ := firstCellLog_geometry gamma hg
  obtain ⟨hup,hxupper,hu2⟩ := hgeometry u hu
  have hgpos : 0<|gamma| := by linarith
  have hgap : firstCellLowerLog gamma≤Real.exp u-1 := by
    have hh := Real.add_one_le_exp u
    linarith [hu.1]
  have hdhalf : firstCellLowerLog gamma≤1/2 := by linarith
  have hxlow : 1<Real.exp u := Real.one_lt_exp_iff.mpr hup
  have hdist (n : ℤ) : firstCellLowerLog gamma≤|Real.exp u-(n:ℝ)| := by
    by_cases hn : n≤1
    · have hn' : (n:ℝ)≤1 := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hn' : (2:ℝ)≤n := by exact_mod_cast (show (2:ℤ)≤n by omega)
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hs := sine_abs_lower_of_integer_distance ha hdist
  have hs2 : 4*(firstCellLowerLog gamma)^2≤Real.sin (Real.pi*Real.exp u)^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0≤2*firstCellLowerLog gamma) hs 2
    simpa only [sq_abs,mul_pow] using h
  have hx2 : (Real.exp u)^2≤4 := by nlinarith [Real.exp_pos u]
  have hid : sincSquared (Real.exp u)*(Real.pi^2*(Real.exp u)^2)=
      Real.sin (Real.pi*Real.exp u)^2 := by
    rw [sincSquared,Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero (Real.exp_ne_zero u)),div_pow]
    field_simp
  have hfinal : (firstCellLowerLog gamma)^2/Real.pi^2≤sincSquared (Real.exp u) := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [sincSquared_nonneg (Real.exp u)]
  convert hfinal using 1
  unfold firstCellLowerLog
  rw [div_pow,mul_pow,sq_abs]
  field_simp
  ring

/-- Full first-cell correction-cost root. The two costs integrate the actual
negative part, with the heat-normalized sinc-squared weight in the second. -/
theorem first_cell_negative_mass_cost (delta gamma : ℝ) (hd : |delta|<1/2)
    (hg : 16≤|gamma|) :
    (∀ u∈Icc (firstCellLowerLog gamma) (firstCellUpperLog gamma),
      coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)≤
        -|gamma|*Real.exp (-u/2)/2) ∧
    Real.pi/6≤firstCellNegativeMass delta gamma ∧
    8*Real.pi/(27*gamma^2)≤firstCellNegativeSincMass delta gamma := by
  have hp := firstCell_density_upper delta gamma
  have hint := firstCell_interval_integrable delta gamma hg
  obtain ⟨ha,hab,hb,hblog,hgeometry⟩ := firstCellLog_geometry gamma hg
  have hexpab := Real.exp_le_exp.mpr hab.le
  have hcont : ContinuousOn (firstCellNegativePart delta gamma)
      (Real.exp '' uIcc (firstCellLowerLog gamma) (firstCellUpperLog gamma)) := by
    apply ((coPoissonRealDensity_continuousOn_firstCell delta gamma (by
      have h : 0<|gamma| := by linarith
      exact abs_pos.mp h)).neg.max continuousOn_const).mono
    rintro x ⟨u,hu,rfl⟩
    rw [uIcc_of_le hab.le] at hu
    have h := hgeometry u hu
    exact ⟨Real.one_lt_exp_iff.mpr h.1,by linarith [h.2.1]⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv' (f := Real.exp) (f' := Real.exp)
    (g := firstCellNegativePart delta gamma)
    (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hcont
  have hm : Real.pi/6≤firstCellNegativeMass delta gamma := by
    unfold firstCellNegativeMass
    rw [←hsub]
    calc
      Real.pi/6 = ∫ u in firstCellLowerLog gamma..firstCellUpperLog gamma, |gamma|/2 := by
        rw [intervalIntegral.integral_const]
        unfold firstCellLowerLog firstCellUpperLog
        rw [smul_eq_mul]
        field_simp
        ring
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hab.le
          (intervalIntegrable_const) ((hcont.comp (Real.continuous_exp.continuousOn)
            (fun u hu => mem_image_of_mem _ hu)).mul Real.continuous_exp.continuousOn |>.intervalIntegrable hab.le)
        intro u hu
        have hU := firstCell_density_upper delta gamma u hd hg hu
        have hN : |gamma|*Real.exp (-u/2)/2≤firstCellNegativePart delta gamma (Real.exp u) :=
          (by unfold firstCellNegativePart; exact le_trans (by linarith) (le_max_left _ _))
        have he : Real.exp (-u/2)*Real.exp u=Real.exp (u/2) := by rw [←Real.exp_add]; congr 1; ring
        have hu0 : 0≤u := (ha.le.trans hu.1)
        have he1 : 1≤Real.exp (u/2) := Real.one_le_exp_iff.mpr (by linarith)
        have hx := mul_le_mul_of_nonneg_right hN (Real.exp_nonneg u)
        rw [show |gamma|*Real.exp (-u/2)/2*Real.exp u=|gamma|/2*Real.exp (u/2) by rw [←mul_assoc,←mul_assoc]; rw [←he]; ring] at hx
        exact (mul_le_mul_of_nonneg_left he1 (by positivity)).trans hx
  refine ⟨fun u hu => firstCell_density_upper delta gamma u hd hg hu,hm,?_⟩
  have hweight : (16/(9*gamma^2))*firstCellNegativeMass delta gamma≤firstCellNegativeSincMass delta gamma := by
    unfold firstCellNegativeMass firstCellNegativeSincMass
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hexpab (hint.1.const_mul _) hint.2
    intro x hx
    have hxpos : 0<x := (Real.exp_pos _).trans_le hx.1
    have hu : Real.log x∈Icc (firstCellLowerLog gamma) (firstCellUpperLog gamma) := by
      constructor
      · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hx.1
      · simpa only [Real.log_exp] using Real.log_le_log hxpos hx.2
    have hw := firstCell_sinc_lower gamma (Real.log x) hg hu
    rw [Real.exp_log hxpos] at hw
    exact mul_le_mul_of_nonneg_right hw (le_max_right _ _)
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : 0≤16/(9*gamma^2))
  have hcalc : (16/(9*gamma^2))*(Real.pi/6)=8*Real.pi/(27*gamma^2) := by ring
  rw [hcalc] at hmul
  exact hmul.trans hweight

end Zeta23.OPICAFollowup
