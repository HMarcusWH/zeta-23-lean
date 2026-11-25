import Zeta23.OPICATerminal.Energy
import Zeta23.OPICATerminal.Analytic.LandauTheorems.poleData
import Zeta23.OPICATerminal.Analytic.LandauTheorems.landauWindow
import Zeta23.OPICATerminal.Analytic.LandauTheorems.WindowHypUOfWindowHyp
import Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor

/-! Literal prime source and positive-energy localization.
The imported conditional analytic window lemma and its pole data are adapted
from Alpöge's original Lean sources (see pinned source manifests).
No upstream arithmetic supply or terminal zero-exclusion theorem is used.
-/
noncomputable section
open Set MeasureTheory Filter
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.ExceptionalZero
namespace Zeta23.OPICATerminal

def principalFamily : Deduction.CharFamily where
  ι := Unit
  N := fun _ => 1
  nz := fun _ => inferInstance
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

theorem principalG_eq_literal (x : ℝ) :
    Deduction.Gm principalFamily x = literalG x := by
  have hχ : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) n = 1 := by
    intro n
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  rw [OPICAExtractionR1.native_literalG_eq_rampG]
  simp [Deduction.Gm, principalFamily, Deduction.Gchi, Deduction.ramp,
    OPICAExtractionR1.rampG, hχ, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]

theorem nativeZero_mem_principal (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ρ ∈ Deduction.zeroSet principalFamily := by
  have hz : IsNontrivialZero ρ := by simpa using hρ
  refine ⟨(zetaZeroConfig.strip ρ hρ).1, (), Or.inl ?_⟩
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ρ = 0
  rw [DirichletCharacter.LFunction_modOne_eq]
  exact hz.1

theorem literalG_continuousOn {u v : ℝ} (hu : 0 < u) :
    ContinuousOn literalG (Icc u v) := by
  have heq : literalG = OPICAExtractionR1.rampG :=
    funext OPICAExtractionR1.native_literalG_eq_rampG
  rw [heq]
  exact OPICAExtractionR1.rampG_continuousOn_pos hu

def density (x : ℝ) : ℝ := (max (literalG x) 0)^2 / x^2

theorem density_nonneg (x : ℝ) : 0 ≤ density x := by
  unfold density
  positivity

theorem density_continuousOn {u v : ℝ} (hu : 0 < u) :
    ContinuousOn density (Icc u v) := by
  exact (((literalG_continuousOn hu).sup continuousOn_const).pow 2).div
    (continuous_id.pow 2).continuousOn
    (fun x hx => pow_ne_zero _ (hu.trans_le hx.1).ne')

theorem literalGEnergy_nonneg {Y : ℝ} (hY : 2 ≤ Y) :
    0 ≤ literalGEnergy Y := by
  have hle : Y ≤ Y^(3/2:ℝ) := by
    calc
      Y = Y^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  exact intervalIntegral.integral_nonneg hle (fun x _ => density_nonneg x)

theorem weighted_positive_continuousOn {u v : ℝ} (hu : 0 < u) (θ : ℝ) :
    ContinuousOn (fun x => max (literalG x) 0 * x^(-θ-1:ℝ)) (Icc u v) :=
  ((literalG_continuousOn hu).sup continuousOn_const).mul
    (fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (hu.trans_le hx.1).ne')).continuousWithinAt)

theorem weighted_positive_young {x t θ : ℝ} (hx : 0 < x) (ht : 0 < t) :
    2 * (max (literalG x) 0 * x^(-θ-1:ℝ)) ≤
      t⁻¹ * density x + t * x^(-2*θ:ℝ) := by
  let A := max (literalG x) 0 / x
  let B := x^(-θ:ℝ)
  have h : 2*A*B ≤ (A^2 + (t*B)^2)/t :=
    (le_div_iff₀ ht).2 (by nlinarith [sq_nonneg (A-t*B)])
  have hw : x^(-θ-1:ℝ) = x^(-θ:ℝ)/x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  have hB : B^2 = x^(-2*θ:ℝ) := by
    dsimp [B]
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le, show (-θ)*2 = -2*θ by ring]
  have hA : A^2 = density x := by simp [A, density, div_pow]
  calc
    _ = 2*A*B := by rw [hw]; dsimp [A, B]; ring
    _ ≤ (A^2+(t*B)^2)/t := h
    _ = t⁻¹*density x+t*x^(-2*θ:ℝ) := by
      rw [mul_pow, hA, hB]
      field_simp [ht.ne']
      <;> ring

theorem tail_integral_bound {u v θ : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hθ : 1/2 < θ) :
    (∫ x in u..v, x^(-2*θ:ℝ)) ≤ u^(1-2*θ:ℝ)/(2*θ-1) := by
  have h0 : (0:ℝ) ∉ [[u,v]] := by
    rw [uIcc_of_le huv]
    intro h
    exact (not_le_of_gt hu) h.1
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have he : -2*θ+1 = 1-2*θ := by ring
  rw [he]
  have hp : 0 < 2*θ-1 := by linarith
  have hpow : 0 ≤ v^(1-2*θ:ℝ) := Real.rpow_nonneg (hu.le.trans huv) _
  have he' : 1-2*θ = -(2*θ-1) := by ring
  calc
    _ = (u^(1-2*θ:ℝ)-v^(1-2*θ:ℝ))/(2*θ-1) := by
      rw [show (1-2*θ:ℝ) = -(2*θ-1) by ring] at *
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ hpow) hp.le

/-- If a full window has small positive energy, the later subwindow has
    a one-sided weighted integral at most one. No pointwise upper bound is assumed. -/
theorem later_window_weighted_le_one {Y c θ h : ℝ} (hY : 2 ≤ Y)
    (hc : 1 ≤ c) (hc' : c ≤ 3/2) (hθ : 1/2 < θ)
    (hE : literalGEnergy Y ≤ Y^h)
    (hmargin : (2*θ-1)⁻¹ ≤ Y^(c*(2*θ-1)-h)) :
    (∫ x in Icc (Y^c) (Y^(3/2:ℝ)), max (literalG x) 0*x^(-θ-1:ℝ)) ≤ 1 := by
  let u := Y^c
  let v := Y^(3/2:ℝ)
  let t := Y^h
  have hYpos : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have ht : 0 < t := Real.rpow_pos_of_pos hYpos _
  have hYu : Y ≤ u := by
    calc
      Y = Y^(1:ℝ) := (Real.rpow_one Y).symm
      _ ≤ u := Real.rpow_le_rpow_of_exponent_le hY1 hc
  have huv : u ≤ v := Real.rpow_le_rpow_of_exponent_le hY1 hc'
  have hu : 0 < u := hYpos.trans_le hYu
  have hp : 0 < 2*θ-1 := by linarith
  have hfull := (density_continuousOn (v := v) hYpos).intervalIntegrable_of_Icc (hYu.trans huv)
  have hi := (density_continuousOn (v := v) hu).intervalIntegrable_of_Icc huv
  have hw := (weighted_positive_continuousOn (v := v) hu θ).intervalIntegrable_of_Icc huv
  have hj : IntervalIntegrable (fun x : ℝ => x^(-2*θ:ℝ)) volume u v :=
    (show ContinuousOn (fun x : ℝ => x^(-2*θ:ℝ)) (Icc u v) from
      fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (hu.trans_le hx.1).ne')).continuousWithinAt).intervalIntegrable_of_Icc huv
  have hsub : (∫ x in u..v, density x) ≤ t := by
    calc
      _ ≤ ∫ x in Y..v, density x :=
        intervalIntegral.integral_mono_interval hYu huv le_rfl
          (Filter.Eventually.of_forall density_nonneg) hfull
      _ ≤ t := hE
  have htail : t * (∫ x in u..v, x^(-2*θ:ℝ)) ≤ 1 := by
    have he : u^(1-2*θ:ℝ) = Y^(c*(1-2*θ):ℝ) := (Real.rpow_mul hYpos.le _ _).symm
    have hm : (2*θ-1)⁻¹ ≤ Y^(-(h+c*(1-2*θ)):ℝ) := by
      convert hmargin using 1 <;> ring
    have hprod : Y^(h+c*(1-2*θ):ℝ) * (2*θ-1)⁻¹ ≤ 1 := by
      calc
        _ ≤ Y^(h+c*(1-2*θ):ℝ) * Y^(-(h+c*(1-2*θ)):ℝ) :=
          mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hYpos.le _)
        _ = 1 := by rw [← Real.rpow_add hYpos, add_neg_cancel, Real.rpow_zero]
    calc
      _ ≤ t*(u^(1-2*θ:ℝ)/(2*θ-1)) :=
        mul_le_mul_of_nonneg_left (tail_integral_bound hu huv hθ) ht.le
      _ = Y^(h+c*(1-2*θ):ℝ)*(2*θ-1)⁻¹ := by
        rw [he, Real.rpow_add hYpos]; dsimp [t]; ring
      _ ≤ 1 := hprod
  have hm := intervalIntegral.integral_mono_on (μ := volume) huv
    (hw.const_mul 2) ((hi.const_mul t⁻¹).add (hj.const_mul t))
    (fun x hx => weighted_positive_young (hu.trans_le hx.1) ht (θ := θ))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi.const_mul t⁻¹) (hj.const_mul t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have hsmall : t⁻¹*(∫ x in u..v, density x) ≤ 1 := by
    calc
      _ ≤ t⁻¹*t := mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr ht.le)
      _ = 1 := inv_mul_cancel₀ ht.ne'
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
  linarith

/-- Arbitrarily late small-energy windows would imply the conditional
    analytic window hypothesis at a narrower, later subwindow. -/
theorem windowHyp_of_cofinal_small_energy {h θ c : ℝ}
    (hc : 1 < c) (hc' : c < 3/2) (hθ : 1/2 < θ)
    (hm : h < c*(2*θ-1))
    (hbad : ∀ R : ℝ, ∃ Y : ℝ, R ≤ Y ∧ literalGEnergy Y ≤ Y^h) :
    Deduction.WindowHyp principalFamily θ ((3/2)/c-1) := by
  intro η hη Y₀
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (show 0 < c by linarith)).eventually_ge_atTop Y₀)
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (sub_pos.mpr hm)).eventually_ge_atTop (2*θ-1)⁻¹)
  obtain ⟨Y,hY,hE⟩ := hbad (max 2 (max B₁ B₂))
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hYpos : 0 < Y := by linarith
  have hcpos : 0 < c := by linarith
  have hYB : max B₁ B₂ ≤ Y := (le_max_right _ _).trans hY
  have hbase : 1 ≤ Y^c := Real.one_le_rpow (by linarith) hcpos.le
  have hu : 0 < Y^c := Real.rpow_pos_of_pos hYpos _
  have he : (Y^c)^((1+((3/2)/c-1)):ℝ) = Y^(3/2:ℝ) := by
    rw [← Real.rpow_mul hYpos.le]
    congr 1
    field_simp [hcpos.ne']
    <;> ring
  refine ⟨Y^c,hB₁ Y ((le_max_left _ _).trans hYB),fun x => max (literalG x) 0,?_⟩
  rw [he]
  refine ⟨?_,?_,?_⟩
  · exact (weighted_positive_continuousOn hu θ).integrableOn_Icc
  · intro x _
    exact ⟨le_max_right _ _, (principalG_eq_literal x).trans_le (le_max_left _ _)⟩
  · exact (later_window_weighted_le_one hY2 hc.le hc'.le hθ hE
        (hB₂ Y ((le_max_right _ _).trans hYB))).trans
      (Real.one_le_rpow hbase hη.le)

/-- The positive energy detects every sufficiently late window, not just
    a subsequence. The proof uses a pole-data contradiction at theta. -/
theorem eventual_energy_growth_of_right_zero {h θ c : ℝ}
    (hc : 1 < c) (hc' : c < 3/2) (hθ : 1/2 < θ) (hθ' : θ < 1)
    (hm : h < c*(2*θ-1))
    (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) (hr : θ < ρ.re) :
    ∀ᶠ Y in atTop, Y^h ≤ literalGEnergy Y := by
  by_contra hn
  rw [eventually_atTop] at hn
  push_neg at hn
  have hbad : ∀ R : ℝ, ∃ Y : ℝ, R ≤ Y ∧ literalGEnergy Y ≤ Y^h := by
    intro R
    obtain ⟨Y,hY,hlt⟩ := hn R
    exact ⟨Y,hY,hlt.le⟩
  have hδ : 0 < (3/2)/c-1 := by
    apply sub_pos.mpr
    exact (lt_div_iff₀ (by linarith : 0 < c)).2 (by linarith)
  obtain ⟨Φ,hP⟩ := Deduction.poleData principalFamily
  have hW := Deduction.windowHypU_of_windowHyp principalFamily hδ
    (windowHyp_of_cofinal_small_energy hc hc' hθ hm hbad)
  exact (not_le_of_gt hr)
    (Deduction.landau_window hP (by linarith) hθ' hδ hW ρ (nativeZero_mem_principal ρ hρ))

end Zeta23.OPICATerminal
