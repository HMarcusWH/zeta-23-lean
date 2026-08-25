import Zeta23.CCM.DictionaryArchSourceIntegrability
import Zeta23.CCM.DictionaryArchBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped FourierTransform

/-! # Even exponential weights for the literature arch bridge

Each positive-abscissa digamma summand is represented by the Fourier transform
of an even exponential weight.  This lets the actual literature gamma integral
reuse `Zeta23.EF.integral_k_mul_weight` one summand at a time.
-/

/-- Even exponential weight with positive decay parameter. -/
def archExpWeight (a : ℝ) (u : ℝ) : ℂ :=
  (Real.exp (-a * |u|) : ℂ)

private theorem archExp_pos_sub_I_ne_zero
    {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    (a : ℂ) - I * τ ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

private theorem archExp_neg_sub_I_ne_zero
    {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    (-(a : ℂ)) - I * τ ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

/-- The even exponential weight is integrable for positive decay. -/
theorem integrable_archExpWeight
    {a : ℝ} (ha : 0 < a) :
    Integrable (archExpWeight a) := by
  have hIic : IntegrableOn (fun u : ℝ => cexp (((a : ℂ)) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simpa using ha) 0
  have hIoi : IntegrableOn (fun u : ℝ => cexp ((-(a : ℂ)) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr ha) 0
  have eIic : EqOn (archExpWeight a)
      (fun u : ℝ => cexp ((a : ℂ) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    change ((Real.exp (-a * |u|) : ℝ) : ℂ) = cexp ((a : ℂ) * (u : ℂ))
    rw [abs_of_nonpos hu, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have eIoi : EqOn (archExpWeight a)
      (fun u : ℝ => cexp (-(a : ℂ) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    change ((Real.exp (-a * |u|) : ℝ) : ℂ) = cexp (-(a : ℂ) * (u : ℂ))
    rw [abs_of_pos hu, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have h := (hIic.congr_fun eIic.symm measurableSet_Iic).union
    (hIoi.congr_fun eIoi.symm measurableSet_Ioi)
  rwa [Iic_union_Ioi, integrableOn_univ] at h

/-- Exact paper-sign Fourier transform of the even exponential weight. -/
theorem integral_archExpWeight_mul
    {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    ∫ u : ℝ, archExpWeight a u * cexp (-I * τ * u) =
      (((2 * a) / (a ^ 2 + τ ^ 2) : ℝ) : ℂ) := by
  have h1 := archExp_pos_sub_I_ne_zero ha τ
  have hIic : IntegrableOn
      (fun u : ℝ => cexp (((a : ℂ) - I * τ) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simpa using ha) 0
  have hIoi : IntegrableOn
      (fun u : ℝ => cexp ((-(a : ℂ) - I * τ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr ha) 0
  have eIic : EqOn
      (fun u : ℝ => archExpWeight a u * cexp (-I * τ * u))
      (fun u : ℝ => cexp (((a : ℂ) - I * τ) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    change ((Real.exp (-a * |u|) : ℝ) : ℂ) * cexp (-I * (τ : ℂ) * (u : ℂ)) =
      cexp (((a : ℂ) - I * (τ : ℂ)) * (u : ℂ))
    rw [abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have eIoi : EqOn
      (fun u : ℝ => archExpWeight a u * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((-(a : ℂ) - I * τ) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    change ((Real.exp (-a * |u|) : ℝ) : ℂ) * cexp (-I * (τ : ℂ) * (u : ℂ)) =
      cexp ((-(a : ℂ) - I * (τ : ℂ)) * (u : ℂ))
    rw [abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0)
      (hIic.congr_fun eIic.symm measurableSet_Iic)
      (hIoi.congr_fun eIoi.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Iic eIic,
    setIntegral_congr_fun measurableSet_Ioi eIoi,
    integral_exp_mul_complex_Iic (by simpa using ha) 0,
    integral_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr ha) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hp : (a : ℂ) + I * (τ : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hneg :
      (-(a : ℂ) - I * (τ : ℂ)) = -((a : ℂ) + I * (τ : ℂ)) := by
    ring
  have hprod :
      ((a : ℂ) - I * (τ : ℂ)) * ((a : ℂ) + I * (τ : ℂ)) =
        (((a ^ 2 + τ ^ 2 : ℝ)) : ℂ) := by
    calc
      ((a : ℂ) - I * (τ : ℂ)) * ((a : ℂ) + I * (τ : ℂ)) =
          (a : ℂ) ^ 2 - (I * (τ : ℂ)) ^ 2 := by ring
      _ = ((a : ℂ) ^ 2 + (τ : ℂ) ^ 2) := by
        rw [mul_pow, Complex.I_sq]
        ring
      _ = (((a ^ 2 + τ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hneg]
  simp only [div_neg, neg_div, neg_neg]
  calc
    (1 : ℂ) / ((a : ℂ) - I * (τ : ℂ)) +
        1 / ((a : ℂ) + I * (τ : ℂ)) =
      ((a : ℂ) + I * (τ : ℂ) + ((a : ℂ) - I * (τ : ℂ))) /
        (((a : ℂ) - I * (τ : ℂ)) * ((a : ℂ) + I * (τ : ℂ))) := by
          field_simp [h1, hp]
    _ = (((2 * a) / (a ^ 2 + τ ^ 2) : ℝ) : ℂ) := by
      rw [hprod]
      push_cast
      ring

/-- Positive abscissa attached to the `m`-th digamma summand. -/
def archSeriesAbscissa (m : ℕ) : ℝ :=
  (m : ℝ) + 1 / 4

/-- The physical even weight for one digamma summand. -/
def archSeriesWeight (m : ℕ) : ℝ → ℂ :=
  archExpWeight (2 * archSeriesAbscissa m)

/-- Every positive abscissa is strictly positive. -/
theorem archSeriesAbscissa_pos (m : ℕ) :
    0 < archSeriesAbscissa m := by
  unfold archSeriesAbscissa
  positivity

/-- Exact transform of one digamma summand weight in the repository convention. -/
theorem integral_archSeriesWeight_mul (m : ℕ) (τ : ℝ) :
    ∫ u : ℝ, archSeriesWeight m u * cexp (-I * τ * u) =
      (((archSeriesAbscissa m) /
        ((archSeriesAbscissa m) ^ 2 + (τ / 2) ^ 2) : ℝ) : ℂ) := by
  have hb := archSeriesAbscissa_pos m
  rw [show archSeriesWeight m = archExpWeight (2 * archSeriesAbscissa m) by rfl,
    integral_archExpWeight_mul (by positivity : 0 < 2 * archSeriesAbscissa m) τ]
  push_cast
  have hden1 : (2 * archSeriesAbscissa m) ^ 2 + τ ^ 2 ≠ 0 := by positivity
  have hden2 : (archSeriesAbscissa m) ^ 2 + (τ / 2) ^ 2 ≠ 0 := by positivity
  field_simp [hden1, hden2]

/-- The constant part of a digamma summand is the zero-frequency transform of
its even exponential weight. -/
theorem integral_archSeriesWeight_mul_zero (m : ℕ) :
    ∫ u : ℝ, archSeriesWeight m u =
      (((1 / archSeriesAbscissa m : ℝ)) : ℂ) := by
  have ha := archSeriesAbscissa_pos m
  have h := integral_archSeriesWeight_mul m 0
  calc
    (∫ u : ℝ, archSeriesWeight m u) =
        (((archSeriesAbscissa m / archSeriesAbscissa m ^ 2 : ℝ)) : ℂ) := by
      simpa using h
    _ = (((1 / archSeriesAbscissa m : ℝ)) : ℂ) := by
      congr 1
      field_simp [ha.ne']

/-- One all-term digamma difference is zero-frequency weight transform minus
its transform at `τ`. -/
theorem archDigammaAllTerm_eq_weightTransformDifference
    (m : ℕ) (τ : ℝ) :
    ((archDigammaAllTerm (τ / 2) m : ℝ) : ℂ) =
      ((1 / archSeriesAbscissa m : ℝ) : ℂ) -
        ∫ u : ℝ, archSeriesWeight m u * cexp (-I * τ * u) := by
  rw [integral_archSeriesWeight_mul]
  unfold archDigammaAllTerm archSeriesAbscissa
  push_cast
  ring

end Zeta23.CCM
