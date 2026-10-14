import Zeta23.CCM.PoleNeutralCompactH2

/-! # Uniqueness of the actual compact H2 inverse from clamped a.e. equations -/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

private theorem expAC (r a b : ℝ) :
    AbsolutelyContinuousOnInterval (nativePoleExponential r) a b := by
  have h : ContDiff ℝ 1 (nativePoleExponential r) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact h.contDiffOn.absolutelyContinuousOnInterval

private theorem exp_ne_zero (r x : ℝ) : nativePoleExponential r x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

private theorem homogeneous_clamped_pair_zero {s : ℝ} {u d : ℝ → ℂ}
    (hu : AbsolutelyContinuousOnInterval u (-s) s)
    (hd : AbsolutelyContinuousOnInterval d (-s) s)
    (huD : ∀ᵐ x : ℝ, HasDerivAt u (d x) x)
    (hdD : ∀ᵐ x : ℝ, HasDerivAt d ((1 / 4 : ℂ) * u x) x)
    (hu0 : u (-s) = 0) (hd0 : d (-s) = 0) :
    ∀ x ∈ uIcc (-s) s, u x = 0 ∧ d x = 0 := by
  let w := fun x : ℝ => d x - (1 / 2 : ℂ) * u x
  have hwAC : AbsolutelyContinuousOnInterval w (-s) s := by
    simpa only [Pi.sub_apply, smul_eq_mul] using! hd.sub (hu.const_smul (1 / 2 : ℂ))
  have hwD : ∀ᵐ x : ℝ, HasDerivAt w (-(1 / 2 : ℂ) * w x) x := by
    filter_upwards [huD, hdD] with x hx hdx
    convert! hdx.sub (hx.const_mul (1 / 2 : ℂ)) using 1 <;> first
      | rfl
      | (dsimp [w]; ring)
  let z := fun x : ℝ => nativePoleExponential (1 / 2) x * w x
  have hzAC : AbsolutelyContinuousOnInterval z (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! (expAC (1 / 2) (-s) s).smul hwAC
  have hzD : ∀ᵐ x : ℝ, x ∈ uIcc (-s) s → HasDerivAt z 0 x := by
    filter_upwards [hwD] with x hx _
    convert! (hasDerivAt_nativePoleExponential (1 / 2) x).mul hx using 1 <;> first
      | rfl
      | (push_cast; ring)
  obtain ⟨C, hC⟩ := hzAC.const_of_ae_hasDerivAt_zero hzD
  have hC0 : C = 0 := by
    simpa only [z, w, hu0, hd0, mul_zero, sub_zero] using (hC (-s) (by simp)).symm
  have hwzero (x : ℝ) (hx : x ∈ uIcc (-s) s) : w x = 0 := by
    have hz := hC x hx
    rw [hC0] at hz
    exact (mul_eq_zero.mp hz).resolve_left (exp_ne_zero (1 / 2) x)
  let y := fun x : ℝ => nativePoleExponential (-1 / 2) x * u x
  have hyAC : AbsolutelyContinuousOnInterval y (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! (expAC (-1 / 2) (-s) s).smul hu
  have hyD : ∀ᵐ x : ℝ, x ∈ uIcc (-s) s → HasDerivAt y 0 x := by
    filter_upwards [huD] with x hx hmem
    have hdx : d x = (1 / 2 : ℂ) * u x := sub_eq_zero.mp (hwzero x hmem)
    convert! (hasDerivAt_nativePoleExponential (-1 / 2) x).mul hx using 1 <;> first
      | rfl
      | (rw [hdx]; push_cast; ring)
  obtain ⟨B, hB⟩ := hyAC.const_of_ae_hasDerivAt_zero hyD
  have hB0 : B = 0 := by
    simpa only [y, hu0, mul_zero] using (hB (-s) (by simp)).symm
  intro x hx
  have hy := hB x hx
  rw [hB0] at hy
  have hux : u x = 0 := (mul_eq_zero.mp hy).resolve_left (exp_ne_zero (-1 / 2) x)
  refine ⟨hux, ?_⟩
  have hwx := hwzero x hx
  simpa only [w, hux, mul_zero, sub_zero] using hwx

/-- The actual a.e. differential equations and clamped jets determine the
continuous compact representatives uniquely; no source smoothness is used. -/
theorem NativeCompactPoleH2.unique {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (a b : NativeCompactPoleH2 s f) : a = b := by
  let u := fun x : ℝ => a.value x - b.value x
  let d := fun x : ℝ => a.first x - b.first x
  have huAC : AbsolutelyContinuousOnInterval u (-s) s := a.value_ac.sub b.value_ac
  have hdAC : AbsolutelyContinuousOnInterval d (-s) s := a.first_ac.sub b.first_ac
  have huD : ∀ᵐ x : ℝ, HasDerivAt u (d x) x := by
    filter_upwards [a.value_derivative, b.value_derivative] with x hx hy
    exact hx.sub hy
  have hdD : ∀ᵐ x : ℝ, HasDerivAt d ((1 / 4 : ℂ) * u x) x := by
    filter_upwards [a.first_derivative, b.first_derivative] with x hx hy
    convert! hx.sub hy using 1 <;> first
      | rfl
      | (dsimp [u]; ring)
  have hu0 : u (-s) = 0 := by simp only [u, a.value_clamped.1, b.value_clamped.1, sub_self]
  have hd0 : d (-s) = 0 := by simp only [d, a.first_clamped.1, b.first_clamped.1, sub_self]
  have hzero := homogeneous_clamped_pair_zero huAC hdAC huD hdD hu0 hd0
  have hav : a.value = b.value := by
    funext x
    by_cases hx : x ∈ Icc (-s) s
    · exact sub_eq_zero.mp (hzero x (by simpa only [uIcc_of_le (show -s ≤ s by linarith)] using hx)).1
    · rw [a.value_support x hx, b.value_support x hx]
  have had : a.first = b.first := by
    funext x
    by_cases hx : x ∈ Icc (-s) s
    · exact sub_eq_zero.mp (hzero x (by simpa only [uIcc_of_le (show -s ≤ s by linarith)] using hx)).2
    · rw [a.first_support x hx, b.first_support x hx]
  cases a
  cases b
  cases hav
  cases had
  rfl

theorem nativePoleCompactH2_exists_unique {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hsupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    ∃! u : NativeCompactPoleH2 s f, True := by
  refine ⟨nativePoleCompactH2 hs hf hsupport hplus hminus, trivial, ?_⟩
  intro u _
  exact u.unique hs _

end Zeta23.CCM

#print axioms Zeta23.CCM.NativeCompactPoleH2.unique
#print axioms Zeta23.CCM.nativePoleCompactH2_exists_unique
