import Zeta23.CCM.DictionaryPoleCompletion
import Zeta23.CCM.DictionarySourceTest
import Zeta23.CCM.Displacement

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped Interval

/-! # Scalar-source completion of the deterministic pole channel

The diagonal basis equality is already proved in `DictionaryPoleCompletion`.
This file evaluates the pole functional on the one-index scalar source tests and
uses the compiler-checked source divided-difference identity to close every
off-diagonal matrix entry.
-/

private theorem dictionaryPoleRHS_eq_spatial_weights
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    dictionaryPoleRHS k =
      (∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)) +
        ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ) := by
  have hA_int : Integrable (fun u : ℝ => k u * (Real.exp (-|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB_int : Integrable (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI1 : Integrable (fun u : ℝ => k u * Complex.exp (I * (I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI2 : Integrable (fun u : ℝ => k u * Complex.exp (I * (-I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  unfold dictionaryPoleRHS
  rw [← integral_add hA_int hB_int]
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, ← integral_add hI1 hI2]
  congr 1
  ext u
  rw [← mul_add, ← mul_add]
  congr 1
  have ha : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hb : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [ha, hb, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 1
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu, neg_div]
  · rw [abs_of_nonpos hu, neg_neg, add_comm, neg_div]

private theorem intervalIntegral_eq_integral_of_support_subset_Icc
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (h : Function.support f ⊆ Icc a b) :
    (∫ x in a..b, f x) = ∫ x : ℝ, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, indicator_eq_self.2 h]

private def sinExpPrimitive (a b y : ℝ) : ℝ :=
  Real.exp (b * y) *
    (b * Real.sin (a * y) - a * Real.cos (a * y)) / (a ^ 2 + b ^ 2)

private theorem hasDerivAt_sinExpPrimitive
    {a b : ℝ} (hden : a ^ 2 + b ^ 2 ≠ 0) (y : ℝ) :
    HasDerivAt (sinExpPrimitive a b)
      (Real.sin (a * y) * Real.exp (b * y)) y := by
  have ha : HasDerivAt (fun x : ℝ => a * x) a y := by
    simpa using (hasDerivAt_id y).const_mul a
  have hb : HasDerivAt (fun x : ℝ => b * x) b y := by
    simpa using (hasDerivAt_id y).const_mul b
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (a * x))
      (Real.cos (a * y) * a) y := ha.sin
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (a * x))
      (-Real.sin (a * y) * a) y := ha.cos
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (b * x))
      (Real.exp (b * y) * b) y := hb.exp
  have hinner : HasDerivAt
      (fun x : ℝ => b * Real.sin (a * x) - a * Real.cos (a * x))
      (b * (Real.cos (a * y) * a) - a * (-Real.sin (a * y) * a)) y :=
    (hsin.const_mul b).sub (hcos.const_mul a)
  have hprod := hexp.mul hinner
  have hdiv := hprod.div_const (a ^ 2 + b ^ 2)
  have hcalc :
      (Real.exp (b * y) * b *
          (b * Real.sin (a * y) - a * Real.cos (a * y)) +
        Real.exp (b * y) *
          (b * (Real.cos (a * y) * a) - a * (-Real.sin (a * y) * a))) /
          (a ^ 2 + b ^ 2) =
        Real.sin (a * y) * Real.exp (b * y) := by
    field_simp [hden]
    ring
  simpa only [sinExpPrimitive, hcalc] using hdiv

private theorem intervalIntegral_sin_mul_exp
    {a b A B : ℝ} (hden : a ^ 2 + b ^ 2 ≠ 0) :
    (∫ y in A..B, Real.sin (a * y) * Real.exp (b * y)) =
      sinExpPrimitive a b B - sinExpPrimitive a b A := by
  have hint : IntervalIntegrable
      (fun y : ℝ => Real.sin (a * y) * Real.exp (b * y)) volume A B := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := sinExpPrimitive a b)
    (f' := fun y : ℝ => Real.sin (a * y) * Real.exp (b * y))
    (fun y _ => hasDerivAt_sinExpPrimitive hden y) hint

private theorem dictionaryFrequency_mul_L_source
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryFrequency n L * L = (n : ℝ) * (2 * Real.pi) := by
  unfold dictionaryFrequency
  field_simp [hL.ne']

private theorem sin_dictionaryFrequency_L_source
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.sin (dictionaryFrequency n L * L) = 0 := by
  rw [dictionaryFrequency_mul_L_source hL n]
  simpa using Real.sin_add_int_mul_two_pi 0 n

private theorem cos_dictionaryFrequency_L_source
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Real.cos (dictionaryFrequency n L * L) = 1 := by
  rw [dictionaryFrequency_mul_L_source hL n]
  simpa using Real.cos_int_mul_two_pi n

private theorem intervalIntegral_source_sin_exp_pos_half
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.sin (dictionaryFrequency n L * y) * Real.exp (y / 2)) =
      dictionaryFrequency n L * (1 - Real.exp (L / 2)) /
        (dictionaryFrequency n L ^ 2 + 1 / 4) := by
  have hden : dictionaryFrequency n L ^ 2 + (1 / 2 : ℝ) ^ 2 ≠ 0 := by
    positivity
  have h := intervalIntegral_sin_mul_exp
    (a := dictionaryFrequency n L) (b := (1 / 2 : ℝ))
    (A := 0) (B := L) hden
  have h' :
      (∫ y in (0 : ℝ)..L,
        Real.sin (dictionaryFrequency n L * y) * Real.exp (y / 2)) =
        sinExpPrimitive (dictionaryFrequency n L) (1 / 2) L -
          sinExpPrimitive (dictionaryFrequency n L) (1 / 2) 0 := by
    convert h using 1 <;> ring
  rw [h']
  unfold sinExpPrimitive
  rw [sin_dictionaryFrequency_L_source hL n,
    cos_dictionaryFrequency_L_source hL n]
  norm_num
  ring

private theorem intervalIntegral_source_sin_exp_neg_half
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (∫ y in (0 : ℝ)..L,
      Real.sin (dictionaryFrequency n L * y) * Real.exp (-y / 2)) =
      dictionaryFrequency n L * (1 - Real.exp (-L / 2)) /
        (dictionaryFrequency n L ^ 2 + 1 / 4) := by
  have hden : dictionaryFrequency n L ^ 2 + (-1 / 2 : ℝ) ^ 2 ≠ 0 := by
    positivity
  have h := intervalIntegral_sin_mul_exp
    (a := dictionaryFrequency n L) (b := (-1 / 2 : ℝ))
    (A := 0) (B := L) hden
  have h' :
      (∫ y in (0 : ℝ)..L,
        Real.sin (dictionaryFrequency n L * y) * Real.exp (-y / 2)) =
        sinExpPrimitive (dictionaryFrequency n L) (-1 / 2) L -
          sinExpPrimitive (dictionaryFrequency n L) (-1 / 2) 0 := by
    convert h using 1 <;> ring
  rw [h']
  unfold sinExpPrimitive
  rw [sin_dictionaryFrequency_L_source hL n,
    cos_dictionaryFrequency_L_source hL n]
  norm_num
  ring

private theorem two_sub_exp_half_sub_exp_neg_half (L : ℝ) :
    2 - Real.exp (L / 2) - Real.exp (-L / 2) =
      -4 * Real.sinh (L / 4) ^ 2 := by
  have hcosh :
      Real.exp (L / 2) + Real.exp (-L / 2) = 2 * Real.cosh (L / 2) := by
    change Real.exp (L / 2) + Real.exp (-L / 2) =
      2 * ((Real.exp (L / 2) + Real.exp (-(L / 2))) / 2)
    rw [show -(L / 2) = -L / 2 by ring]
    ring
  have h1 := Real.cosh_two_mul (L / 4)
  have h2 := Real.cosh_sq_sub_sinh_sq (L / 4)
  rw [show 2 * (L / 4) = L / 2 by ring] at h1
  nlinarith

private theorem sourcePole_real_algebra
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    -(1 / Real.pi) *
        (dictionaryFrequency n L *
          (2 - Real.exp (L / 2) - Real.exp (-L / 2)) /
          (dictionaryFrequency n L ^ 2 + 1 / 4)) =
      poleSeq n L := by
  rw [two_sub_exp_half_sub_exp_neg_half]
  have hd : 0 < L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
    positivity
  unfold dictionaryFrequency poleSeq
  dsimp
  field_simp [hL.ne', Real.pi_ne_zero, ne_of_gt hd]
  ring

/-- The scalar source test evaluates to the pole displacement potential exactly. -/
theorem dictionaryPoleRHS_sourceTest
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryPoleRHS (dictionarySourceTest n L) = ((poleSeq n L : ℝ) : ℂ) := by
  let G : ℝ → ℂ := fun y =>
    dictionarySourceTest n L y *
      ((Real.exp (-|y| / 2) : ℂ) + (Real.exp (|y| / 2) : ℂ))
  have hk := continuous_dictionarySourceTest n L
  have hkc := dictionarySourceTest_hasCompactSupport hL n
  rw [dictionaryPoleRHS_eq_spatial_weights hk hkc]
  have hA : Integrable
      (fun y : ℝ => dictionarySourceTest n L y * (Real.exp (-|y| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB : Integrable
      (fun y : ℝ => dictionarySourceTest n L y * (Real.exp (|y| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  rw [← integral_add hA hB]
  simp_rw [← mul_add]
  change (∫ y : ℝ, G y) = _
  have hGsupp : Function.support G ⊆ Icc (-L) L := by
    intro y hy
    apply dictionarySourceTest_support_subset hL n
    intro hzero
    apply hy
    simp [G, hzero]
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc (by linarith : -L ≤ L) hGsupp]
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hGcont.intervalIntegrable (-L) 0) (hGcont.intervalIntegrable 0 L)
  rw [← hsplit]
  have hGneg : ∀ y : ℝ, G (-y) = G y := by
    intro y
    simp [G, dictionarySourceTest_neg]
  have hleft : (∫ y in -L..(0 : ℝ), G y) = ∫ y in (0 : ℝ)..L, G y := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) G
    have h2 : (∫ y in (0 : ℝ)..L, G (-y)) = ∫ y in (0 : ℝ)..L, G y := by
      apply intervalIntegral.integral_congr
      intro y _
      exact hGneg y
    rw [← h2, h1]
    norm_num
  rw [hleft]
  let X : ℝ :=
    dictionaryFrequency n L *
      (2 - Real.exp (L / 2) - Real.exp (-L / 2)) /
      (dictionaryFrequency n L ^ 2 + 1 / 4)
  have hpos :
      (∫ y in (0 : ℝ)..L, G y) = (((-1 / (2 * Real.pi)) * X : ℝ) : ℂ) := by
    have hfun : ∀ y ∈ Set.uIcc (0 : ℝ) L,
        G y =
          (((-1 / (2 * Real.pi)) *
            (Real.sin (dictionaryFrequency n L * y) *
              (Real.exp (-y / 2) + Real.exp (y / 2))) : ℝ) : ℂ) := by
      intro y hy
      rw [Set.uIcc_of_le hL.le] at hy
      have hy0 : 0 ≤ y := hy.1
      have hyL : y ≤ L := hy.2
      have habs : |y| ≤ L := by simpa [abs_of_nonneg hy0] using hyL
      change dictionarySourceTest n L y *
          ((Real.exp (-|y| / 2) : ℂ) + (Real.exp (|y| / 2) : ℂ)) = _
      rw [dictionarySourceTest_eq_sine_of_abs_le hL habs n]
      simp [abs_of_nonneg hy0, dictionaryFrequency]
      push_cast
      ring
    rw [intervalIntegral.integral_congr hfun]
    rw [intervalIntegral.integral_ofReal]
    apply Complex.ofReal_injective
    have hsinNeg : IntervalIntegrable
        (fun y : ℝ => Real.sin (dictionaryFrequency n L * y) * Real.exp (-y / 2))
        volume 0 L := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hsinPos : IntervalIntegrable
        (fun y : ℝ => Real.sin (dictionaryFrequency n L * y) * Real.exp (y / 2))
        volume 0 L := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hsinNeg hsinPos]
    rw [intervalIntegral_source_sin_exp_neg_half hL n,
      intervalIntegral_source_sin_exp_pos_half hL n]
    dsimp [X]
    ring
  rw [hpos]
  rw [← Complex.ofReal_add]
  apply Complex.ofReal_injective
  calc
    (-1 / (2 * Real.pi)) * X + (-1 / (2 * Real.pi)) * X =
        -(1 / Real.pi) * X := by ring
    _ = poleSeq n L := by
      dsimp [X]
      exact sourcePole_real_algebra hL n

/-- Off the diagonal, the literature pole channel satisfies exactly the same
one-index displacement law as the fork-owned finite pole component. -/
theorem dictionaryPoleRHS_basis_of_ne
    {L : ℝ} (hL : 0 < L) {n m : ℤ} (hnm : n ≠ m) :
    dictionaryPoleRHS (dictionaryBasisTest n m L) =
      ((poleComponent n m L : ℝ) : ℂ) := by
  have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hnmC : (((n - m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hnmZ
  have hfun :
      (fun y : ℝ => (((n - m : ℤ) : ℂ)) * dictionaryBasisTest n m L y) =
        fun y => dictionarySourceTest n L y - dictionarySourceTest m L y := by
    funext y
    exact dictionaryBasisTest_displacement_eq_sourceTest_sub hL hnm y
  have hkN := continuous_dictionarySourceTest n L
  have hkM := continuous_dictionarySourceTest m L
  have hkcN := dictionarySourceTest_hasCompactSupport hL n
  have hkcM := dictionarySourceTest_hasCompactSupport hL m
  have hlin_smul :
      dictionaryPoleRHS
          (fun y : ℝ => (((n - m : ℤ) : ℂ)) * dictionaryBasisTest n m L y) =
        (((n - m : ℤ) : ℂ)) * dictionaryPoleRHS (dictionaryBasisTest n m L) := by
    unfold dictionaryPoleRHS
    simp_rw [Zeta23.paperFT_def]
    have hp : (fun u : ℝ => (((n - m : ℤ) : ℂ)) * dictionaryBasisTest n m L u *
        Complex.exp (I * (I / 2) * u)) =
        fun u => (((n - m : ℤ) : ℂ)) *
          (dictionaryBasisTest n m L u * Complex.exp (I * (I / 2) * u)) := by
      funext u
      ring
    have hm : (fun u : ℝ => (((n - m : ℤ) : ℂ)) * dictionaryBasisTest n m L u *
        Complex.exp (I * (-I / 2) * u)) =
        fun u => (((n - m : ℤ) : ℂ)) *
          (dictionaryBasisTest n m L u * Complex.exp (I * (-I / 2) * u)) := by
      funext u
      ring
    rw [hp, hm, Zeta23.integral_const_mul_C, Zeta23.integral_const_mul_C]
    ring
  have hlin_sub :
      dictionaryPoleRHS
          (fun y : ℝ => dictionarySourceTest n L y - dictionarySourceTest m L y) =
        dictionaryPoleRHS (dictionarySourceTest n L) -
          dictionaryPoleRHS (dictionarySourceTest m L) := by
    unfold dictionaryPoleRHS
    simp_rw [Zeta23.paperFT_def]
    have hpN : Integrable
        (fun y : ℝ => dictionarySourceTest n L y * Complex.exp (I * (I / 2) * y)) :=
      (hkN.mul (by fun_prop)).integrable_of_hasCompactSupport hkcN.mul_right
    have hpM : Integrable
        (fun y : ℝ => dictionarySourceTest m L y * Complex.exp (I * (I / 2) * y)) :=
      (hkM.mul (by fun_prop)).integrable_of_hasCompactSupport hkcM.mul_right
    have hmN : Integrable
        (fun y : ℝ => dictionarySourceTest n L y * Complex.exp (I * (-I / 2) * y)) :=
      (hkN.mul (by fun_prop)).integrable_of_hasCompactSupport hkcN.mul_right
    have hmM : Integrable
        (fun y : ℝ => dictionarySourceTest m L y * Complex.exp (I * (-I / 2) * y)) :=
      (hkM.mul (by fun_prop)).integrable_of_hasCompactSupport hkcM.mul_right
    have hp : (fun u : ℝ =>
        (dictionarySourceTest n L u - dictionarySourceTest m L u) *
          Complex.exp (I * (I / 2) * u)) =
        fun u => dictionarySourceTest n L u * Complex.exp (I * (I / 2) * u) -
          dictionarySourceTest m L u * Complex.exp (I * (I / 2) * u) := by
      funext u
      ring
    have hm : (fun u : ℝ =>
        (dictionarySourceTest n L u - dictionarySourceTest m L u) *
          Complex.exp (I * (-I / 2) * u)) =
        fun u => dictionarySourceTest n L u * Complex.exp (I * (-I / 2) * u) -
          dictionarySourceTest m L u * Complex.exp (I * (-I / 2) * u) := by
      funext u
      ring
    rw [hp, hm, integral_sub hpN hpM, integral_sub hmN hmM]
    ring
  have hdisp :
      (((n - m : ℤ) : ℂ)) * dictionaryPoleRHS (dictionaryBasisTest n m L) =
        ((poleSeq n L - poleSeq m L : ℝ) : ℂ) := by
    rw [← hlin_smul, hfun, hlin_sub,
      dictionaryPoleRHS_sourceTest hL n, dictionaryPoleRHS_sourceTest hL m]
    push_cast
    ring
  have hcompReal := poleComponent_displacement (n := n) (m := m) hL
  have hcomp :
      (((n - m : ℤ) : ℂ)) * ((poleComponent n m L : ℝ) : ℂ) =
        ((poleSeq n L - poleSeq m L : ℝ) : ℂ) := by
    exact_mod_cast hcompReal
  apply (mul_left_cancel₀ hnmC)
  rw [hdisp, hcomp]

/-- Complete production pole-channel normalization for every basis entry. -/
theorem dictionaryPoleRHS_basis
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    dictionaryPoleRHS (dictionaryBasisTest n m L) =
      ((poleComponent n m L : ℝ) : ℂ) := by
  by_cases hnm : n = m
  · subst m
    exact dictionaryPoleRHS_basis_diag hL n
  · exact dictionaryPoleRHS_basis_of_ne hL hnm

end Zeta23.CCM
