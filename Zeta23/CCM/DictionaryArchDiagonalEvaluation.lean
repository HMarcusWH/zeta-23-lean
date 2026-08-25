import Zeta23.CCM.DictionaryArchDiagonalPhysical

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped FourierTransform Interval

/-! # Diagonal physical archimedean evaluation

This module is the Phase-G2 continuation of the compiler-green literature-to-
physical bridge.  It evaluates the diagonal finite-aperture functional in the
existing `gammaL` / `betaL` normalization and then composes that evaluation with
G1.  No new special-function or improper-integral argument is introduced here.
-/

/-- The physical diagonal entry is exactly the diagonal `archComponent` with
its full scalar identity correction. -/
theorem dictionaryArchPhysicalRHS_basis_diag
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryArchPhysicalRHS (dictionaryBasisTest n n L) L =
      -((archComponent n n L : ℝ) : ℂ) +
        ((2 * cCorrection L : ℝ) : ℂ) := by
  let k : ℝ → ℂ := dictionaryBasisTest n n L
  let p : ℝ → ℂ := fun x =>
    (k x - (Real.exp (-x / 2) : ℂ)) * (archDensity x : ℂ)
  let g : ℝ → ℂ := fun x =>
    (((Real.cos (2 * Real.pi * (n : ℝ) * x / L) -
        Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)
  let b : ℝ → ℂ := fun x =>
    ((x * Real.cos (2 * Real.pi * (n : ℝ) * x / L) *
      archDensity x : ℝ) : ℂ)
  have hk0 : k 0 = 1 := by
    simp [k, dictionaryBasisTest, kernel_zero hL.le]
  have hpOn : IntegrableOn p (Ioi 0) := by
    simpa [p, k] using
      integrableOn_dictionaryBasisTest_diag_sub_exp_mul_archDensity_Ioi hL n
  have hpInt : IntervalIntegrable p volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    exact hpOn.mono_set fun x hx => hx.1
  have href : IntegrableOn (fun x : ℝ =>
      (((1 - Real.exp (-x / 2)) * archDensity x : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi.ofReal
  have hcos : IntegrableOn (fun x : ℝ =>
      ((archDensity x *
        (1 - Real.cos (dictionaryFrequency n L * x)) : ℝ) : ℂ))
      (Ioi 0) :=
    (integrableOn_archDensity_mul_one_sub_cos_Ioi
      (dictionaryFrequency n L)).ofReal
  have hgOn : IntegrableOn g (Ioi 0) := by
    have hdifference := href.sub hcos
    refine hdifference.congr ?_
    filter_upwards with x
    have hfreq : dictionaryFrequency n L * x =
        2 * Real.pi * (n : ℝ) * x / L := by
      unfold dictionaryFrequency
      ring
    simp only [Pi.sub_apply]
    rw [hfreq]
    dsimp [g]
    push_cast
    ring
  have hgInt : IntervalIntegrable g volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    exact hgOn.mono_set fun x hx => hx.1
  have hbInt : IntervalIntegrable b volume 0 L := by
    have hcomb := (hgInt.sub hpInt).const_mul (L : ℂ)
    refine hcomb.congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le hL.le] at hx
    have hxIcc : x ∈ Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
    have hfreq : dictionaryFrequency n L * x =
        2 * Real.pi * (n : ℝ) * x / L := by
      unfold dictionaryFrequency
      ring
    dsimp [p, g, b, k]
    rw [dictionaryBasisTest_diag_eq_tent_cos hL n x,
      dictionaryTent_eq_one_sub_div_of_mem_Icc hL hxIcc, hfreq]
    push_cast
    field_simp [hL.ne']
    ring
  have hpPoint : EqOn p
      (fun x : ℝ => g x - (1 / L : ℂ) * b x) (uIoo 0 L) := by
    intro x hx
    rw [uIoo_of_le hL.le] at hx
    have hxIcc : x ∈ Icc (0 : ℝ) L := ⟨hx.1.le, hx.2.le⟩
    have hfreq : dictionaryFrequency n L * x =
        2 * Real.pi * (n : ℝ) * x / L := by
      unfold dictionaryFrequency
      ring
    dsimp [p, g, b, k]
    rw [dictionaryBasisTest_diag_eq_tent_cos hL n x,
      dictionaryTent_eq_one_sub_div_of_mem_Icc hL hxIcc, hfreq]
    push_cast
    field_simp [hL.ne']
    ring
  have hpIntegral :
      (∫ x : ℝ in (0 : ℝ)..L, p x) =
        (∫ x : ℝ in (0 : ℝ)..L, g x) -
          (1 / L : ℂ) * ∫ x : ℝ in (0 : ℝ)..L, b x := by
    calc
      (∫ x : ℝ in (0 : ℝ)..L, p x) =
          ∫ x : ℝ in (0 : ℝ)..L,
            (g x - (1 / L : ℂ) * b x) := by
        exact intervalIntegral.integral_congr_uIoo hpPoint
      _ = (∫ x : ℝ in (0 : ℝ)..L, g x) -
          ∫ x : ℝ in (0 : ℝ)..L, (1 / L : ℂ) * b x := by
        rw [intervalIntegral.integral_sub hgInt
          (hbInt.const_mul (1 / L : ℂ))]
      _ = (∫ x : ℝ in (0 : ℝ)..L, g x) -
          (1 / L : ℂ) * ∫ x : ℝ in (0 : ℝ)..L, b x := by
        rw [intervalIntegral.integral_const_mul]
  have hgammaPatch :
      (((∫ x : ℝ in (0 : ℝ)..L,
          (if x = 0 then 1 / 4
          else (Real.cos (2 * Real.pi * (n : ℝ) * x / L) -
            Real.exp (-x / 2)) * archDensity x)) : ℝ) : ℂ) =
        ∫ x : ℝ in (0 : ℝ)..L, g x := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    have hxne : x ≠ 0 := by
      rw [uIoo_of_le hL.le] at hx
      exact ne_of_gt hx.1
    simp [g, hxne]
  have hbetaPatch :
      (((∫ x : ℝ in (0 : ℝ)..L,
          (if x = 0 then 1 / 2
          else x * Real.cos (2 * Real.pi * (n : ℝ) * x / L) *
            archDensity x)) : ℝ) : ℂ) =
        ∫ x : ℝ in (0 : ℝ)..L, b x := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    have hxne : x ≠ 0 := by
      rw [uIoo_of_le hL.le] at hx
      exact ne_of_gt hx.1
    simp [b, hxne]
  have hk0basis : dictionaryBasisTest n n L 0 = 1 := by
    simpa [k] using hk0
  rw [dictionaryArchPhysicalRHS, hk0basis]
  change (-2 : ℂ) * (∫ x : ℝ in (0 : ℝ)..L, p x) -
      ((2 * wCorrection L : ℝ) : ℂ) =
    -((archComponent n n L : ℝ) : ℂ) +
      ((2 * cCorrection L : ℝ) : ℂ)
  rw [hpIntegral]
  unfold archComponent
  simp only [if_pos]
  unfold gammaL betaL
  push_cast
  rw [hgammaPatch, hbetaPatch]
  ring

/-- Phase-G3 wrapper: the exact diagonal literature-channel entry, including
`2*cCorrection(L)` in the identity channel. -/
theorem dictionaryArchRHS_basis_diag
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    dictionaryArchRHS (dictionaryBasisTest n n L) =
      -((archComponent n n L : ℝ) : ℂ) +
        ((2 * cCorrection L : ℝ) : ℂ) := by
  rw [dictionaryArchRHS_basis_diag_eq_physical hL n]
  exact dictionaryArchPhysicalRHS_basis_diag hL n

end Zeta23.CCM
