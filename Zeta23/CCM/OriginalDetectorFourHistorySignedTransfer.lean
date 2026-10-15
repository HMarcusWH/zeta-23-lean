import Zeta23.CCM.OriginalDetectorFourHistoryTransfer
import Zeta23.CCM.NativeOriginalExteriorHistory

/-!
# Signed complete original four-prime history under compact inverse

This establishes the LOCAL source-specific signed transfer for the
genuine original smooth detector with BOTH reflection terms. It is
not the source-specific subexponential Step 4 law, and it does not
replace the full physical Weil response with a prime-only expression.

It does not assume X globally square integrable. It derives the
four pairings independently, and only then composes with the actual
phase sign and fixed original physical normalization.
-/

noncomputable section
open MeasureTheory Set
namespace Zeta23.CCM

def originalSmoothFourPrimeXHistories (σ a x : ℝ) : ℂ :=
  (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
    (((nativeOriginalPrimeField
       (x - Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter) : ℝ) +
      (nativeOriginalPrimeField
       (Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter - x) : ℝ) : ℂ) +
     (σ : ℂ) *
       (((nativeOriginalPrimeField
         (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a - x -
           Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter) : ℝ) +
        (nativeOriginalPrimeField
         (x + Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter -
           Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) : ℝ) : ℂ))

private theorem intervalIntegral_four_signed_pairings
    {s : ℝ} {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : ℝ → ℂ}
    (hA₁ : IntervalIntegrable A₁ volume (-s) s)
    (hA₂ : IntervalIntegrable A₂ volume (-s) s)
    (hA₃ : IntervalIntegrable A₃ volume (-s) s)
    (hA₄ : IntervalIntegrable A₄ volume (-s) s)
    (hB₁ : IntervalIntegrable B₁ volume (-s) s)
    (hB₂ : IntervalIntegrable B₂ volume (-s) s)
    (hB₃ : IntervalIntegrable B₃ volume (-s) s)
    (hB₄ : IntervalIntegrable B₄ volume (-s) s)
    (h₁ : (∫ x in (-s)..s, A₁ x) = ∫ x in (-s)..s, B₁ x)
    (h₂ : (∫ x in (-s)..s, A₂ x) = ∫ x in (-s)..s, B₂ x)
    (h₃ : (∫ x in (-s)..s, A₃ x) = ∫ x in (-s)..s, B₃ x)
    (h₄ : (∫ x in (-s)..s, A₄ x) = ∫ x in (-s)..s, B₄ x)
    (κ σ : ℂ) :
    (∫ x in (-s)..s, κ * ((A₁ x + A₂ x) + σ * (A₃ x + A₄ x))) =
      ∫ x in (-s)..s, κ * ((B₁ x + B₂ x) + σ * (B₃ x + B₄ x)) := by
  have hA :
      (∫ x in (-s)..s, κ * ((A₁ x + A₂ x) + σ * (A₃ x + A₄ x))) =
      κ * (((∫ x in (-s)..s, A₁ x) + (∫ x in (-s)..s, A₂ x)) +
         σ * ((∫ x in (-s)..s, A₃ x) + (∫ x in (-s)..s, A₄ x))) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (hA₁.add hA₂)
      ((hA₃.add hA₄).const_mul σ)]
    rw [intervalIntegral.integral_add hA₁ hA₂,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hA₃ hA₄]
  have hB :
      (∫ x in (-s)..s, κ * ((B₁ x + B₂ x) + σ * (B₃ x + B₄ x))) =
      κ * (((∫ x in (-s)..s, B₁ x) + (∫ x in (-s)..s, B₂ x)) +
         σ * ((∫ x in (-s)..s, B₃ x) + (∫ x in (-s)..s, B₄ x))) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (hB₁.add hB₂)
      ((hB₃.add hB₄).const_mul σ)]
    rw [intervalIntegral.integral_add hB₁ hB₂,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hB₃ hB₄]
  rw [hA, hB, h₁, h₂, h₃, h₄]

/-- Full SAME-SOURCE prime response: original σ and original κ are
retained, including BOTH reflected histories and finite interior.
No sign of this complex-valued expression is presumed. -/
theorem NativeCompactPoleH2.originalSmoothFourPrimeHistories_to_actualX
    {s : ℝ} {f : ℝ → ℂ} (u : NativeCompactPoleH2 s f)
    (hf : Continuous f) (σ a : ℝ) :
    (∫ x in (-s)..s, f x * originalSmoothFourPrimeHistories σ a x) =
      ∫ x in (-s)..s, u.value x * originalSmoothFourPrimeXHistories σ a x := by
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let c := Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
  let F := nativeOriginalKernelPrimeField
  let X : ℝ → ℂ := fun x => (nativeOriginalPrimeField x : ℂ)
  let κ : ℂ := Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization
  have hF : Continuous F := nativeOriginalKernelPrimeField_contDiff.continuous
  have hX : Continuous X :=
    Complex.continuous_ofReal.comp nativeOriginalPrimeField_continuous
  have hF₁ : IntervalIntegrable (fun x : ℝ => f x * F (x - c)) volume (-s) s :=
    (hf.mul (hF.comp (by fun_prop))).intervalIntegrable _ _
  have hF₂ : IntervalIntegrable (fun x : ℝ => f x * F (c - x)) volume (-s) s :=
    (hf.mul (hF.comp (by fun_prop))).intervalIntegrable _ _
  have hF₃ : IntervalIntegrable (fun x : ℝ => f x * F (L - x - c)) volume (-s) s :=
    (hf.mul (hF.comp (by fun_prop))).intervalIntegrable _ _
  have hF₄ : IntervalIntegrable (fun x : ℝ => f x * F (x + c - L)) volume (-s) s :=
    (hf.mul (hF.comp (by fun_prop))).intervalIntegrable _ _
  have hX₁ : IntervalIntegrable (fun x : ℝ => u.value x * X (x - c)) volume (-s) s :=
    (u.value_continuous.mul (hX.comp (by fun_prop))).intervalIntegrable _ _
  have hX₂ : IntervalIntegrable (fun x : ℝ => u.value x * X (c - x)) volume (-s) s :=
    (u.value_continuous.mul (hX.comp (by fun_prop))).intervalIntegrable _ _
  have hX₃ : IntervalIntegrable (fun x : ℝ => u.value x * X (L - x - c)) volume (-s) s :=
    (u.value_continuous.mul (hX.comp (by fun_prop))).intervalIntegrable _ _
  have hX₄ : IntervalIntegrable (fun x : ℝ => u.value x * X (x + c - L)) volume (-s) s :=
    (u.value_continuous.mul (hX.comp (by fun_prop))).intervalIntegrable _ _
  obtain ⟨h₁, h₂, h₃, h₄⟩ := u.originalFourHistories_to_actualX hf a
  have hCombined :=
    intervalIntegral_four_signed_pairings hF₁ hF₂ hF₃ hF₄
      hX₁ hX₂ hX₃ hX₄ h₁ h₂ h₃ h₄ κ (σ : ℂ)
  have hsource (x : ℝ) :
      f x * originalSmoothFourPrimeHistories σ a x =
        κ * (((f x * F (x - c) + f x * F (c - x)) +
          (σ : ℂ) * (f x * F (L - x - c) + f x * F (x + c - L)))) := by
    dsimp [originalSmoothFourPrimeHistories, F, κ, L, c]
    ring
  have htarget (x : ℝ) :
      u.value x * originalSmoothFourPrimeXHistories σ a x =
        κ * (((u.value x * X (x - c) + u.value x * X (c - x)) +
          (σ : ℂ) * (u.value x * X (L - x - c) +
            u.value x * X (x + c - L)))) := by
    dsimp [originalSmoothFourPrimeXHistories, X, κ, L, c]
    push_cast
    ring
  calc
    (∫ x in (-s)..s, f x * originalSmoothFourPrimeHistories σ a x) =
      ∫ x in (-s)..s, κ * (((f x * F (x - c) + f x * F (c - x)) +
        (σ : ℂ) * (f x * F (L - x - c) + f x * F (x + c - L)))) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hsource x
    _ = ∫ x in (-s)..s, κ * (((u.value x * X (x - c) + u.value x * X (c - x)) +
        (σ : ℂ) * (u.value x * X (L - x - c) + u.value x * X (x + c - L)))) :=
      hCombined
    _ = ∫ x in (-s)..s, u.value x * originalSmoothFourPrimeXHistories σ a x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (htarget x).symm

end Zeta23.CCM

#print axioms Zeta23.CCM.NativeCompactPoleH2.originalSmoothFourPrimeHistories_to_actualX
