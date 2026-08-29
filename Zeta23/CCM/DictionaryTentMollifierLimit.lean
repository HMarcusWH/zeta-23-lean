import Zeta23.CCM.DictionaryTentMollifierTransform

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution Topology

/-!
# Fixed-frequency convergence of the canonical tent mollifier

Route M M0--M3 proves exact factorization

```text
paperFT (dictionaryTentMollified L n) z
  = dictionaryTentMollifierTransform n z * paperFT (dictionaryTent L) z.
```

The missing fixed-frequency input for M4, M6 and M7 is that the normalized
shrinking mollifier transform tends to one at every fixed complex frequency.
This is another direct use of Mathlib's normalized-bump approximate identity;
no explicit-formula theorem is used here.
-/

/-- Continuous phase whose value at `-x` is the exponential appearing in the
project's positive-sign `paperFT` convention. -/
private def dictionaryTentMollifierPhase (z : ℂ) : ℝ → ℂ :=
  fun x => Complex.exp (-Complex.I * z * x)

private theorem continuous_dictionaryTentMollifierPhase (z : ℂ) :
    Continuous (dictionaryTentMollifierPhase z) := by
  unfold dictionaryTentMollifierPhase
  fun_prop

/-- At the origin, convolution of the normalized real mollifier with the
opposite-sign exponential phase is exactly the native mollifier transform. -/
private theorem dictionaryTentMollifierTransform_eq_convolution_zero
    (n : ℕ) (z : ℂ) :
    dictionaryTentMollifierTransform n z =
      (dictionaryTentMollifier n ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
        dictionaryTentMollifierPhase z) 0 := by
  unfold dictionaryTentMollifierTransform Zeta23.paperFT
  rw [convolution_lsmul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [dictionaryTentMollifierComplex, dictionaryTentMollifierPhase,
    Complex.real_smul]
  congr 1
  push_cast
  ring

/-- M3.5: the transform of the normalized shrinking mollifier tends to one at
every fixed complex frequency. -/
theorem dictionaryTentMollifierTransform_tendsto_one
    (z : ℂ) :
    Tendsto
      (fun n : ℕ => dictionaryTentMollifierTransform n z)
      atTop
      (𝓝 1) := by
  have happrox :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume)
      (φ := dictionaryTentMollifierBump)
      (g := dictionaryTentMollifierPhase z)
      dictionaryTentMollifierBump_rOut_tendsto_zero
      (continuous_dictionaryTentMollifierPhase z)
      0
  have hseq :
      (fun n : ℕ => dictionaryTentMollifierTransform n z) =
        fun n =>
          (dictionaryTentMollifier n ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume]
            dictionaryTentMollifierPhase z) 0 := by
    funext n
    exact dictionaryTentMollifierTransform_eq_convolution_zero n z
  rw [hseq]
  simpa [dictionaryTentMollifier, dictionaryTentMollifierPhase] using happrox

/-- Fixed-frequency transform convergence transfers immediately to the
mollified tents through the exact M2 factorization. -/
theorem paperFT_dictionaryTentMollified_tendsto
    {L : ℝ} (hL : 0 < L) (z : ℂ) :
    Tendsto
      (fun n : ℕ =>
        Zeta23.paperFT (dictionaryTentMollified L n) z)
      atTop
      (𝓝 (Zeta23.paperFT (dictionaryTent L) z)) := by
  have hmul :=
    (dictionaryTentMollifierTransform_tendsto_one z).mul_const
      (Zeta23.paperFT (dictionaryTent L) z)
  have hseq :
      (fun n : ℕ =>
        Zeta23.paperFT (dictionaryTentMollified L n) z) =
      fun n =>
        dictionaryTentMollifierTransform n z *
          Zeta23.paperFT (dictionaryTent L) z := by
    funext n
    exact paperFT_dictionaryTentMollified_factor hL n z
  rw [hseq]
  simpa using hmul

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTentMollifierTransform_tendsto_one
#print axioms Zeta23.CCM.paperFT_dictionaryTentMollified_tendsto
