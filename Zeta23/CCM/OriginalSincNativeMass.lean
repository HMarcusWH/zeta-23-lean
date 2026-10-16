import Zeta23.CCM.OriginalSincNativeSource

/-!
# A mass anchor for the fixed original first-prime field

The exact first-prime window contains the complete translated source and
no later integer atom. Its integral is obtained from `∫j = 1/16`, rather
than from a sampled value such as `j(0)`. This is a local nonzero anchor;
it makes no assertion about global field norms or a stable forward input.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def nativeOriginalFirstPrimeWindow : Set ℝ :=
  Icc (Real.log 2 - UniversalSinc.fixedScale) (Real.log 2 + UniversalSinc.fixedScale)

private theorem firstPrime_source_integral :
    (∫ t : ℝ in nativeOriginalFirstPrimeWindow,
      nativeOriginalSource (t - Real.log 2)) = (1 / 16 : ℝ) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_sub_right_eq_self, nativeOriginalSource_integral]
  · intro t ht
    apply nativeOriginalSource_supported
    intro hmem
    apply ht
    change t ∈ Icc (Real.log 2 - UniversalSinc.fixedScale)
      (Real.log 2 + UniversalSinc.fixedScale)
    constructor <;> linarith [hmem.1, hmem.2]

/-- Exact first-prime mass with the unchanged von Mangoldt/square-root
coefficient and the actual fixed twice pole-killed source. -/
theorem nativeOriginalPrimeField_firstPrimeWindow_integral :
    (∫ t : ℝ in nativeOriginalFirstPrimeWindow, nativeOriginalPrimeField t) =
      (Real.log 2 / Real.sqrt 2) / 16 := by
  calc
    _ = ∫ t : ℝ in nativeOriginalFirstPrimeWindow,
        (Real.log 2 / Real.sqrt 2) * nativeOriginalSource (t - Real.log 2) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact nativeOriginalPrimeField_firstPrime_atom ht.2
    _ = (Real.log 2 / Real.sqrt 2) *
        ∫ t : ℝ in nativeOriginalFirstPrimeWindow, nativeOriginalSource (t - Real.log 2) :=
      integral_const_mul _ _
    _ = (Real.log 2 / Real.sqrt 2) * (1 / 16) := by rw [firstPrime_source_integral]
    _ = _ := by ring

theorem nativeOriginalPrimeField_firstPrimeWindow_integral_pos :
    0 < ∫ t : ℝ in nativeOriginalFirstPrimeWindow, nativeOriginalPrimeField t := by
  rw [nativeOriginalPrimeField_firstPrimeWindow_integral]
  exact div_pos (div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num)))
    (by norm_num)

theorem nativeOriginalPrimeField_not_identically_zero : nativeOriginalPrimeField ≠ 0 := by
  intro hzero
  have hpos := nativeOriginalPrimeField_firstPrimeWindow_integral_pos
  rw [hzero] at hpos
  simpa using hpos

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalPrimeField_firstPrimeWindow_integral
#print axioms Zeta23.CCM.nativeOriginalPrimeField_not_identically_zero
