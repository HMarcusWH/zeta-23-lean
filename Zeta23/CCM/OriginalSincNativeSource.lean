import Zeta23.CCM.UniversalSincSourceFacade
import Zeta23.CCM.NativeIntegerPrimeField

/-!
# The fixed original source in the actual native arithmetic fields

The arithmetic fields below use `j = P²q` at the prescribed scale
`1/4096`. Exact source support supplies local finite histories and the
first-prime atom. The nonzero mass of `j` is a zeroth Fourier identity;
global norm, stable-forward-input and range assertions remain separate.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology BigOperators

namespace Zeta23.CCM

def nativeOriginalSource : ℝ → ℝ :=
  universalSincSecondSource UniversalSinc.fixedScale

def nativeOriginalPrimeField : ℝ → ℝ := nativePrimeField nativeOriginalSource

def nativeOriginalIntegerDrive : ℝ → ℝ := nativeIntegerDriveField nativeOriginalSource

theorem nativeOriginalSource_supported :
    NativeSourceSupported UniversalSinc.fixedScale nativeOriginalSource := by
  intro x hx
  exact universalSincSecondSource_zero_outside UniversalSinc.fixedScale_pos hx

theorem nativeOriginalSource_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) nativeOriginalSource :=
  universalSincSecondSource_contDiff UniversalSinc.fixedScale_pos

theorem nativeOriginalSource_integral :
    (∫ x : ℝ, nativeOriginalSource x) = (1 / 16 : ℝ) :=
  universalSincSecondSource_integral UniversalSinc.fixedScale_pos

theorem nativeOriginalSource_integrable : Integrable nativeOriginalSource := by
  apply nativeOriginalSource_contDiff.continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
    isCompact_Icc
  exact nativeOriginalSource_supported

theorem nativeOriginalSource_not_identically_zero : nativeOriginalSource ≠ 0 := by
  intro hzero
  have hmass := nativeOriginalSource_integral
  rw [hzero] at hmass
  norm_num at hmass

theorem nativeOriginalPrimeField_eq_history_sum {T t : ℝ} (ht : t ≤ T) :
    nativeOriginalPrimeField t =
      ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale T + 1),
        nativePrimeCoefficient n * nativeOriginalSource (t - Real.log n) :=
  nativePrimeField_eq_history_sum nativeOriginalSource_supported ht

theorem nativeOriginalIntegerDrive_eq_history_sum {T t : ℝ} (ht : t ≤ T) :
    nativeOriginalIntegerDrive t =
      ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale T + 1),
        nativeIntegerDriveCoefficient n * nativeOriginalSource (t - Real.log n) :=
  nativeIntegerDriveField_eq_history_sum nativeOriginalSource_supported ht

theorem nativeOriginalPrimeField_firstPrime_atom {t : ℝ}
    (ht : t ≤ Real.log 2 + UniversalSinc.fixedScale) :
    nativeOriginalPrimeField t =
      Real.log 2 / Real.sqrt 2 * nativeOriginalSource (t - Real.log 2) :=
  nativePrimeField_frozen_firstPrime_atom nativeOriginalSource_supported ht

theorem nativeOriginalPrimeField_continuous : Continuous nativeOriginalPrimeField :=
  nativePrimeField_continuous nativeOriginalSource_supported nativeOriginalSource_contDiff.continuous

theorem nativeOriginalIntegerDrive_continuous : Continuous nativeOriginalIntegerDrive :=
  nativeIntegerDriveField_continuous nativeOriginalSource_supported nativeOriginalSource_contDiff.continuous

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalSource_supported
#print axioms Zeta23.CCM.nativeOriginalSource_integral
#print axioms Zeta23.CCM.nativeOriginalPrimeField_firstPrime_atom
