import Zeta23.OPICAFollowup.WeightedMixing

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
open Zeta23.OPICA

namespace Zeta23.OPICAFollowup.Validation

/-- Independently packaged full complex weighted inverse contract.  The four
coordinates belong to the actual physical mixture, rather than caller-supplied
eta data.  Both complex coordinate equations and the absolute convolution
integrals are retained. -/
def independentlyIntendedComplexMobius
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < ∞) : Prop :=
  let physical := weightedDilationMixture sigma a ha.le hm
  let etaReP := positiveLogMeasure physical.rePart.positive
  let etaReN := positiveLogMeasure physical.rePart.negative
  let etaImP := positiveLogMeasure physical.imPart.positive
  let etaImN := positiveLogMeasure physical.imPart.negative
  let absoluteMobius := moebiusPlusComb + moebiusMinusComb
  -- eta = N * sigma, with BOTH real and imaginary coordinates.
  (etaReP + integerLogComb ∗ sigma.rePart.negative =
    etaReN + integerLogComb ∗ sigma.rePart.positive) ∧
  (etaImP + integerLogComb ∗ sigma.imPart.negative =
    etaImN + integerLogComb ∗ sigma.imPart.positive) ∧
  -- sigma = M_mu * eta, with BOTH real and imaginary coordinates.
  (sigma.rePart.positive +
      (moebiusPlusComb ∗ etaReN + moebiusMinusComb ∗ etaReP) =
    sigma.rePart.negative +
      (moebiusPlusComb ∗ etaReP + moebiusMinusComb ∗ etaReN)) ∧
  (sigma.imPart.positive +
      (moebiusPlusComb ∗ etaImN + moebiusMinusComb ∗ etaImP) =
    sigma.imPart.negative +
      (moebiusPlusComb ∗ etaImP + moebiusMinusComb ∗ etaImN)) ∧
  -- All physical input/output coordinates lie in the weighted algebra.
  (∀ i : Fin 4, weightedLogNorm a (mixingCoordinate sigma i) < ∞) ∧
  (∀ i : Fin 4, weightedLogNorm a
    (positiveLogMeasure (mixingCoordinate physical i)) < ∞) ∧
  -- Absolute weighted Fubini for every coordinate, including imaginary ones.
  (∀ i : Fin 4, weightedLogNorm a
    (absoluteMobius ∗ positiveLogMeasure (mixingCoordinate physical i)) < ∞) ∧
  (∀ i : Fin 4,
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-a * (x + y)))
      ∂(positiveLogMeasure (mixingCoordinate physical i)) ∂absoluteMobius) < ∞) ∧
  -- The positive/negative physical Mobius combs form its Jordan pair.
  (moebiusPlusComb ⟂ₘ moebiusMinusComb) ∧
  -- Exact weighted variation norm, not merely an upper bound.
  weightedLogNorm a absoluteMobius = ENNReal.ofReal
    ((riemannZeta ((a + 1 / 2 : ℝ) : ℂ) /
      riemannZeta ((2 * a + 1 : ℝ) : ℂ)).re)

theorem expected_independent_complete_complex_mobius
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < ∞) :
    independentlyIntendedComplexMobius sigma a ha hm
    := by
  rcases weighted_mobius_inverse sigma a ha hm with
    ⟨hraw, hre, him, hunit, hinvre, hinvim, hsigma, heta, hmul, hn, hmobius⟩
  let physical := weightedDilationMixture sigma a ha.le hm
  have hetaAll (i : Fin 4) : weightedLogNorm a
      (positiveLogMeasure (mixingCoordinate physical i)) < ∞ := by
    fin_cases i
    · exact heta.1
    · exact heta.2.1
    · exact heta.2.2.1
    · exact heta.2.2.2
  have habsolute : weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) < ∞ := by
    rw [weightedLogNorm_add]
    exact ENNReal.add_lt_top.mpr (weightedLogNorm_moebiusComb_lt_top ha)
  have hconv (i : Fin 4) : weightedLogNorm a
      ((moebiusPlusComb + moebiusMinusComb) ∗
        positiveLogMeasure (mixingCoordinate physical i)) < ∞ := by
    rw [hmul]
    exact ENNReal.mul_lt_top habsolute (hetaAll i)
  have hfubini (i : Fin 4) :
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-a * (x + y)))
        ∂(positiveLogMeasure (mixingCoordinate physical i))
        ∂(moebiusPlusComb + moebiusMinusComb)) < ∞ := by
    rw [← Measure.lintegral_conv (by fun_prop :
      Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-a * z))))]
    exact hconv i
  have hexact : weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
      ENNReal.ofReal ((riemannZeta ((a + 1 / 2 : ℝ) : ℂ) /
        riemannZeta ((2 * a + 1 : ℝ) : ℂ)).re) := by
    rw [hmobius.2.1]
    exact congrArg ENNReal.ofReal (by simpa using congrArg Complex.re hmobius.2.2)
  exact ⟨hre, him, hinvre, hinvim, hsigma, hetaAll, hconv, hfubini, hmobius.1, hexact⟩

#print axioms Zeta23.OPICAFollowup.Validation.expected_independent_complete_complex_mobius

end Zeta23.OPICAFollowup.Validation

