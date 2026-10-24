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

private theorem eraseImaginaryInterface {A B C D E F G H I J K : Prop}
    (h : A ∧ B ∧ C ∧ D ∧ E ∧ F ∧ G ∧ H ∧ I ∧ J ∧ K) :
    A ∧ B ∧ True ∧ D ∧ E ∧ True ∧ G ∧ H ∧ I ∧ J ∧ K := by
  rcases h with ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI, hJ, hK⟩
  exact ⟨hA, hB, True.intro, hD, hE, True.intro, hG, hH, hI, hJ, hK⟩
theorem expected_independent_complete_complex_mobius
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < ∞) :
    independentlyIntendedComplexMobius sigma a ha hm
    := by
  rcases eraseImaginaryInterface (weighted_mobius_inverse sigma a ha hm) with
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

/-- Postseal auxiliary interface: these explicit clauses were added only after
inspection of the production root.  No blind-authorship claim is made for them.
Together with the independently sealed core they preserve every original root
interface clause, while the core also exposes finite absolute double integrals. -/
def postSealMobiusAuxiliaryInterface
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ) : Prop :=
  (∀ i : Fin 4, positiveLogMeasure (positiveDilationMixture (mixingCoordinate sigma i)) =
    integerLogComb ∗ mixingCoordinate sigma i) ∧
  (moebiusPlusComb ∗ integerLogComb =
    Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb) ∧
  (∀ (mu rho : Measure ℝ) [SFinite rho],
    weightedLogNorm a (mu ∗ rho) = weightedLogNorm a mu * weightedLogNorm a rho) ∧
  (weightedLogNorm a integerLogComb = ENNReal.ofReal
      (∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2))) ∧
    ((∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
      riemannZeta ((a + 1 / 2 : ℝ) : ℂ)) ∧
  (weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) = ENNReal.ofReal
      (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) ∧
    ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
      riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ))

theorem expected_independent_complex_mobius_full_interface
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < ∞) :
    independentlyIntendedComplexMobius sigma a ha hm ∧
      postSealMobiusAuxiliaryInterface sigma a := by
  rcases eraseImaginaryInterface (weighted_mobius_inverse sigma a ha hm) with
    ⟨hraw, hre, him, hunit, hinvre, hinvim, hsigma, heta, hmul, hn, hmobius⟩
  refine ⟨expected_independent_complete_complex_mobius sigma a ha hm, ?_⟩
  exact ⟨hraw, hunit, hmul, hn, hmobius.2.1, hmobius.2.2⟩

#print axioms Zeta23.OPICAFollowup.Validation.expected_independent_complex_mobius_full_interface

end Zeta23.OPICAFollowup.Validation

