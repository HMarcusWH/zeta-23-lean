import Zeta23.CCM.SourceContraction
import Zeta23.CCM.LocalizedFiniteSpace

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators Convolution ComplexConjugate Interval

/-!
# Closure campaign A1: source contraction through the localized autocorrelation

This module pushes the remaining source-contraction analysis onto the actual
zero-extended finite Fourier function already constructed in the repository.
The remaining open inequality is now a standard L2 autocorrelation bound rather
than a matrix-entry estimate.
-/

/-- The elementary source contraction is exactly the unit-aperture localized
finite autocorrelation at complementary shift. -/
theorem sourceContract_eq_localizedWeilCorrelation_unit
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    sourceContract K u ω =
      localizedWeilCorrelation
        (localizedFiniteVector 1 K u)
        (localizedFiniteVector 1 K u) (1 - ω) := by
  have hy0 : 0 ≤ 1 - ω := sub_nonneg.mpr hω1
  have hy1 : 1 - ω ≤ (1 : ℝ) := by linarith
  have hcorr :=
    localizedWeilCorrelation_finiteVector_eq_two_mul_dictionaryTest_of_nonneg
      K u (L := (1 : ℝ)) (y := 1 - ω) (by norm_num) hy0 hy1
  have habs : |1 - ω| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hy0]
    exact hy1
  have hdict :
      dictionaryTest K u 1 (1 - ω) =
        (1 / 2 : ℂ) * sourceContract K u ω := by
    unfold dictionaryTest dictionaryKernel
    rw [if_pos habs, abs_of_nonneg hy0]
    congr 2
    ring
  rw [hdict] at hcorr
  have htwo : (2 : ℂ) * ((1 / 2 : ℂ) * sourceContract K u ω) =
      sourceContract K u ω := by ring
  rw [htwo] at hcorr
  exact hcorr.symm

/-- Exact matrix-energy form of the same bridge. -/
theorem matrixRealEnergy_sourceMatrix_eq_localizedWeilCorrelation_re
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    matrixRealEnergy (sourceMatrix ω K) x =
      Complex.re
        (localizedWeilCorrelation
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (1 - ω)) := by
  change
    Complex.re
      (sourceContract K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ω) =
      Complex.re
        (localizedWeilCorrelation
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (1 - ω))
  rw [sourceContract_eq_localizedWeilCorrelation_unit
    K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ω hω0 hω1]

/-- The coefficient mass is exactly the Euclidean norm-square after taking
real parts.  This fixes the normalization used by the L2 reduction. -/
theorem coefficientMass_re_eq_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Complex.re
        (coefficientMass K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) =
      ‖x‖ ^ 2 := by
  have h := matrixRealEnergy_sourceMatrix_one K x
  change
    Complex.re
        (sourceContract K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) 1) =
      2 * ‖x‖ ^ 2 at h
  rw [sourceContract_one] at h
  norm_num [Complex.mul_re] at h ⊢
  nlinarith

/-- Unit-aperture Parseval normalization for the actual finite Fourier
function, derived from the already-proved zero-shift correlation identity. -/
theorem localizedFiniteFunction_unit_energy_eq_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (∫ t in (0 : ℝ)..1,
        ‖localizedFiniteFunction 1 K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t‖ ^ 2) =
      ‖x‖ ^ 2 := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  let f := localizedFiniteVector 1 K u
  have hzero :=
    localizedWeilCorrelation_finiteVector_zero K u
      (L := (1 : ℝ)) (by norm_num)
  have hzero' :
      Zeta23.EF.weilTest f f 0 + Zeta23.EF.weilTest f f 0 =
        2 * coefficientMass K u := by
    simpa [f, localizedWeilCorrelation] using hzero
  have hweil :
      Zeta23.EF.weilTest f f 0 = coefficientMass K u := by
    linear_combination (1 / 2 : ℂ) * hzero'
  have hpos :=
    weilTest_localizedFiniteVector_pos K u
      (L := (1 : ℝ)) (y := (0 : ℝ)) (by norm_num) (by norm_num)
  have hcomplex :
      (∫ t in (0 : ℝ)..1,
          localizedFiniteFunction 1 K u t *
            conj (localizedFiniteFunction 1 K u t)) =
        coefficientMass K u := by
    calc
      (∫ t in (0 : ℝ)..1,
          localizedFiniteFunction 1 K u t *
            conj (localizedFiniteFunction 1 K u t)) =
          Zeta23.EF.weilTest f f 0 := by
            simpa [f] using hpos.symm
      _ = coefficientMass K u := hweil
  have hcont : Continuous (fun t : ℝ =>
      localizedFiniteFunction 1 K u t *
        conj (localizedFiniteFunction 1 K u t)) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ =>
        localizedFiniteFunction 1 K u t *
          conj (localizedFiniteFunction 1 K u t))
      volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable (0 : ℝ) 1
  have hre := congrArg Complex.re hcomplex
  have hre' :
      (∫ t in (0 : ℝ)..1,
          RCLike.re
            (localizedFiniteFunction 1 K u t *
              conj (localizedFiniteFunction 1 K u t))) =
        RCLike.re (coefficientMass K u) :=
    (intervalIntegral.intervalIntegral_re hint).trans hre
  simp only [Complex.mul_conj', RCLike.ofReal_re] at hre'
  have hmass :
      RCLike.re (coefficientMass K u) = ‖x‖ ^ 2 := by
    simpa [u] using coefficientMass_re_eq_norm_sq K x
  rw [hmass] at hre'
  simpa [u] using hre'

/-- Every nonnegative subinterval of the unit source interval carries at
most the full finite-Fourier energy. -/
theorem localizedFiniteFunction_unit_subinterval_energy_le_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in a..b,
        ‖localizedFiniteFunction 1 K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t‖ ^ 2) ≤
      ‖x‖ ^ 2 := by
  rw [← localizedFiniteFunction_unit_energy_eq_norm_sq K x]
  let F : ℝ → ℂ := fun t =>
    localizedFiniteFunction 1 K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t
  have hcont : Continuous (fun t : ℝ => ‖F t‖ ^ 2) := by
    dsimp [F]
    fun_prop
  exact intervalIntegral.integral_mono_interval
    (f := fun t : ℝ => ‖F t‖ ^ 2)
    (μ := volume) (a := a) (b := b) (c := 0) (d := 1)
    ha hab hb
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (hcont.intervalIntegrable 0 1)

/-- Translation of a unit-source subinterval preserves its available L2
budget. -/
theorem localizedFiniteFunction_unit_shifted_energy_le_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∫ t in (0 : ℝ)..(1 - y),
        ‖localizedFiniteFunction 1 K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) (t + y)‖ ^ 2) ≤
      ‖x‖ ^ 2 := by
  let F : ℝ → ℂ := fun t =>
    localizedFiniteFunction 1 K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t
  have hshift :=
    intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ => ‖F t‖ ^ 2)
      (a := (0 : ℝ)) (b := 1 - y) y
  calc
    (∫ t in (0 : ℝ)..(1 - y), ‖F (t + y)‖ ^ 2) =
        ∫ t in y..1, ‖F t‖ ^ 2 := by
          simpa using hshift
    _ ≤ ‖x‖ ^ 2 := by
      simpa [F] using
        localizedFiniteFunction_unit_subinterval_energy_le_norm_sq
          K x hy0 hy1 le_rfl

/-- The unshifted part of the same overlap interval is also controlled by the
full unit-source energy. -/
theorem localizedFiniteFunction_unit_initial_energy_le_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∫ t in (0 : ℝ)..(1 - y),
        ‖localizedFiniteFunction 1 K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t‖ ^ 2) ≤
      ‖x‖ ^ 2 := by
  exact localizedFiniteFunction_unit_subinterval_energy_le_norm_sq
    K x le_rfl (sub_nonneg.mpr hy1) (by linarith)

/-- One oriented overlap is bounded by the coefficient norm-square.  This is
the Cauchy--Schwarz/AM-GM step behind the source contraction bound. -/
theorem localizedFiniteFunction_positiveOverlap_norm_le_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖∫ t in (0 : ℝ)..(1 - y),
        localizedFiniteFunction 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) (t + y) *
          conj (localizedFiniteFunction 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t)‖ ≤
      ‖x‖ ^ 2 := by
  let F : ℝ → ℂ := fun t =>
    localizedFiniteFunction 1 K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t
  have hab : 0 ≤ 1 - y := sub_nonneg.mpr hy1
  have hA : IntervalIntegrable (fun t : ℝ => ‖F (t + y)‖ ^ 2)
      volume 0 (1 - y) := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hB : IntervalIntegrable (fun t : ℝ => ‖F t‖ ^ 2)
      volume 0 (1 - y) := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hprod : IntervalIntegrable (fun t : ℝ => ‖F (t + y)‖ * ‖F t‖)
      volume 0 (1 - y) := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have havg : IntervalIntegrable
      (fun t : ℝ => (‖F (t + y)‖ ^ 2 + ‖F t‖ ^ 2) / 2)
      volume 0 (1 - y) := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hmono :
      (∫ t in (0 : ℝ)..(1 - y), ‖F (t + y)‖ * ‖F t‖) ≤
        ∫ t in (0 : ℝ)..(1 - y),
          (‖F (t + y)‖ ^ 2 + ‖F t‖ ^ 2) / 2 := by
    exact intervalIntegral.integral_mono_on hab hprod havg fun t _ => by
      nlinarith [sq_nonneg (‖F (t + y)‖ - ‖F t‖)]
  have havgEq :
      (∫ t in (0 : ℝ)..(1 - y),
          (‖F (t + y)‖ ^ 2 + ‖F t‖ ^ 2) / 2) =
        ((∫ t in (0 : ℝ)..(1 - y), ‖F (t + y)‖ ^ 2) +
          ∫ t in (0 : ℝ)..(1 - y), ‖F t‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add hA hB]
  have hshift :
      (∫ t in (0 : ℝ)..(1 - y), ‖F (t + y)‖ ^ 2) ≤ ‖x‖ ^ 2 := by
    simpa [F] using
      localizedFiniteFunction_unit_shifted_energy_le_norm_sq K x hy0 hy1
  have hinit :
      (∫ t in (0 : ℝ)..(1 - y), ‖F t‖ ^ 2) ≤ ‖x‖ ^ 2 := by
    simpa [F] using
      localizedFiniteFunction_unit_initial_energy_le_norm_sq K x hy0 hy1
  calc
    ‖∫ t in (0 : ℝ)..(1 - y), F (t + y) * conj (F t)‖
        ≤ ∫ t in (0 : ℝ)..(1 - y), ‖F (t + y) * conj (F t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in (0 : ℝ)..(1 - y), ‖F (t + y)‖ * ‖F t‖ := by
      apply intervalIntegral.integral_congr
      intro t _
      simp [norm_mul]
    _ ≤ ∫ t in (0 : ℝ)..(1 - y),
          (‖F (t + y)‖ ^ 2 + ‖F t‖ ^ 2) / 2 := hmono
    _ = ((∫ t in (0 : ℝ)..(1 - y), ‖F (t + y)‖ ^ 2) +
          ∫ t in (0 : ℝ)..(1 - y), ‖F t‖ ^ 2) / 2 := havgEq
    _ ≤ ‖x‖ ^ 2 := by nlinarith

/-- The complementary overlap orientation is the conjugate of the positive
overlap, so it has exactly the same norm bound. -/
theorem localizedFiniteFunction_negativeOverlap_norm_le_norm_sq
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖∫ t in (0 : ℝ)..(1 - y),
        localizedFiniteFunction 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t *
          conj (localizedFiniteFunction 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) (t + y))‖ ≤
      ‖x‖ ^ 2 := by
  let F : ℝ → ℂ := fun t =>
    localizedFiniteFunction 1 K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t
  have hconj :
      (∫ t in (0 : ℝ)..(1 - y), F t * conj (F (t + y))) =
        conj (∫ t in (0 : ℝ)..(1 - y), F (t + y) * conj (F t)) := by
    calc
      (∫ t in (0 : ℝ)..(1 - y), F t * conj (F (t + y))) =
          ∫ t in (0 : ℝ)..(1 - y),
            conj (F (t + y) * conj (F t)) := by
              apply intervalIntegral.integral_congr
              intro t _
              simp [map_mul, mul_comm]
      _ = conj (∫ t in (0 : ℝ)..(1 - y),
          F (t + y) * conj (F t)) := by
            exact intervalIntegral.intervalIntegral_conj
  rw [hconj]
  simpa using
    localizedFiniteFunction_positiveOverlap_norm_le_norm_sq K x hy0 hy1

/-- Standard L2 statement still required analytically: the symmetrized
autocorrelation of the normalized finite Fourier vector is bounded by twice
its Euclidean coefficient mass. -/
def LocalizedFiniteAutocorrelationBound : Prop :=
  ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
      |Complex.re
        (localizedWeilCorrelation
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          y)| ≤ 2 * ‖x‖ ^ 2

/-- The standard L2 autocorrelation estimate is now proved for the actual
localized finite Fourier vectors. -/
theorem localizedFiniteAutocorrelationBound_proved :
    LocalizedFiniteAutocorrelationBound := by
  intro K x y hy0 hy1
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  let F := localizedFiniteFunction 1 K u
  have hpos :=
    weilTest_localizedFiniteVector_pos K u
      (L := (1 : ℝ)) (y := y) hy0 hy1
  have hneg :=
    weilTest_localizedFiniteVector_neg K u
      (L := (1 : ℝ)) (y := y) hy0 hy1
  unfold localizedWeilCorrelation
  rw [hpos, hneg]
  calc
    |Complex.re
        ((∫ t in (0 : ℝ)..(1 - y), F (t + y) * conj (F t)) +
          ∫ t in (0 : ℝ)..(1 - y), F t * conj (F (t + y)))|
        ≤ ‖(∫ t in (0 : ℝ)..(1 - y), F (t + y) * conj (F t)) +
            ∫ t in (0 : ℝ)..(1 - y), F t * conj (F (t + y))‖ :=
          Complex.abs_re_le_norm _
    _ ≤ ‖∫ t in (0 : ℝ)..(1 - y), F (t + y) * conj (F t)‖ +
          ‖∫ t in (0 : ℝ)..(1 - y), F t * conj (F (t + y))‖ :=
          norm_add_le _ _
    _ ≤ ‖x‖ ^ 2 + ‖x‖ ^ 2 := by
      exact add_le_add
        (by simpa [F, u] using
          localizedFiniteFunction_positiveOverlap_norm_le_norm_sq K x hy0 hy1)
        (by simpa [F, u] using
          localizedFiniteFunction_negativeOverlap_norm_le_norm_sq K x hy0 hy1)
    _ = 2 * ‖x‖ ^ 2 := by ring

/-- The localized autocorrelation inequality immediately supplies the complete
source-contraction theorem, including both endpoints. -/
theorem sourceContractionBound_of_localizedAutocorrelation
    (h : LocalizedFiniteAutocorrelationBound) :
    SourceContractionBound := by
  intro K ω hω0 hω1 x
  rw [matrixRealEnergy_sourceMatrix_eq_localizedWeilCorrelation_re
    K x ω hω0 hω1]
  exact h K x (1 - ω) (sub_nonneg.mpr hω1) (by linarith)

/-- The elementary source contraction is uniformly bounded on the complete
source interval. -/
theorem sourceContractionBound_proved : SourceContractionBound :=
  sourceContractionBound_of_localizedAutocorrelation
    localizedFiniteAutocorrelationBound_proved

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceContract_eq_localizedWeilCorrelation_unit
#print axioms Zeta23.CCM.coefficientMass_re_eq_norm_sq
#print axioms Zeta23.CCM.localizedFiniteFunction_unit_energy_eq_norm_sq
#print axioms Zeta23.CCM.matrixRealEnergy_sourceMatrix_eq_localizedWeilCorrelation_re
#print axioms Zeta23.CCM.localizedFiniteFunction_unit_subinterval_energy_le_norm_sq
#print axioms Zeta23.CCM.localizedFiniteFunction_positiveOverlap_norm_le_norm_sq
#print axioms Zeta23.CCM.localizedFiniteAutocorrelationBound_proved
#print axioms Zeta23.CCM.sourceContractionBound_proved
#print axioms Zeta23.CCM.sourceContractionBound_of_localizedAutocorrelation
