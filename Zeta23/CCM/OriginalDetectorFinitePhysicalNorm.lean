import Zeta23.CCM.OriginalDetectorFinitePoleImage
import Zeta23.CCM.SourceContractionLocalized

/-! # Exact physical/coefficient norm normalization at every positive aperture -/

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace Zeta23.CCM

/-- Actual finite-Fourier Parseval normalization at arbitrary positive
aperture. This generalizes the inherited unit-aperture theorem using the
same proved zero-shift correlation identity. -/
theorem localizedFiniteFunction_energy_eq_norm_sq
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (∫ t in (0 : ℝ)..L, ‖localizedFiniteFunction L K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) t‖ ^ 2) = ‖x‖ ^ 2 := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  let f := localizedFiniteVector L K u
  have hzero := localizedWeilCorrelation_finiteVector_zero K u hL
  have hzero' : Zeta23.EF.weilTest f f 0 + Zeta23.EF.weilTest f f 0 =
      2 * coefficientMass K u := by
    simpa [f, localizedWeilCorrelation] using hzero
  have hweil : Zeta23.EF.weilTest f f 0 = coefficientMass K u := by
    linear_combination (1 / 2 : ℂ) * hzero'
  have hpos := weilTest_localizedFiniteVector_pos K u (L := L) (y := 0) (by norm_num) hL.le
  have hcomplex : (∫ t in (0 : ℝ)..L,
      localizedFiniteFunction L K u t * conj (localizedFiniteFunction L K u t)) =
        coefficientMass K u := by
    calc
      _ = Zeta23.EF.weilTest f f 0 := by simpa [f] using hpos.symm
      _ = _ := hweil
  have hcont : Continuous (fun t : ℝ => localizedFiniteFunction L K u t *
      conj (localizedFiniteFunction L K u t)) := by fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => localizedFiniteFunction L K u t *
      conj (localizedFiniteFunction L K u t)) volume (0 : ℝ) L :=
    hcont.intervalIntegrable (0 : ℝ) L
  have hre := congrArg Complex.re hcomplex
  have hre' : (∫ t in (0 : ℝ)..L,
      RCLike.re (localizedFiniteFunction L K u t * conj (localizedFiniteFunction L K u t))) =
        RCLike.re (coefficientMass K u) :=
    (intervalIntegral.intervalIntegral_re hint).trans hre
  have hreal (t : ℝ) : RCLike.re (localizedFiniteFunction L K u t *
      conj (localizedFiniteFunction L K u t)) = ‖localizedFiniteFunction L K u t‖ ^ 2 := by
    rw [Complex.mul_conj']
    simp [pow_two, Complex.mul_re]
  simp_rw [hreal] at hre'
  have hmass : RCLike.re (coefficientMass K u) = ‖x‖ ^ 2 := by
    simpa [u] using coefficientMass_re_eq_norm_sq K x
  rw [hmass] at hre'
  exact hre'

/-- The actual finite `Pq` image has exactly the native Euclidean norm,
with no aperture-dependent adjustment or unspecified isometry. -/
theorem originalDetectorFinitePoleImage_physical_energy_eq_norm_sq
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    (∫ t in (0 : ℝ)..L,
      ‖Zeta23.ExceptionalZero.poleKilled
        (originalDetectorFiniteWindowImage s L c (by linarith)) t‖ ^ 2) =
      ‖WithLp.toLp 2 (originalDetectorFinitePoleImageCoefficients s L c (by linarith))‖ ^ 2 := by
  rw [← localizedFiniteFunction_originalDetectorFinitePoleImageCoefficients s c hL]
  exact localizedFiniteFunction_energy_eq_norm_sq (by linarith)
    (originalDetectorQuarticCutoff L)
    (WithLp.toLp 2 (originalDetectorFinitePoleImageCoefficients s L c (by linarith)))

end Zeta23.CCM

#print axioms Zeta23.CCM.localizedFiniteFunction_energy_eq_norm_sq
#print axioms Zeta23.CCM.originalDetectorFinitePoleImage_physical_energy_eq_norm_sq
