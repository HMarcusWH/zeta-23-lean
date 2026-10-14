import Zeta23.ExceptionalZero.NativeActualInputZeroJets
import Zeta23.CCM.NativeCompletedInputRangeOfPrimeLp
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

/-!
# The two native analytic closing statements are sufficient for RH

A-X and B-Y below are explicit, unresolved propositions about the literal
original field and the actual causal completion operator. Their sufficiency
uses the physical zero-jet obstruction, including the reflected actual zero
and its prescribed positive damping. No inverse or convergence assertion is
an additional premise. The half-line integral formulation of A-X is proved
equivalent to its full-line L2 formulation, using actual causal support.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped Topology ENNReal

namespace Zeta23.CCM

/-- OPEN A-X: actual original prime-field L2 control at every positive damping. -/
def NativeOriginalPrimeFieldAllDampedL2 : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume

/-- OPEN A-X in its original half-line weighted-square integral formulation. -/
def NativeOriginalPrimeFieldAllDampedIntegral : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
      (Real.exp (-2 * epsilon * t) * |nativeOriginalPrimeField t| ^ 2)) < ∞

/-- OPEN B-Y: the actual stable input belongs to the actual causal range closure. -/
def NativeInputAllRangeClosure : Prop :=
  ∀ (epsilon : ℝ) (hepsilon : 0 < epsilon),
    nativeCompletedInputCausalL2 epsilon hepsilon.le ∈
      closure (Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon.le))

theorem nativeOriginalDampedPrimeField_continuous (epsilon : ℝ) :
    Continuous (nativeOriginalDampedPrimeField epsilon) := by
  unfold nativeOriginalDampedPrimeField
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      nativeOriginalPrimeField_continuous)

theorem nativeOriginalDampedPrimeField_norm_sq (epsilon t : ℝ) :
    ‖nativeOriginalDampedPrimeField epsilon t‖ ^ 2 =
      Real.exp (-2 * epsilon * t) * |nativeOriginalPrimeField t| ^ 2 := by
  rw [nativeOriginalDampedPrimeField, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _), mul_pow]
  have he : Real.exp (-epsilon * t) ^ 2 = Real.exp (-2 * epsilon * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]

/-- Full-line L2 membership is exactly the original nonnegative half-line
integral condition. The field vanishes at every negative time. -/
theorem nativeOriginalDampedPrimeField_memLp_iff_halfLineIntegral (epsilon : ℝ) :
    MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume ↔
      (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
        (Real.exp (-2 * epsilon * t) * |nativeOriginalPrimeField t| ^ 2)) < ∞ := by
  let W : ℝ → ℝ := fun t =>
    Real.exp (-2 * epsilon * t) * |nativeOriginalPrimeField t| ^ 2
  have hW : Continuous W := by
    dsimp [W]
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (nativeOriginalPrimeField_continuous.abs.pow 2)
  have hWnonneg : ∀ t, 0 ≤ W t := fun t =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hfinite : (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal (W t)) < ∞ ↔
      IntegrableOn W (Ici 0) := by
    rw [lt_top_iff_ne_top]
    exact lintegral_ofReal_ne_top_iff_integrable
      hW.aestronglyMeasurable (Filter.Eventually.of_forall hWnonneg)
  rw [memLp_two_iff_integrable_sq_norm
    (nativeOriginalDampedPrimeField_continuous epsilon).aestronglyMeasurable]
  change Integrable (fun t : ℝ => ‖nativeOriginalDampedPrimeField epsilon t‖ ^ 2) ↔
    (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal (W t)) < ∞
  rw [hfinite]
  constructor
  · intro h
    exact h.integrableOn.congr_fun
      (fun t _ => nativeOriginalDampedPrimeField_norm_sq epsilon t) measurableSet_Ici
  · intro h
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
    refine ⟨?_, ?_⟩
    · exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun
        (fun t ht => by
          change (0 : ℝ) = ‖nativeOriginalDampedPrimeField epsilon t‖ ^ 2
          rw [nativeOriginalDampedPrimeField_zero_of_neg epsilon ht, norm_zero]
          norm_num) measurableSet_Iio
    · exact h.congr_fun
        (fun t _ => (nativeOriginalDampedPrimeField_norm_sq epsilon t).symm) measurableSet_Ici

theorem nativeOriginalPrimeField_allDampedL2_iff_integral :
    NativeOriginalPrimeFieldAllDampedL2 ↔ NativeOriginalPrimeFieldAllDampedIntegral := by
  constructor
  · intro h epsilon hepsilon
    exact (nativeOriginalDampedPrimeField_memLp_iff_halfLineIntegral epsilon).mp (h epsilon hepsilon)
  · intro h epsilon hepsilon
    exact (nativeOriginalDampedPrimeField_memLp_iff_halfLineIntegral epsilon).mpr (h epsilon hepsilon)

/-- A-X implies B-Y by the independently proved literal a*X=Y equation and
the actual Bochner representative bridge. No converse is asserted. -/
theorem nativeInput_allRangeClosure_of_originalPrimeField_allDampedL2
    (hX : NativeOriginalPrimeFieldAllDampedL2) : NativeInputAllRangeClosure := by
  intro epsilon hepsilon
  exact nativeCompletedInput_mem_rangeClosure_of_prime_memLp epsilon hepsilon.le (hX epsilon hepsilon)

end Zeta23.CCM

namespace Zeta23.ExceptionalZero

/-- B-Y is an explicit OPEN sufficient premise for Mathlib's exact RH statement. -/
theorem riemannHypothesis_of_nativeInput_allRangeClosure
    (hY : CCM.NativeInputAllRangeClosure) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hs : IsNontrivialZero s :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hmem : s ∈ zetaZeroConfig.carrier := by simpa using hs
  let rho : zetaZeroConfig.carrier := ⟨s, hmem⟩
  by_contra hoff
  exact nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero rho hoff
    (hY (nativeZeroJetDamping rho) (nativeZeroJetDamping_pos rho hoff))

/-- A-X is an explicit OPEN sufficient premise; its implication factors
through actual B-Y and the physical off-line-zero obstruction. -/
theorem riemannHypothesis_of_originalPrimeField_allDampedL2
    (hX : CCM.NativeOriginalPrimeFieldAllDampedL2) : RiemannHypothesis :=
  riemannHypothesis_of_nativeInput_allRangeClosure
    (CCM.nativeInput_allRangeClosure_of_originalPrimeField_allDampedL2 hX)

theorem riemannHypothesis_of_originalPrimeField_allDampedIntegral
    (hX : CCM.NativeOriginalPrimeFieldAllDampedIntegral) : RiemannHypothesis :=
  riemannHypothesis_of_originalPrimeField_allDampedL2
    (CCM.nativeOriginalPrimeField_allDampedL2_iff_integral.mpr hX)

end Zeta23.ExceptionalZero

#print axioms Zeta23.CCM.nativeOriginalDampedPrimeField_continuous
#print axioms Zeta23.CCM.nativeOriginalDampedPrimeField_norm_sq
#print axioms Zeta23.CCM.nativeOriginalDampedPrimeField_memLp_iff_halfLineIntegral
#print axioms Zeta23.CCM.nativeOriginalPrimeField_allDampedL2_iff_integral
#print axioms Zeta23.CCM.nativeInput_allRangeClosure_of_originalPrimeField_allDampedL2
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_nativeInput_allRangeClosure
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_originalPrimeField_allDampedL2
#print axioms Zeta23.ExceptionalZero.riemannHypothesis_of_originalPrimeField_allDampedIntegral
