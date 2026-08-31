import Zeta23.CCM.LocalizedFiniteSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace Zeta23.CCM

open Complex Set
open scoped BigOperators

/-!
# G1-B1A: finite-sector source kappa map

This module theorem-locks the finite coordinate transport used by
Connes--Consani--Moscovici before the localized Weil functional is introduced.

For `lambda > 1`, the source aperture is

`L = 2 * log(lambda)`

and the logarithmic coordinate map is

`x = log(lambda * u)`,

sending the multiplicative interval `[lambda⁻¹, lambda]` to the additive
interval `[0,L]`.  The explicit reverse coordinate is
`u = lambda⁻¹ * exp(x)`.

The source paper defines `V_n = kappa(U_n)` (equation (3.21)); accordingly
`sourceMultiplicativeMode` is a formula-level theorem lock of that convention,
not an independently derived object.  The source finite vector used below is
then the actual zero-extended span on `[lambda⁻¹, lambda]`, matching the
paper's finite `E_N` test-function convention.

Claim firewall: this file does not define or identify the multiplicative Haar
measure `d*u`, the bundled L2 isometry in Proposition 3.2(i), `QW_lambda`,
`PsiSharp`, form-core density, Rayleigh--Ritz convergence, positivity,
Suzuki, or RH.
-/

/-- Source aperture parameter `L = 2 * log(lambda)`. -/
def sourceLength (lam : ℝ) : ℝ :=
  2 * Real.log lam

/-- Logarithmic coordinate used by the source kappa map. -/
def sourceLogCoordinate (lam u : ℝ) : ℝ :=
  Real.log (lam * u)

/-- Explicit inverse coordinate to `u ↦ log(lambda*u)`. -/
def sourceExpCoordinate (lam x : ℝ) : ℝ :=
  lam⁻¹ * Real.exp x

/-- The source aperture is positive whenever `lambda > 1`. -/
theorem sourceLength_pos
    {lam : ℝ} (hlam : 1 < lam) :
    0 < sourceLength lam := by
  unfold sourceLength
  have hlog : 0 < Real.log lam := Real.log_pos hlam
  linarith

/-- The lower multiplicative endpoint maps to additive coordinate zero. -/
theorem sourceLogCoordinate_inv
    {lam : ℝ} (hlam : 1 < lam) :
    sourceLogCoordinate lam lam⁻¹ = 0 := by
  have hne : lam ≠ 0 := by linarith
  simp [sourceLogCoordinate, hne]

/-- The upper multiplicative endpoint maps to additive coordinate `L`. -/
theorem sourceLogCoordinate_self
    {lam : ℝ} (hlam : 1 < lam) :
    sourceLogCoordinate lam lam = sourceLength lam := by
  have hne : lam ≠ 0 := by linarith
  unfold sourceLogCoordinate sourceLength
  rw [Real.log_mul hne hne]
  ring

/-- The full source multiplicative interval maps into the additive source
interval. -/
theorem sourceLogCoordinate_mem_Icc
    {lam u : ℝ}
    (hlam : 1 < lam)
    (hu : u ∈ Icc lam⁻¹ lam) :
    sourceLogCoordinate lam u ∈ Icc 0 (sourceLength lam) := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hinv0 : 0 < lam⁻¹ := inv_pos.mpr hlam0
  have hu0 : 0 < u := lt_of_lt_of_le hinv0 hu.1
  have hne : lam ≠ 0 := ne_of_gt hlam0
  have hlower : 1 ≤ lam * u := by
    have hmul := mul_le_mul_of_nonneg_left hu.1 hlam0.le
    simpa [hne] using hmul
  have hupper : lam * u ≤ lam * lam :=
    mul_le_mul_of_nonneg_left hu.2 hlam0.le
  have hprod0 : 0 < lam * u := mul_pos hlam0 hu0
  have hsq0 : 0 < lam * lam := mul_pos hlam0 hlam0
  constructor
  · exact Real.log_nonneg hlower
  · have hlog :
        Real.log (lam * u) ≤ Real.log (lam * lam) :=
      (Real.log_le_log_iff hprod0 hsq0).2 hupper
    rw [Real.log_mul hne hne] at hlog
    simpa [sourceLogCoordinate, sourceLength, two_mul] using hlog

/-- Logarithmic coordinate after the explicit reverse coordinate is exactly
the original additive coordinate. -/
theorem sourceLogCoordinate_sourceExpCoordinate
    {lam : ℝ} (hlam : 1 < lam) (x : ℝ) :
    sourceLogCoordinate lam (sourceExpCoordinate lam x) = x := by
  have hne : lam ≠ 0 := by linarith
  unfold sourceLogCoordinate sourceExpCoordinate
  have hprod :
      lam * (lam⁻¹ * Real.exp x) = Real.exp x := by
    calc
      lam * (lam⁻¹ * Real.exp x) =
          (lam * lam⁻¹) * Real.exp x := by ring
      _ = Real.exp x := by simp [hne]
  rw [hprod, Real.log_exp]

/-- The explicit reverse coordinate after the logarithmic coordinate is exactly
the original positive multiplicative coordinate. -/
theorem sourceExpCoordinate_sourceLogCoordinate
    {lam u : ℝ}
    (hlam : 1 < lam)
    (hu : 0 < u) :
    sourceExpCoordinate lam (sourceLogCoordinate lam u) = u := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hne : lam ≠ 0 := ne_of_gt hlam0
  unfold sourceExpCoordinate sourceLogCoordinate
  rw [Real.exp_log (mul_pos hlam0 hu)]
  calc
    lam⁻¹ * (lam * u) = (lam⁻¹ * lam) * u := by ring
    _ = u := by simp [hne]

/-- The explicit reverse coordinate sends the additive source interval back
into the multiplicative source interval. -/
theorem sourceExpCoordinate_mem_Icc
    {lam x : ℝ}
    (hlam : 1 < lam)
    (hx : x ∈ Icc 0 (sourceLength lam)) :
    sourceExpCoordinate lam x ∈ Icc lam⁻¹ lam := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hinv0 : 0 < lam⁻¹ := inv_pos.mpr hlam0
  have hne : lam ≠ 0 := ne_of_gt hlam0
  have hexpLower : 1 ≤ Real.exp x := by
    have h := Real.exp_le_exp.mpr hx.1
    simpa using h
  have hLexp : Real.exp (sourceLength lam) = lam * lam := by
    unfold sourceLength
    rw [show 2 * Real.log lam = Real.log lam + Real.log lam by ring,
      Real.exp_add]
    simp [Real.exp_log hlam0]
  have hexpUpper : Real.exp x ≤ lam * lam := by
    have h := Real.exp_le_exp.mpr hx.2
    rw [hLexp] at h
    exact h
  constructor
  · unfold sourceExpCoordinate
    simpa using mul_le_mul_of_nonneg_left hexpLower hinv0.le
  · unfold sourceExpCoordinate
    calc
      lam⁻¹ * Real.exp x ≤ lam⁻¹ * (lam * lam) :=
        mul_le_mul_of_nonneg_left hexpUpper hinv0.le
      _ = (lam⁻¹ * lam) * lam := by ring
      _ = lam := by simp [hne]

/-- The repository additive Fourier mode is smooth before zero extension. -/
@[fun_prop] theorem contDiff_localizedMode
    (L : ℝ) (n : ℤ) :
    ContDiff ℝ ⊤ (localizedMode L n) := by
  unfold localizedMode
  have hreal :
      ContDiff ℝ ⊤
        (fun x : ℝ => 2 * Real.pi * (n : ℝ) * x / L) := by
    fun_prop
  have hcast :
      ContDiff ℝ ⊤
        (fun x : ℝ =>
          (((2 * Real.pi * (n : ℝ) * x / L : ℝ)) : ℂ)) := by
    change ContDiff ℝ ⊤
      (Complex.ofRealCLM ∘
        (fun x : ℝ => 2 * Real.pi * (n : ℝ) * x / L))
    exact Complex.ofRealCLM.contDiff.comp hreal
  have hphase :
      ContDiff ℝ ⊤
        (fun x : ℝ =>
          Complex.I *
            (((2 * Real.pi * (n : ℝ) * x / L : ℝ)) : ℂ)) :=
    contDiff_const.mul hcast
  have hexp :
      ContDiff ℝ ⊤
        (fun x : ℝ =>
          Complex.exp
            (Complex.I *
              (((2 * Real.pi * (n : ℝ) * x / L : ℝ)) : ℂ))) :=
    hphase.cexp
  exact contDiff_const.mul hexp

/-- Every formula-level finite Fourier combination is smooth before zero
extension.  This is the correct source-domain formula object; the zero-extended
`localizedFiniteVector` is not asserted smooth at the endpoints. -/
@[fun_prop] theorem contDiff_localizedFiniteFunction
    (L : ℝ) (N : ℕ)
    (u : Fin (2 * N + 1) → ℂ) :
    ContDiff ℝ ⊤ (localizedFiniteFunction L N u) := by
  unfold localizedFiniteFunction
  fun_prop

/-- Literal source kappa coordinate pullback.  This raw formula is total as a
Lean function on `ℝ`; promoted source statements below impose `lambda > 1`
and localize to `[lambda⁻¹,lambda]`.  No measure or Hilbert-space structure is
hidden in this definition. -/
def sourceKappa
    (lam : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => f (sourceLogCoordinate lam u)

/-- Formula-level source mode `V_n` from equation (3.21):
`V_n(u)=U_n(log(lambda*u))`.  Its source semantics are restricted to
`u ∈ [lambda⁻¹,lambda]`; zero extension is modeled separately below. -/
def sourceMultiplicativeMode
    (lam : ℝ) (n : ℤ) (u : ℝ) : ℂ :=
  ((1 / Real.sqrt (sourceLength lam) : ℝ) : ℂ) *
    Complex.exp
      (Complex.I *
        (((2 * Real.pi * (n : ℝ) * sourceLogCoordinate lam u /
          sourceLength lam : ℝ) : ℂ)))

/-- Equation-(3.21) theorem lock: kappa maps the repository's normalized
additive mode to the source formula-level `V_n`.  The equality is
definition-level because the source itself defines `V_n = kappa(U_n)`. -/
theorem sourceKappa_localizedMode_eq_sourceMultiplicativeMode
    {lam : ℝ} (_hlam : 1 < lam) (n : ℤ) :
    sourceKappa lam (localizedMode (sourceLength lam) n) =
      sourceMultiplicativeMode lam n := by
  rfl

/-- Formula-level finite source Fourier combination in centered coordinates.
This is not by itself the ambient zero-extended `E_N` test vector. -/
def sourceFiniteFourierFunction
    (lam : ℝ)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ)
    (u : ℝ) : ℂ :=
  ∑ i,
    coeff i *
      sourceMultiplicativeMode lam (centeredIndex N i) u

/-- Kappa maps every arbitrary-complex repository finite Fourier formula
exactly to the corresponding source formula, with the same centered
coefficients. -/
theorem sourceKappa_localizedFiniteFunction_eq_sourceFiniteFourierFunction
    {lam : ℝ} (_hlam : 1 < lam)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) :
    sourceKappa lam
        (localizedFiniteFunction (sourceLength lam) N coeff) =
      sourceFiniteFourierFunction lam N coeff := by
  funext u
  simp [sourceKappa, localizedFiniteFunction,
    sourceFiniteFourierFunction, sourceMultiplicativeMode,
    localizedMode, sourceLogCoordinate]

/-- One source mode, extended by zero outside the multiplicative source
interval. -/
def sourceZeroExtendedMode
    (lam : ℝ) (n : ℤ) : ℝ → ℂ :=
  (Icc lam⁻¹ lam).indicator (sourceMultiplicativeMode lam n)

/-- Actual zero-extended finite source vector representing the paper's
finite `E_N` test-function convention. -/
def sourceFiniteVector
    (lam : ℝ)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) : ℝ → ℂ :=
  (Icc lam⁻¹ lam).indicator
    (sourceFiniteFourierFunction lam N coeff)

/-- The actual source finite vector is the centered finite sum of the
zero-extended source modes. -/
theorem sourceFiniteVector_eq_sum_zeroExtendedModes
    (lam : ℝ)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) :
    sourceFiniteVector lam N coeff =
      fun u => ∑ i,
        coeff i *
          sourceZeroExtendedMode lam (centeredIndex N i) u := by
  funext u
  by_cases hu : u ∈ Icc lam⁻¹ lam
  · simp [sourceFiniteVector, sourceZeroExtendedMode,
      sourceFiniteFourierFunction, hu]
  · simp [sourceFiniteVector, sourceZeroExtendedMode, hu]

/-- Every source finite vector is supported inside the source multiplicative
interval. -/
theorem sourceFiniteVector_support_subset
    (lam : ℝ)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) :
    Function.support (sourceFiniteVector lam N coeff) ⊆
      Icc lam⁻¹ lam := by
  intro u hu
  by_contra hmem
  exact hu (by
    simp [sourceFiniteVector, Set.indicator_of_notMem hmem])

/-- Every source finite vector has compact support as an ambient real
function. -/
theorem sourceFiniteVector_hasCompactSupport
    (lam : ℝ)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) :
    HasCompactSupport (sourceFiniteVector lam N coeff) := by
  refine HasCompactSupport.intro
    (K := Icc lam⁻¹ lam) isCompact_Icc ?_
  intro u hu
  by_contra hzero
  exact hu (sourceFiniteVector_support_subset lam N coeff hzero)

/-- Zero-extended kappa image on the source multiplicative interval. -/
def sourceKappaFiniteVector
    (lam : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Icc lam⁻¹ lam).indicator (sourceKappa lam f)

/-- **G1-B1A production endpoint.**

For `lambda > 1`, the zero-extended kappa image of every arbitrary-complex
repository finite Fourier formula is exactly the corresponding actual finite
source vector, with the same centered coefficient coordinates. -/
theorem sourceKappaFiniteVector_eq_sourceFiniteVector
    {lam : ℝ} (hlam : 1 < lam)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) :
    sourceKappaFiniteVector lam
        (localizedFiniteFunction (sourceLength lam) N coeff) =
      sourceFiniteVector lam N coeff := by
  unfold sourceKappaFiniteVector sourceFiniteVector
  rw [sourceKappa_localizedFiniteFunction_eq_sourceFiniteFourierFunction
    hlam N coeff]

/-- Predicate naming the actual zero-extended finite source Fourier sector
represented by the repository's centered coefficient coordinates. -/
def IsSourceFiniteFourierVector
    (lam : ℝ)
    (N : ℕ)
    (F : ℝ → ℂ) : Prop :=
  ∃ coeff : Fin (2 * N + 1) → ℂ,
    F = sourceFiniteVector lam N coeff

/-- Every localized kappa image of a repository finite Fourier formula lies in
the actual zero-extended finite source Fourier sector. -/
theorem sourceKappa_localizedFiniteFunction_isSourceFiniteFourierVector
    {lam : ℝ} (hlam : 1 < lam)
    (N : ℕ)
    (coeff : Fin (2 * N + 1) → ℂ) :
    IsSourceFiniteFourierVector lam N
      (sourceKappaFiniteVector lam
        (localizedFiniteFunction (sourceLength lam) N coeff)) := by
  refine ⟨coeff, ?_⟩
  exact sourceKappaFiniteVector_eq_sourceFiniteVector hlam N coeff

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceLength_pos
#print axioms Zeta23.CCM.sourceLogCoordinate_inv
#print axioms Zeta23.CCM.sourceLogCoordinate_self
#print axioms Zeta23.CCM.sourceLogCoordinate_mem_Icc
#print axioms Zeta23.CCM.sourceLogCoordinate_sourceExpCoordinate
#print axioms Zeta23.CCM.sourceExpCoordinate_sourceLogCoordinate
#print axioms Zeta23.CCM.sourceExpCoordinate_mem_Icc
#print axioms Zeta23.CCM.contDiff_localizedMode
#print axioms Zeta23.CCM.contDiff_localizedFiniteFunction
#print axioms Zeta23.CCM.sourceKappa_localizedMode_eq_sourceMultiplicativeMode
#print axioms Zeta23.CCM.sourceKappa_localizedFiniteFunction_eq_sourceFiniteFourierFunction
#print axioms Zeta23.CCM.sourceFiniteVector_eq_sum_zeroExtendedModes
#print axioms Zeta23.CCM.sourceFiniteVector_support_subset
#print axioms Zeta23.CCM.sourceFiniteVector_hasCompactSupport
#print axioms Zeta23.CCM.sourceKappaFiniteVector_eq_sourceFiniteVector
#print axioms Zeta23.CCM.sourceKappa_localizedFiniteFunction_isSourceFiniteFourierVector
