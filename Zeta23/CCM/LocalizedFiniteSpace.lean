import Zeta23.CCM.LocalizedBasis
import Zeta23.CCM.DictionaryFiniteExpansion
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators Convolution ComplexConjugate

/-!
# Localized finite space and source autocorrelation

G0-B turns the formula-level character calculation from `LocalizedBasis.lean`
into an actual compactly supported finite function family.

The source interval is `[0,L]`.  Each Fourier mode is extended by zero to
all of `ℝ`, and arbitrary complex coefficient vectors use the existing
centered `Fin (2*N+1)` coordinates.

The source symmetrized correlation is written with the repository's
`EF.weilTest` convention.  Since `EF.weilTest g f = g ⋆ f̃`, this is the
commuted form of the source convolution `f̃ ⋆ g`; the two agree on the
additive real line.

This module deliberately stops before the localized Weil quadratic form,
form domains, form-core density, Rayleigh--Ritz convergence, positivity, or RH.
-/

/-- A normalized localized Fourier mode, extended by zero outside `[0,L]`. -/
def localizedZeroExtendedMode (L : ℝ) (n : ℤ) : ℝ → ℂ :=
  (Icc (0 : ℝ) L).indicator (localizedMode L n)

/-- The actual zero-extended finite localized vector attached to the repository's
full complex centered coefficient coordinates. -/
def localizedFiniteVector
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) : ℝ → ℂ :=
  fun x => ∑ i, u i * localizedZeroExtendedMode L (centeredIndex N i) x

/-- The finite vector is exactly the indicator of the formula-level finite Fourier
combination introduced in G0-A.  This is the main representation firewall between
the global character formula and the actual source-supported function. -/
theorem localizedFiniteVector_eq_indicator
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteVector L N u =
      (Icc (0 : ℝ) L).indicator (localizedFiniteFunction L N u) := by
  ext x
  by_cases hx : x ∈ Icc (0 : ℝ) L
  · simp [localizedFiniteVector, localizedZeroExtendedMode, hx]
  · simp [localizedFiniteVector, localizedZeroExtendedMode, localizedFiniteFunction, hx]

/-- Pointwise support of a zero-extended mode stays in the source interval. -/
theorem localizedZeroExtendedMode_support_subset
    (L : ℝ) (n : ℤ) :
    Function.support (localizedZeroExtendedMode L n) ⊆ Icc (0 : ℝ) L := by
  intro x hx
  by_contra hmem
  exact hx (by simp [localizedZeroExtendedMode, Set.indicator_of_notMem hmem])

/-- Pointwise support of every finite localized vector stays in the source interval. -/
theorem localizedFiniteVector_support_subset
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Function.support (localizedFiniteVector L N u) ⊆ Icc (0 : ℝ) L := by
  intro x hx
  by_contra hmem
  exact hx (by
    rw [localizedFiniteVector_eq_indicator]
    simp [Set.indicator_of_notMem hmem])

/-- Every finite localized vector has compact support. -/
theorem localizedFiniteVector_hasCompactSupport
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    HasCompactSupport (localizedFiniteVector L N u) := by
  refine HasCompactSupport.intro (K := Icc (0 : ℝ) L) isCompact_Icc ?_
  intro x hx
  by_contra hzero
  exact hx (localizedFiniteVector_support_subset L N u hzero)

/-- The formula-level finite Fourier combination is continuous on the real line. -/
@[fun_prop] theorem continuous_localizedFiniteFunction
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Continuous (localizedFiniteFunction L N u) := by
  unfold localizedFiniteFunction localizedMode
  fun_prop

/-- Every zero-extended finite localized vector is an actual L² function.
The proof uses only continuity of the finite Fourier combination, its boundedness
on the compact source interval, and the zero-extension support certificate. -/
theorem localizedFiniteVector_memLp_two
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    MemLp (localizedFiniteVector L N u) (2 : ENNReal) volume := by
  have hcont : Continuous (localizedFiniteFunction L N u) :=
    continuous_localizedFiniteFunction L N u
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  have hmeas : AEStronglyMeasurable (localizedFiniteVector L N u) volume := by
    rw [localizedFiniteVector_eq_indicator]
    exact hcont.aestronglyMeasurable.indicator measurableSet_Icc
  have hbound : ∀ᵐ x : ℝ ∂volume, ‖localizedFiniteVector L N u x‖ ≤ C := by
    filter_upwards with x
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · rw [localizedFiniteVector_eq_indicator, Set.indicator_of_mem hx]
      exact hC x hx
    · rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hx]
      simp
  exact (localizedFiniteVector_hasCompactSupport L N u).memLp_of_bound hmeas C hbound

/-- Source symmetrized correlation in repository convolution conventions.

The argument order is intentional: `EF.weilTest g f = g ⋆ f̃`, the commuted
version of the source `f̃ ⋆ g`.  Symmetrization at `y` and `-y` is the
source `q(f,g)` object. -/
def localizedWeilCorrelation (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun y => Zeta23.EF.weilTest g f y + Zeta23.EF.weilTest g f (-y)

/-- The source correlation is even by construction. -/
@[simp] theorem localizedWeilCorrelation_neg
    (f g : ℝ → ℂ) (y : ℝ) :
    localizedWeilCorrelation f g (-y) = localizedWeilCorrelation f g y := by
  simp [localizedWeilCorrelation, add_comm]

end Zeta23.CCM

#print axioms Zeta23.CCM.localizedFiniteVector_eq_indicator
#print axioms Zeta23.CCM.localizedFiniteVector_support_subset
#print axioms Zeta23.CCM.localizedFiniteVector_hasCompactSupport
#print axioms Zeta23.CCM.localizedFiniteVector_memLp_two
#print axioms Zeta23.CCM.localizedWeilCorrelation_neg
