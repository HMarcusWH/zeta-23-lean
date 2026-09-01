import Zeta23.CCM.BoundaryFlatFiniteSpace
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section

namespace Zeta23.CCM

open Complex
open Function
open MeasureTheory
open Set
open TopologicalSpace
open scoped BigOperators

/-!
# F0-B1C-A: finite AddCircle Fourier approximation in the localized basis

This module is the raw approximation half of F0-B1C.

It bridges Mathlib's finite Fourier span on `AddCircle L` to the repository's
exact centered finite coordinates `Fin (2*N+1)`, with the goal of uniform
control of the function and its first two formula-level jets on `[0,L]`.

The module deliberately stops before `boundaryFlatProject`, hard-window
legality of the raw approximant, genuine-Weil continuity, sign transfer, F1,
or RH.
-/

/-- A point outside the topological support has value zero. -/
theorem value_eq_zero_of_not_mem_tsupport
    {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ tsupport f) :
    f x = 0 := by
  by_contra hfx
  exact hx (subset_closure (show x ∈ support f from hfx))

/-- Strict support inside `(0,L)` kills the value and first two derivatives
at both endpoints. -/
theorem strictSupport_endpoint_jet_package
    {L : ℝ} {h : ℝ → ℂ}
    (hs : tsupport h ⊆ Ioo 0 L) :
    h 0 = 0 ∧ h L = 0 ∧
    deriv h 0 = 0 ∧ deriv h L = 0 ∧
    deriv (deriv h) 0 = 0 ∧ deriv (deriv h) L = 0 := by
  have h0not : (0 : ℝ) ∉ tsupport h := by
    intro h0
    have := hs h0
    exact (lt_irrefl (0 : ℝ)) this.1
  have hLnot : L ∉ tsupport h := by
    intro hL
    have := hs hL
    exact (lt_irrefl L) this.2
  have hds : tsupport (deriv h) ⊆ tsupport h :=
    tsupport_deriv_subset
  have hdds : tsupport (deriv (deriv h)) ⊆ tsupport (deriv h) :=
    tsupport_deriv_subset
  have hd0not : (0 : ℝ) ∉ tsupport (deriv h) := fun hx => h0not (hds hx)
  have hdLnot : L ∉ tsupport (deriv h) := fun hx => hLnot (hds hx)
  have hdd0not : (0 : ℝ) ∉ tsupport (deriv (deriv h)) :=
    fun hx => h0not (hds (hdds hx))
  have hddLnot : L ∉ tsupport (deriv (deriv h)) :=
    fun hx => hLnot (hds (hdds hx))
  exact ⟨
    value_eq_zero_of_not_mem_tsupport h0not,
    value_eq_zero_of_not_mem_tsupport hLnot,
    value_eq_zero_of_not_mem_tsupport hd0not,
    value_eq_zero_of_not_mem_tsupport hdLnot,
    value_eq_zero_of_not_mem_tsupport hdd0not,
    value_eq_zero_of_not_mem_tsupport hddLnot⟩

/-- Continuous periodic incarnation of the second derivative of a strict-collar
C² function. The positive-aperture and seam hypotheses are explicit: this
object is not defined by inventing behavior for nonpositive periods. -/
def periodicSecondDerivMap
    (L : ℝ) (h : ℝ → ℂ)
    (hL : 0 < L)
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L) :
    C(AddCircle L, ℂ) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hj := strictSupport_endpoint_jet_package (L := L) (h := h) hs
  have hdd : Continuous (deriv (deriv h)) := by
    have hd : ContDiff ℝ 1 (deriv h) := by
      simpa using hh.deriv'
    exact hd.continuous_deriv_one
  exact ⟨AddCircle.liftIoc L 0 (deriv (deriv h)),
    AddCircle.liftIoc_zero_continuous hj.2.2.2.2.2 hdd.continuousOn⟩

/-- Finite AddCircle Fourier polynomial encoded by a Finsupp coefficient vector. -/
def addCircleFourierPolynomial
    {L : ℝ} (c : ℤ →₀ ℂ) :
    C(AddCircle L, ℂ) :=
  c.sum fun n a => a • AddCircle.fourier n

/-- The normalized repository mode is Mathlib's AddCircle character multiplied
by the fixed `L^{-1/2}` normalization. -/
theorem localizedMode_eq_addCircle_fourier
    {L : ℝ} (n : ℤ) (x : ℝ) :
    localizedMode L n x =
      ((1 / Real.sqrt L : ℝ) : ℂ) *
        AddCircle.fourier n (x : AddCircle L) := by
  rw [AddCircle.fourier_coe_apply]
  unfold localizedMode
  congr 2
  push_cast
  ring

/-- The repository frequency is the usual AddCircle frequency. -/
theorem localizedFrequency_eq_addCircle_frequency
    {L : ℝ} (n : ℤ) :
    localizedFrequency L n =
      (2 * Real.pi * Complex.I * (n : ℂ)) / (L : ℂ) := by
  unfold localizedFrequency localizedBaseFrequency
  push_cast
  ring

/-- Nonzero Fourier index has nonzero frequency for positive aperture. -/
theorem localizedFrequency_ne_zero
    {L : ℝ} (hL : 0 < L) {n : ℤ} (hn : n ≠ 0) :
    localizedFrequency L n ≠ 0 := by
  rw [localizedFrequency_eq_addCircle_frequency]
  simp [hL.ne', Real.pi_ne_zero, hn, Complex.I_ne_zero]

/-- The coordinate slot centered at zero. -/
def centeredZeroIndex (N : ℕ) : Fin (2 * N + 1) :=
  ⟨N, by omega⟩

@[simp] theorem centeredIndex_centeredZeroIndex
    (N : ℕ) :
    centeredIndex N (centeredZeroIndex N) = 0 := by
  simp [centeredZeroIndex, centeredIndex]

/-- Every integer in the centered interval `[-N,N]` is represented by one
repository coordinate. -/
theorem exists_centeredIndex_eq_of_bounds
    {N : ℕ} {n : ℤ}
    (hlo : -(N : ℤ) ≤ n)
    (hhi : n ≤ (N : ℤ)) :
    ∃ i : Fin (2 * N + 1), centeredIndex N i = n := by
  let k : ℕ := (n + (N : ℤ)).toNat
  have hk0 : 0 ≤ n + (N : ℤ) := by omega
  have hkcast : (k : ℤ) = n + (N : ℤ) := by
    dsimp [k]
    rw [Int.toNat_of_nonneg hk0]
  have hklt : k < 2 * N + 1 := by
    rw [← Int.ofNat_lt]
    simp only [Int.natCast_add, Int.natCast_mul, Int.ofNat_ofNat]
    omega
  refine ⟨⟨k, hklt⟩, ?_⟩
  simp [centeredIndex, k, hkcast]

/-- Finite integer support is contained in some symmetric centered aperture. -/
theorem exists_support_natAbs_bound
    (c : ℤ →₀ ℂ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ∈ c.support, Int.natAbs n ≤ N := by
  let N₀ : ℕ := c.support.sup Int.natAbs
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro n hn
  exact (Finset.le_sup hn).trans (le_max_right _ _)

/-- Coefficient vector on the repository centered coordinates obtained by
padding an integer Finsupp with zeros outside `[-N,N]`. The `sqrt L`
factor compensates for the repository's normalized `localizedMode`. -/
def centeredCoefficientsOfFinsupp
    (L : ℝ) (N : ℕ) (c : ℤ →₀ ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i => ((Real.sqrt L : ℝ) : ℂ) * c (centeredIndex N i)

/-- The zero mode contributes no first formula-level jet. -/
theorem localizedFiniteFirstJet_zeroMode_single
    (L : ℝ) (N : ℕ) (z : ℂ) (x : ℝ) :
    localizedFiniteFirstJet L N
      (fun i => if i = centeredZeroIndex N then z else 0) x = 0 := by
  unfold localizedFiniteFirstJet
  rw [Finset.sum_eq_zero]
  intro i hi
  by_cases hiz : i = centeredZeroIndex N
  · subst i
    simp
  · simp [hiz]

/-- The zero mode contributes no second formula-level jet. -/
theorem localizedFiniteSecondJet_zeroMode_single
    (L : ℝ) (N : ℕ) (z : ℂ) (x : ℝ) :
    localizedFiniteSecondJet L N
      (fun i => if i = centeredZeroIndex N then z else 0) x = 0 := by
  unfold localizedFiniteSecondJet
  rw [Finset.sum_eq_zero]
  intro i hi
  by_cases hiz : i = centeredZeroIndex N
  · subst i
    simp
  · simp [hiz]

end Zeta23.CCM
