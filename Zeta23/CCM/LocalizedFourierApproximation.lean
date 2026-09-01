import Zeta23.CCM.BoundaryFlatFiniteSpace
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
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
  have hseam : deriv (deriv h) 0 = deriv (deriv h) L := by
    rw [hj.2.2.2.2.1, hj.2.2.2.2.2]
  exact ⟨AddCircle.liftIoc L 0 (deriv (deriv h)),
    AddCircle.liftIoc_zero_continuous hseam hdd.continuousOn⟩

/-- Finite AddCircle Fourier polynomial encoded by a Finsupp coefficient vector. -/
def addCircleFourierPolynomial
    {L : ℝ} (c : ℤ →₀ ℂ) :
    C(AddCircle L, ℂ) :=
  c.sum fun n a => a • fourier n

/-- The normalized repository mode is Mathlib's AddCircle character multiplied
by the fixed `L^{-1/2}` normalization. -/
theorem localizedMode_eq_addCircle_fourier
    {L : ℝ} (n : ℤ) (x : ℝ) :
    localizedMode L n x =
      ((1 / Real.sqrt L : ℝ) : ℂ) *
        fourier n (x : AddCircle L) := by
  rw [fourier_coe_apply]
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


/-- Basic algebra for the finite AddCircle Fourier polynomial. -/
@[simp] theorem addCircleFourierPolynomial_zero
    {L : ℝ} :
    addCircleFourierPolynomial (L := L) 0 = 0 := by
  ext x
  simp [addCircleFourierPolynomial]

@[simp] theorem addCircleFourierPolynomial_single
    {L : ℝ} (n : ℤ) (a : ℂ) :
    addCircleFourierPolynomial (L := L) (Finsupp.single n a) =
      a • fourier n := by
  ext x
  simp [addCircleFourierPolynomial]

theorem addCircleFourierPolynomial_add
    {L : ℝ} (c d : ℤ →₀ ℂ) :
    addCircleFourierPolynomial (L := L) (c + d) =
      addCircleFourierPolynomial c + addCircleFourierPolynomial d := by
  ext x
  simp [addCircleFourierPolynomial, Finsupp.sum_add_index]

/-- Every finite-span AddCircle approximant may be represented by an explicit
integer Finsupp coefficient vector. -/
theorem exists_addCircleFourierPolynomial_norm_sub_lt
    {L : ℝ} [Fact (0 < L)]
    (F : C(AddCircle L, ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℤ →₀ ℂ,
      ‖addCircleFourierPolynomial c - F‖ < δ := by
  have hmem :
      F ∈ (Submodule.span ℂ (Set.range (@fourier L))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    simp
  obtain ⟨r, hrspan, hdist⟩ :=
    (Metric.mem_closure_iff.mp hmem) δ hδ
  obtain ⟨c, hc⟩ :=
    (Finsupp.mem_span_range_iff_exists_finsupp (R := ℂ)).mp hrspan
  refine ⟨c, ?_⟩
  have hpoly : addCircleFourierPolynomial c = r := by
    simpa [addCircleFourierPolynomial] using hc
  rw [hpoly]
  simpa [dist_eq_norm, norm_sub_rev] using hdist

/-- Fourier coefficients of one finite AddCircle Fourier polynomial are exactly
its Finsupp coefficients. -/
theorem fourierCoeff_addCircleFourierPolynomial
    {L : ℝ} [Fact (0 < L)]
    (c : ℤ →₀ ℂ) :
    fourierCoeff (addCircleFourierPolynomial c) = c := by
  induction c using Finsupp.induction_linear with
  | zero =>
      ext m
      simp [addCircleFourierPolynomial, fourierCoeff]
  | add c d hc hd =>
      rw [addCircleFourierPolynomial_add]
      have hci :
          Integrable (addCircleFourierPolynomial c)
            (@AddCircle.haarAddCircle L inferInstance) :=
        (addCircleFourierPolynomial c).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hdi :
          Integrable (addCircleFourierPolynomial d)
            (@AddCircle.haarAddCircle L inferInstance) :=
        (addCircleFourierPolynomial d).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [fourierCoeff.add hci hdi, hc, hd]
      rfl
  | single n a =>
      rw [addCircleFourierPolynomial_single,
        fourierCoeff.const_smul,
        fourierCoeff_fourier]
      ext m
      by_cases hmn : m = n
      · subst m
        simp
      · simp [hmn]

/-- A Fourier coefficient of a continuous AddCircle function is bounded by its
uniform norm. -/
theorem norm_fourierCoeff_le_norm
    {L : ℝ} [Fact (0 < L)]
    (F : C(AddCircle L, ℂ)) (n : ℤ) :
    ‖fourierCoeff F n‖ ≤ ‖F‖ := by
  unfold fourierCoeff
  have h :=
    norm_integral_le_of_norm_le_const
      (μ := @AddCircle.haarAddCircle L inferInstance)
      (f := fun t : AddCircle L => fourier (-n) t • F t)
      (C := ‖F‖)
      (Filter.Eventually.of_forall fun t => by
        rw [norm_smul]
        have hfourier : ‖fourier (-n) t‖ = 1 := by
          rw [fourier_apply, Circle.norm_coe]
        rw [hfourier, one_mul]
        exact ContinuousMap.norm_coe_le_norm F t)
  simpa using h


/-- Fourier coefficients respect subtraction for continuous AddCircle maps. -/
theorem fourierCoeff_sub
    {L : ℝ} [Fact (0 < L)]
    (F G : C(AddCircle L, ℂ)) :
    fourierCoeff (F - G) =
      fourierCoeff F - fourierCoeff G := by
  have hFi :
      Integrable F (@AddCircle.haarAddCircle L inferInstance) :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGi :
      Integrable G (@AddCircle.haarAddCircle L inferInstance) :=
    G.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  ext n
  unfold fourierCoeff
  simp only [ContinuousMap.sub_apply, smul_sub]
  rw [integral_sub (hFi.fourier_smul (-n)) (hGi.fourier_smul (-n))]
  rfl

/-- Removing the integer zero coefficient removes exactly the constant Fourier
mode. -/
theorem addCircleFourierPolynomial_erase_zero
    {L : ℝ} (c : ℤ →₀ ℂ) :
    addCircleFourierPolynomial (L := L) (c.erase 0) =
      addCircleFourierPolynomial c - c 0 • fourier 0 := by
  have h := congrArg (addCircleFourierPolynomial (L := L))
    (Finsupp.erase_add_single 0 c)
  rw [addCircleFourierPolynomial_add,
    addCircleFourierPolynomial_single] at h
  exact eq_sub_of_add_eq h

/-- Uniform approximation of a zero-mean target may be chosen with the finite
Fourier polynomial's zero mode removed, losing at most a factor two. -/
theorem exists_zeroModeFree_addCircleFourierPolynomial_norm_sub_lt
    {L : ℝ} [Fact (0 < L)]
    (F : C(AddCircle L, ℂ))
    (hF0 : fourierCoeff F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℤ →₀ ℂ,
      c 0 = 0 ∧
      ‖addCircleFourierPolynomial c - F‖ < 2 * δ := by
  obtain ⟨d, hd⟩ :=
    exists_addCircleFourierPolynomial_norm_sub_lt F hδ
  let c : ℤ →₀ ℂ := d.erase 0
  have hc0 : c 0 = 0 := by
    simp [c]
  have hcoeff0 :
      fourierCoeff
          (addCircleFourierPolynomial d - F) 0 = d 0 := by
    rw [fourierCoeff_sub, fourierCoeff_addCircleFourierPolynomial, hF0]
    simp
  have hd0le : ‖d 0‖ ≤ ‖addCircleFourierPolynomial d - F‖ := by
    have h :=
      norm_fourierCoeff_le_norm
        (addCircleFourierPolynomial d - F) 0
    rwa [hcoeff0] at h
  have hd0lt : ‖d 0‖ < δ :=
    lt_of_le_of_lt hd0le hd
  refine ⟨c, hc0, ?_⟩
  rw [show addCircleFourierPolynomial c =
      addCircleFourierPolynomial d - d 0 • fourier 0 by
        simpa [c] using
          addCircleFourierPolynomial_erase_zero (L := L) d]
  calc
    ‖(addCircleFourierPolynomial d - d 0 • fourier 0) - F‖
        = ‖(addCircleFourierPolynomial d - F) -
            d 0 • fourier 0‖ := by
            congr 1
            abel
    _ ≤ ‖addCircleFourierPolynomial d - F‖ +
          ‖d 0 • fourier (T := L) 0‖ :=
      norm_sub_le _ _
    _ = ‖addCircleFourierPolynomial d - F‖ + ‖d 0‖ := by
      rw [norm_smul, fourier_norm]
      simp
    _ < δ + δ := add_lt_add hd hd0lt
    _ = 2 * δ := by ring


/-- The periodic second derivative has zero Fourier coefficient at index zero.
This is the fundamental theorem of calculus plus the strict-collar first-jet
seam condition. -/
theorem periodicSecondDerivMap_fourierCoeff_zero
    {L : ℝ} {h : ℝ → ℂ}
    (hL : 0 < L)
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L) :
    fourierCoeff
      (periodicSecondDerivMap L h hL hh hs) 0 = 0 := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hj := strictSupport_endpoint_jet_package (L := L) (h := h) hs
  have hd : Differentiable ℝ (deriv h) :=
    hh.differentiable_deriv_two
  have hdd : Continuous (deriv (deriv h)) := by
    have hd1 : ContDiff ℝ 1 (deriv h) := by
      simpa using hh.deriv'
    exact hd1.continuous_deriv_one
  have hFTC :
      (∫ x in (0 : ℝ)..L, deriv (deriv h) x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..L, deriv (deriv h) x)
          = deriv h L - deriv h 0 := by
              exact intervalIntegral.integral_deriv_eq_sub
                (fun x _ => (hd x).hasDerivAt)
                (hdd.intervalIntegrable 0 L)
      _ = 0 := by rw [hj.2.2.1, hj.2.2.2.1, sub_self]
  have hOn :
      fourierCoeffOn hL (deriv (deriv h)) 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul]
    rw [hFTC]
    simp
  change fourierCoeff
      (AddCircle.liftIoc L 0 (deriv (deriv h))) 0 = 0
  simpa [fourierCoeffOn] using hOn

/-- A strict-collar C² function has a zero-mode-free finite Fourier polynomial
uniformly approximating its periodic second derivative. -/
theorem exists_zeroModeFree_secondDeriv_fourierPolynomial
    {L : ℝ} {h : ℝ → ℂ}
    (hL : 0 < L)
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℤ →₀ ℂ,
      c 0 = 0 ∧
      ‖addCircleFourierPolynomial c -
          periodicSecondDerivMap L h hL hh hs‖ < 2 * δ := by
  letI : Fact (0 < L) := ⟨hL⟩
  exact exists_zeroModeFree_addCircleFourierPolynomial_norm_sub_lt
    (periodicSecondDerivMap L h hL hh hs)
    (periodicSecondDerivMap_fourierCoeff_zero hL hh hs)
    hδ


/-- A natAbs bound is exactly the pair of centered integer bounds needed by
`centeredIndex`. -/
theorem int_bounds_of_natAbs_le
    {N : ℕ} {n : ℤ}
    (h : Int.natAbs n ≤ N) :
    -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
  have habs : |n| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr h
  exact abs_le.mp habs

/-- Reindex a bounded integer Finsupp sum through the repository's exact
centered `Fin (2*N+1)` coordinates. -/
theorem sum_centeredIndex_eq_finsupp_sum
    {N : ℕ} (c : ℤ →₀ ℂ)
    (hbound : ∀ n ∈ c.support, Int.natAbs n ≤ N)
    (g : ℤ → ℂ) :
    (∑ i : Fin (2 * N + 1),
        c (centeredIndex N i) * g (centeredIndex N i)) =
      c.sum fun n a => a * g n := by
  classical
  let s : Finset (Fin (2 * N + 1)) :=
    Finset.univ.filter fun i => centeredIndex N i ∈ c.support
  calc
    (∑ i : Fin (2 * N + 1),
        c (centeredIndex N i) * g (centeredIndex N i))
        =
      ∑ i ∈ s,
        c (centeredIndex N i) * g (centeredIndex N i) := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i hi hnot
          have hnotmem : centeredIndex N i ∉ c.support := by
            intro hmem
            apply hnot
            simp [s, hmem]
          rw [Finsupp.notMem_support_iff.mp hnotmem, zero_mul]
    _ = ∑ n ∈ c.support, c n * g n := by
          apply Finset.sum_bij
            (fun i _ => centeredIndex N i)
          · intro i hi
            exact (Finset.mem_filter.mp hi).2
          · intro i₁ hi₁ i₂ hi₂ heq
            exact centeredIndex_injective N heq
          · intro n hn
            have hb := int_bounds_of_natAbs_le (hbound n hn)
            obtain ⟨i, hi⟩ :=
              exists_centeredIndex_eq_of_bounds hb.1 hb.2
            refine ⟨i, ?_, hi⟩
            simp [s, hi, hn]
          · intro i hi
            rfl
    _ = c.sum fun n a => a * g n := rfl


/-- Exact normalization bridge from a bounded integer Finsupp polynomial to the
repository's normalized centered finite Fourier function. -/
theorem localizedFiniteFunction_centeredCoefficientsOfFinsupp_eq
    {L : ℝ} (hL : 0 < L)
    {N : ℕ} (c : ℤ →₀ ℂ)
    (hbound : ∀ n ∈ c.support, Int.natAbs n ≤ N)
    (x : ℝ) :
    localizedFiniteFunction L N
        (centeredCoefficientsOfFinsupp L N c) x =
      addCircleFourierPolynomial c (x : AddCircle L) := by
  have hsqrt : Real.sqrt L ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hL
  unfold localizedFiniteFunction centeredCoefficientsOfFinsupp
  calc
    (∑ i : Fin (2 * N + 1),
        (((Real.sqrt L : ℝ) : ℂ) * c (centeredIndex N i)) *
          localizedMode L (centeredIndex N i) x)
        =
      ∑ i : Fin (2 * N + 1),
        c (centeredIndex N i) *
          fourier (centeredIndex N i) (x : AddCircle L) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [localizedMode_eq_addCircle_fourier]
          have hsqrtC : (((Real.sqrt L : ℝ) : ℂ)) ≠ 0 := by
            exact ofReal_ne_zero.mpr hsqrt
          field_simp [hsqrtC]
          ring
    _ =
      c.sum fun n a =>
        a * fourier n (x : AddCircle L) :=
      sum_centeredIndex_eq_finsupp_sum c hbound
        (fun n => fourier n (x : AddCircle L))
    _ = addCircleFourierPolynomial c (x : AddCircle L) := by
      simp [addCircleFourierPolynomial, smul_eq_mul]

/-- Coefficients whose second formula-level jet is a prescribed zero-mode-free
Fourier Finsupp. -/
def localizedTwicePrimitiveCoefficients
    (L : ℝ) (N : ℕ) (c : ℤ →₀ ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i =>
    let n := centeredIndex N i
    if hn : n = 0 then 0
    else
      (((Real.sqrt L : ℝ) : ℂ) * c n) /
        (localizedFrequency L n) ^ 2

/-- The second jet of the twice-primitive coefficients is exactly the requested
zero-mode-free AddCircle polynomial. -/
theorem localizedFiniteSecondJet_twicePrimitive_eq
    {L : ℝ} (hL : 0 < L)
    {N : ℕ} (c : ℤ →₀ ℂ)
    (hc0 : c 0 = 0)
    (hbound : ∀ n ∈ c.support, Int.natAbs n ≤ N)
    (x : ℝ) :
    localizedFiniteSecondJet L N
        (localizedTwicePrimitiveCoefficients L N c) x =
      addCircleFourierPolynomial c (x : AddCircle L) := by
  unfold localizedFiniteSecondJet localizedTwicePrimitiveCoefficients
  calc
    (∑ i : Fin (2 * N + 1),
        (if hn : centeredIndex N i = 0 then 0
          else
            (((Real.sqrt L : ℝ) : ℂ) * c (centeredIndex N i)) /
              localizedFrequency L (centeredIndex N i) ^ 2) *
          localizedFrequency L (centeredIndex N i) ^ 2 *
          localizedMode L (centeredIndex N i) x)
        =
      ∑ i : Fin (2 * N + 1),
        c (centeredIndex N i) *
          fourier (centeredIndex N i) (x : AddCircle L) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hn : centeredIndex N i = 0
          · rw [dif_pos hn, hn, hc0]
            simp
          · rw [dif_neg hn, localizedMode_eq_addCircle_fourier]
            have hfreq : localizedFrequency L (centeredIndex N i) ≠ 0 :=
              localizedFrequency_ne_zero hL hn
            have hsqrt : (((Real.sqrt L : ℝ) : ℂ)) ≠ 0 := by
              exact ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
            field_simp [hfreq, hsqrt]
            ring
    _ =
      c.sum fun n a =>
        a * fourier n (x : AddCircle L) :=
      sum_centeredIndex_eq_finsupp_sum c hbound
        (fun n => fourier n (x : AddCircle L))
    _ = addCircleFourierPolynomial c (x : AddCircle L) := by
      simp [addCircleFourierPolynomial, smul_eq_mul]


/-- Replace only the zero-frequency coefficient so that the finite Fourier
function is anchored to vanish at the left endpoint. -/
def anchorLocalizedCoefficients
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Fin (2 * N + 1) → ℂ :=
  fun i =>
    if i = centeredZeroIndex N then
      -∑ j ∈ Finset.univ.erase (centeredZeroIndex N), u j
    else
      u i

/-- The anchored coefficient vector has total coefficient sum zero. -/
theorem sum_anchorLocalizedCoefficients
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    ∑ i, anchorLocalizedCoefficients N u i = 0 := by
  classical
  let z : Fin (2 * N + 1) := centeredZeroIndex N
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)]
  simp only [anchorLocalizedCoefficients]
  have hz :
      (if z = centeredZeroIndex N then
          -∑ j ∈ Finset.univ.erase (centeredZeroIndex N), u j
        else u z)
        =
      -∑ j ∈ Finset.univ.erase z, u j := by
    simp [z]
  rw [hz]
  have hrest :
      ∑ x ∈ Finset.univ.erase z,
        (if x = centeredZeroIndex N then
            -∑ j ∈ Finset.univ.erase (centeredZeroIndex N), u j
          else u x)
        =
      ∑ x ∈ Finset.univ.erase z, u x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxz : x ≠ z := by
      exact Finset.ne_of_mem_erase hx
    simp [z, hxz]
  rw [hrest]
  abel

/-- Anchoring the zero mode forces the formula-level finite Fourier function
to vanish at the left endpoint. -/
theorem localizedFiniteFunction_anchor_zero
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteFunction L N (anchorLocalizedCoefficients N u) 0 = 0 := by
  unfold localizedFiniteFunction
  simp_rw [localizedMode_zero]
  rw [← Finset.sum_mul]
  rw [sum_anchorLocalizedCoefficients]
  simp

/-- Anchoring changes only the zero-frequency coefficient, hence the first
formula-level jet is unchanged. -/
theorem localizedFiniteFirstJet_anchor
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    localizedFiniteFirstJet L N (anchorLocalizedCoefficients N u) x =
      localizedFiniteFirstJet L N u x := by
  unfold localizedFiniteFirstJet anchorLocalizedCoefficients
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hiz : i = centeredZeroIndex N
  · subst i
    simp
  · simp [hiz]

/-- Anchoring changes only the zero-frequency coefficient, hence the second
formula-level jet is unchanged. -/
theorem localizedFiniteSecondJet_anchor
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) :
    localizedFiniteSecondJet L N (anchorLocalizedCoefficients N u) x =
      localizedFiniteSecondJet L N u x := by
  unfold localizedFiniteSecondJet anchorLocalizedCoefficients
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hiz : i = centeredZeroIndex N
  · subst i
    simp
  · simp [hiz]

/-- The anchored finite Fourier function also vanishes at the right endpoint
by periodicity. -/
theorem localizedFiniteFunction_anchor_right_zero
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteFunction L N (anchorLocalizedCoefficients N u) L = 0 := by
  have hp :=
    localizedFiniteFunction_add_period
      L N (anchorLocalizedCoefficients N u) 0 hL.ne'
  simpa using hp.trans (localizedFiniteFunction_anchor_zero L N u)


/-- On the closed aperture, the periodic second-derivative map agrees with the
ordinary second derivative of the strict-collar function. -/
theorem periodicSecondDerivMap_coe_eq
    {L : ℝ} {h : ℝ → ℂ}
    (hL : 0 < L)
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    periodicSecondDerivMap L h hL hh hs (x : AddCircle L) =
      deriv (deriv h) x := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hj := strictSupport_endpoint_jet_package (L := L) (h := h) hs
  by_cases hx0 : x = 0
  · subst x
    change AddCircle.liftIoc L 0 (deriv (deriv h)) (0 : AddCircle L) =
      deriv (deriv h) 0
    have hcircle : (0 : AddCircle L) = (L : AddCircle L) := by
      simpa using (AddCircle.coe_add_period L (0 : ℝ)).symm
    rw [hcircle]
    rw [AddCircle.liftIoc_zero_coe_apply]
    · rw [hj.2.2.2.2.1, hj.2.2.2.2.2]
    · exact ⟨hL, le_rfl⟩
  · change AddCircle.liftIoc L 0 (deriv (deriv h)) (x : AddCircle L) =
      deriv (deriv h) x
    rw [AddCircle.liftIoc_zero_coe_apply]
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩


/-- A complex-valued function on `[0,L]` with zero integral and derivative
bounded by `η` is uniformly bounded by `2*L*η`. This is a vector-valued
estimate; no scalar intermediate-value or mean-value zero is used. -/
theorem norm_le_two_mul_length_mul_of_integral_eq_zero
    {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    {f f' : ℝ → ℂ}
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc (0 : ℝ) L, ‖f' x‖ ≤ η)
    (hint : (∫ x in (0 : ℝ)..L, f x) = 0) :
    ∀ x ∈ Icc (0 : ℝ) L, ‖f x‖ ≤ 2 * L * η := by
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hosc :
      ∀ x ∈ Icc (0 : ℝ) L, ‖f x - f 0‖ ≤ η * L := by
    intro x hx
    have hmv :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        (a := (0 : ℝ)) (b := L)
        (f := f) (f' := f') (C := η)
        (fun y hy => (hf y).hasDerivWithinAt)
        (fun y hy => hbound y (Ico_subset_Icc_self hy))
        x hx
    have hxL : x ≤ L := hx.2
    have hx0 : 0 ≤ x := hx.1
    calc
      ‖f x - f 0‖ ≤ η * (x - 0) := hmv
      _ = η * x := by ring
      _ ≤ η * L := mul_le_mul_of_nonneg_left hxL hη
  have hfint : IntervalIntegrable f volume 0 L :=
    hcont.intervalIntegrable 0 L
  have hIntSub :
      (∫ t in (0 : ℝ)..L, (f 0 - f t)) = (L : ℝ) • f 0 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfint,
      intervalIntegral.integral_const, hint]
    simp
  have hnormInt :
      ‖(L : ℝ) • f 0‖ ≤ (η * L) * L := by
    rw [← hIntSub]
    have hi :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t : ℝ => f 0 - f t)
        (a := (0 : ℝ)) (b := L)
        (C := η * L)
        (fun t ht => by
          have ht' : t ∈ Icc (0 : ℝ) L := by
            have htIoc : t ∈ Ioc (0 : ℝ) L := by
              simpa [uIoc_of_le hL.le] using ht
            exact ⟨htIoc.1.le, htIoc.2⟩
          simpa [norm_sub_rev] using hosc t ht')
    simpa [abs_of_pos hL] using hi
  have hf0 : ‖f 0‖ ≤ L * η := by
    have hnormsmul :
        ‖(L : ℝ) • f 0‖ = L * ‖f 0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    rw [hnormsmul] at hnormInt
    nlinarith [norm_nonneg (f 0)]
  intro x hx
  calc
    ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
      simpa [sub_add_cancel] using
        norm_add_le (f x - f 0) (f 0)
    _ ≤ η * L + L * η := add_le_add (hosc x hx) hf0
    _ = 2 * L * η := by ring

/-- Uniform second-jet control plus zero endpoint values controls the first-jet
error with a fixed-`L` constant. -/
theorem firstJet_error_norm_le_of_secondJet_error
    {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L)
    (hq0 : localizedFiniteFunction L N u 0 = 0)
    (hqL : localizedFiniteFunction L N u L = 0)
    (hsecond :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteSecondJet L N u x -
            deriv (deriv h) x‖ ≤ η) :
    ∀ x ∈ Icc (0 : ℝ) L,
      ‖localizedFiniteFirstJet L N u x - deriv h x‖ ≤
        2 * L * η := by
  let f : ℝ → ℂ :=
    fun x => localizedFiniteFirstJet L N u x - deriv h x
  let f' : ℝ → ℂ :=
    fun x => localizedFiniteSecondJet L N u x - deriv (deriv h) x
  have hfderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    exact (hasDerivAt_localizedFiniteFirstJet L N u x).sub
      ((hh.differentiable_deriv_two x).hasDerivAt)
  have hfirstInt : (∫ x in (0 : ℝ)..L, f x) = 0 := by
    have hhdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
    have hqcont : Continuous (localizedFiniteFunction L N u) :=
      (contDiff_localizedFiniteFunction L N u).continuous
    have hhcont : Continuous h := hh.continuous
    have hecont :
        Continuous (fun x => localizedFiniteFunction L N u x - h x) :=
      hqcont.sub hhcont
    have hfcont : Continuous f :=
      continuous_iff_continuousAt.mpr fun x => (hfderiv x).continuousAt
    have hFTC :
        (∫ x in (0 : ℝ)..L, f x) =
          (localizedFiniteFunction L N u L - h L) -
            (localizedFiniteFunction L N u 0 - h 0) := by
      exact intervalIntegral.integral_deriv_eq_sub
        (fun x _ =>
          (hasDerivAt_localizedFiniteFunction L N u x).sub
            ((hhdiff x).hasDerivAt))
        (hfcont.intervalIntegrable 0 L)
    have hj := strictSupport_endpoint_jet_package (L := L) (h := h) hs
    rw [hFTC, hqL, hq0, hj.2.1, hj.1]
    simp
  apply norm_le_two_mul_length_mul_of_integral_eq_zero
    hL hη hfderiv
  · intro x hx
    exact hsecond x hx
  · exact hfirstInt

/-- Once the function error is anchored at zero, uniform first-jet control
gives a fixed-`L` uniform function bound. -/
theorem function_error_norm_le_of_firstJet_error
    {L B : ℝ} (hL : 0 < L) (hB : 0 ≤ B)
    {N : ℕ} {u : Fin (2 * N + 1) → ℂ}
    {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h)
    (hq0 : localizedFiniteFunction L N u 0 = h 0)
    (hfirst :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteFirstJet L N u x - deriv h x‖ ≤ B) :
    ∀ x ∈ Icc (0 : ℝ) L,
      ‖localizedFiniteFunction L N u x - h x‖ ≤ L * B := by
  let e : ℝ → ℂ := fun x => localizedFiniteFunction L N u x - h x
  let e' : ℝ → ℂ := fun x => localizedFiniteFirstJet L N u x - deriv h x
  have hhdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hederiv : ∀ x : ℝ, HasDerivAt e (e' x) x := by
    intro x
    exact (hasDerivAt_localizedFiniteFunction L N u x).sub
      ((hhdiff x).hasDerivAt)
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := L)
      (f := e) (f' := e') (C := B)
      (fun x hx => (hederiv x).hasDerivWithinAt)
      (fun x hx => hfirst x (Ico_subset_Icc_self hx))
  intro x hx
  have hxL : x ≤ L := hx.2
  have hx0 : 0 ≤ x := hx.1
  have he0 : e 0 = 0 := by
    simp [e, hq0]
  calc
    ‖localizedFiniteFunction L N u x - h x‖
        = ‖e x - e 0‖ := by simp [e, he0]
    _ ≤ B * (x - 0) := hmv x hx
    _ = B * x := by ring
    _ ≤ B * L := mul_le_mul_of_nonneg_left hxL hB
    _ = L * B := by ring


/-- **F0-B1C-A headline theorem.** Every C² function supported strictly inside
a positive aperture admits a centered finite Fourier formula that vanishes at
the left endpoint and approximates the function and its first two jets
uniformly on the closed aperture.

This is a formula-level periodic approximation theorem only. It does not claim
that the raw hard-window zero extension is globally C². -/
theorem exists_localizedFinite_uniform_C2_approx
    {L : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h)
    (hs : tsupport h ⊆ Ioo 0 L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ u : Fin (2 * N + 1) → ℂ,
        localizedFiniteFunction L N u 0 = 0 ∧
        (∀ x ∈ Icc (0 : ℝ) L,
          ‖localizedFiniteFunction L N u x - h x‖ < ε) ∧
        (∀ x ∈ Icc (0 : ℝ) L,
          ‖localizedFiniteFirstJet L N u x - deriv h x‖ < ε) ∧
        (∀ x ∈ Icc (0 : ℝ) L,
          ‖localizedFiniteSecondJet L N u x -
              deriv (deriv h) x‖ < ε) := by
  let δ : ℝ :=
    min (ε / 4)
      (min (ε / (8 * L)) (ε / (8 * L ^ 2)))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · positivity
    · apply lt_min <;> positivity
  have hδ0 : δ ≤ ε / 4 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ1 : δ ≤ ε / (8 * L) := by
    dsimp [δ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ ε / (8 * L ^ 2) := by
    dsimp [δ]
    exact (min_le_right _ _).trans (min_le_right _ _)
  letI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨c, hc0, hcapprox⟩ :=
    exists_zeroModeFree_secondDeriv_fourierPolynomial
      hL hh hs hδ
  obtain ⟨N, hN, hbound⟩ :=
    exists_support_natAbs_bound c
  let u0 : Fin (2 * N + 1) → ℂ :=
    localizedTwicePrimitiveCoefficients L N c
  let u : Fin (2 * N + 1) → ℂ :=
    anchorLocalizedCoefficients N u0
  have hq0 : localizedFiniteFunction L N u 0 = 0 := by
    simpa [u] using localizedFiniteFunction_anchor_zero L N u0
  have hqL : localizedFiniteFunction L N u L = 0 := by
    simpa [u] using
      localizedFiniteFunction_anchor_right_zero hL N u0
  have hj := strictSupport_endpoint_jet_package (L := L) (h := h) hs
  have hsecond_lt :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteSecondJet L N u x -
            deriv (deriv h) x‖ < 2 * δ := by
    intro x hx
    have hpoint :=
      ContinuousMap.norm_coe_le_norm
        (addCircleFourierPolynomial c -
          periodicSecondDerivMap L h hL hh hs)
        (x : AddCircle L)
    have hpoly :
        localizedFiniteSecondJet L N u x =
          addCircleFourierPolynomial c (x : AddCircle L) := by
      rw [show localizedFiniteSecondJet L N u x =
          localizedFiniteSecondJet L N u0 x by
            simpa [u] using
              localizedFiniteSecondJet_anchor L N u0 x]
      simpa [u0] using
        localizedFiniteSecondJet_twicePrimitive_eq
          hL c hc0 hbound x
    have htarget :
        periodicSecondDerivMap L h hL hh hs (x : AddCircle L) =
          deriv (deriv h) x :=
      periodicSecondDerivMap_coe_eq hL hh hs hx
    rw [hpoly, ← htarget]
    exact lt_of_le_of_lt
      (by
        simpa using hpoint)
      hcapprox
  have hsecond_le :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteSecondJet L N u x -
            deriv (deriv h) x‖ ≤ 2 * δ :=
    fun x hx => (hsecond_lt x hx).le
  have hfirst_le :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteFirstJet L N u x - deriv h x‖ ≤
          2 * L * (2 * δ) :=
    firstJet_error_norm_le_of_secondJet_error
      hL (mul_nonneg (by norm_num) hδ.le)
      hh hs hq0 hqL hsecond_le
  have hfunc_le :
      ∀ x ∈ Icc (0 : ℝ) L,
        ‖localizedFiniteFunction L N u x - h x‖ ≤
          L * (2 * L * (2 * δ)) := by
    apply function_error_norm_le_of_firstJet_error
      hL (by positivity) hh
    · rw [hq0, hj.1]
    · exact hfirst_le
  have hsecond_budget : 2 * δ < ε := by
    calc
      2 * δ ≤ 2 * (ε / 4) :=
        mul_le_mul_of_nonneg_left hδ0 (by norm_num)
      _ = ε / 2 := by ring
      _ < ε := by linarith
  have hfirst_budget : 2 * L * (2 * δ) < ε := by
    calc
      2 * L * (2 * δ)
          ≤ 2 * L * (2 * (ε / (8 * L))) := by
            gcongr
      _ = ε / 2 := by
            field_simp [hL.ne']
            ring
      _ < ε := by linarith
  have hfunc_budget : L * (2 * L * (2 * δ)) < ε := by
    calc
      L * (2 * L * (2 * δ))
          ≤ L * (2 * L * (2 * (ε / (8 * L ^ 2)))) := by
            gcongr
      _ = ε / 2 := by
            field_simp [hL.ne']
            ring
      _ < ε := by linarith
  refine ⟨N, hN, u, hq0, ?_, ?_, ?_⟩
  · intro x hx
    exact lt_of_le_of_lt (hfunc_le x hx) hfunc_budget
  · intro x hx
    exact lt_of_le_of_lt (hfirst_le x hx) hfirst_budget
  · intro x hx
    exact lt_of_lt_of_le (hsecond_lt x hx) hsecond_budget.le

end Zeta23.CCM
