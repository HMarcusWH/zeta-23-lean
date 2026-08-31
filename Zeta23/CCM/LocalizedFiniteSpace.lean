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

/-- Negating the real coordinate conjugates a normalized localized Fourier mode. -/
@[simp] theorem localizedMode_neg
    (L : ℝ) (n : ℤ) (x : ℝ) :
    localizedMode L n (-x) = conj (localizedMode L n x) := by
  simp only [localizedMode, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Real part of a normalized localized Fourier mode. -/
@[simp] theorem localizedMode_re
    (L : ℝ) (n : ℤ) (x : ℝ) :
    (localizedMode L n x).re =
      (1 / Real.sqrt L) *
        Real.cos (2 * Real.pi * (n : ℝ) * x / L) := by
  unfold localizedMode
  have hphase :
      Complex.I * (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)) =
        (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)) * Complex.I := by
    ring
  rw [hphase, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.exp_ofReal_mul_I_re]

/-- Imaginary part of a normalized localized Fourier mode. -/
@[simp] theorem localizedMode_im
    (L : ℝ) (n : ℤ) (x : ℝ) :
    (localizedMode L n x).im =
      (1 / Real.sqrt L) *
        Real.sin (2 * Real.pi * (n : ℝ) * x / L) := by
  unfold localizedMode
  have hphase :
      Complex.I * (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)) =
        (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)) * Complex.I := by
    ring
  rw [hphase, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.exp_ofReal_mul_I_im]

/-- Each normalized localized mode is continuous on the ambient real line. -/
@[fun_prop] theorem continuous_localizedMode
    (L : ℝ) (n : ℤ) :
    Continuous (localizedMode L n) := by
  unfold localizedMode
  fun_prop

/-- The real part of one shifted basis overlap is the cosine integrand used by
G0-A.  The apparent sign is removed by cosine evenness. -/
theorem localizedMode_overlap_re
    (n m : ℤ) {L y x : ℝ} (hL : 0 < L) :
    (localizedMode L m (x + y) * conj (localizedMode L n x)).re =
      (1 / L) *
        Real.cos
          (2 * Real.pi *
            ((((n - m : ℤ) : ℝ) * x - (m : ℝ) * y) / L)) := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    localizedMode_re, localizedMode_im]
  let a : ℝ := 1 / Real.sqrt L
  let A : ℝ := 2 * Real.pi * (m : ℝ) * (x + y) / L
  let B : ℝ := 2 * Real.pi * (n : ℝ) * x / L
  change
    (a * Real.cos A) * (a * Real.cos B) -
        (a * Real.sin A) * (-(a * Real.sin B)) =
      (1 / L) *
        Real.cos
          (2 * Real.pi *
            ((((n - m : ℤ) : ℝ) * x - (m : ℝ) * y) / L))
  rw [show
      (a * Real.cos A) * (a * Real.cos B) -
          (a * Real.sin A) * (-(a * Real.sin B)) =
        (a * a) *
          (Real.cos A * Real.cos B + Real.sin A * Real.sin B) by ring]
  rw [← Real.cos_sub]
  have hscale : a * a = 1 / L := by
    dsimp [a]
    rw [one_div_mul_one_div, ← pow_two, Real.sq_sqrt hL.le]
  rw [hscale]
  have hphase :
      A - B =
        -(2 * Real.pi *
          ((((n - m : ℤ) : ℝ) * x - (m : ℝ) * y) / L)) := by
    dsimp [A, B]
    field_simp [hL.ne'] <;> push_cast <;> ring
  rw [hphase, Real.cos_neg]

/-- Symmetrizing one shifted overlap produces the real hard-window cosine
integrand with the production normalization. -/
theorem localizedMode_symmetrized_product_eq
    (n m : ℤ) {L y x : ℝ} (hL : 0 < L) :
    localizedMode L m (x + y) * conj (localizedMode L n x) +
        conj (localizedMode L m (x + y)) * localizedMode L n x =
      (((2 / L) *
        Real.cos
          (2 * Real.pi *
            ((((n - m : ℤ) : ℝ) * x - (m : ℝ) * y) / L)) : ℝ) : ℂ) := by
  have hconj :
      conj (localizedMode L m (x + y) * conj (localizedMode L n x)) =
        conj (localizedMode L m (x + y)) * localizedMode L n x := by
    simp
  rw [← hconj, Complex.add_conj, localizedMode_overlap_re n m hL]
  push_cast
  ring

/-- Integer Fourier modes are periodic with the source interval length.
The positivity/source-validity hypothesis used downstream supplies the required
nonzero denominator. -/
theorem localizedMode_add_period
    (L : ℝ) (n : ℤ) (x : ℝ) (hL : L ≠ 0) :
    localizedMode L n (x + L) = localizedMode L n x := by
  unfold localizedMode
  congr 1
  have hphase :
      Complex.I * (((2 * Real.pi * (n : ℝ) * (x + L) / L : ℝ) : ℂ)) =
        Complex.I * (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)) +
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [hL] <;> ring
  rw [hphase, Complex.exp_add]
  have hperiod :
      Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa using Complex.exp_int_mul_two_pi_mul_I n
  rw [hperiod, mul_one]

/-- Reflection across the overlap interval turns the negative-shift basis
integrand into the conjugate of the positive-shift integrand.  This is the
periodicity step that makes the source symmetrization real. -/
theorem localizedMode_reflection_product
    (n m : ℤ) {L y x : ℝ} (hL : 0 < L) :
    localizedMode L m (L - y - x) *
        conj (localizedMode L n (L - x)) =
      conj (localizedMode L m (x + y)) * localizedMode L n x := by
  have hm :
      localizedMode L m (L - y - x) =
        conj (localizedMode L m (x + y)) := by
    calc
      localizedMode L m (L - y - x) =
          localizedMode L m (-(x + y) + L) := by
            congr 2 <;> ring
      _ = localizedMode L m (-(x + y)) := by
            simpa [add_comm] using
              localizedMode_add_period L m (-(x + y)) hL.ne'
      _ = conj (localizedMode L m (x + y)) :=
            localizedMode_neg L m (x + y)
  have hn :
      localizedMode L n (L - x) = conj (localizedMode L n x) := by
    calc
      localizedMode L n (L - x) =
          localizedMode L n (-x + L) := by
            congr 2 <;> ring
      _ = localizedMode L n (-x) := by
            simpa [add_comm] using localizedMode_add_period L n (-x) hL.ne'
      _ = conj (localizedMode L n x) := localizedMode_neg L n x
  rw [hm, hn, conj_conj]

/-- The finite vector is exactly the indicator of the formula-level finite Fourier
combination introduced in G0-A.  This is the main representation firewall between
the global character formula and the actual source-supported function. -/
theorem localizedFiniteVector_eq_indicator
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    localizedFiniteVector L N u =
      (Icc (0 : ℝ) L).indicator (localizedFiniteFunction L N u) := by
  ext x
  by_cases hx : x ∈ Icc (0 : ℝ) L
  · simp [localizedFiniteVector, localizedZeroExtendedMode, localizedFiniteFunction, hx]
  · simp [localizedFiniteVector, localizedZeroExtendedMode, hx]

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
  let B : ℝ := max C 0
  have hbound : ∀ᵐ x : ℝ ∂volume, ‖localizedFiniteVector L N u x‖ ≤ B := by
    filter_upwards with x
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · rw [localizedFiniteVector_eq_indicator, Set.indicator_of_mem hx]
      exact (hC x hx).trans (le_max_left C 0)
    · rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hx]
      exact norm_zero.trans_le (le_max_right C 0)
  exact (localizedFiniteVector_hasCompactSupport L N u).memLp_of_bound hmeas B hbound

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

/-- For a nonnegative shift inside the aperture, the actual inherited Weil
convolution of two zero-extended basis modes is the overlap integral on
`[0,L-y]`. -/
theorem weilTest_localizedZeroExtendedMode_pos
    (n m : ℤ) {L y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    Zeta23.EF.weilTest
        (localizedZeroExtendedMode L m)
        (localizedZeroExtendedMode L n) y =
      ∫ x in 0..(L - y),
        localizedMode L m (x + y) * conj (localizedMode L n x) := by
  simp only [Zeta23.EF.weilTest, convolution_def,
    ContinuousLinearMap.mul_apply', Zeta23.EF.tilde]
  have hfun :
      (fun t : ℝ =>
        localizedZeroExtendedMode L m t *
          conj (localizedZeroExtendedMode L n (-(y - t)))) =
        (Icc y L).indicator
          (fun t : ℝ =>
            localizedMode L m t * conj (localizedMode L n (t - y))) := by
    funext t
    have harg : -(y - t) = t - y := by ring
    rw [harg]
    by_cases ht : t ∈ Icc y L
    · have ht0 : t ∈ Icc (0 : ℝ) L := ⟨hy0.trans ht.1, ht.2⟩
      have hty : t - y ∈ Icc (0 : ℝ) L := by
        constructor
        · exact sub_nonneg.mpr ht.1
        · linarith [ht.2, hy0]
      simp [localizedZeroExtendedMode, ht, ht0, hty]
    · by_cases ht0 : t ∈ Icc (0 : ℝ) L
      · have hlt : t < y := by
          by_contra h
          exact ht ⟨le_of_not_gt h, ht0.2⟩
        have hty : t - y ∉ Icc (0 : ℝ) L := by
          intro hmem
          exact (not_lt_of_ge hmem.1) (sub_neg.mpr hlt)
        simp [localizedZeroExtendedMode, ht, ht0, hty]
      · simp [localizedZeroExtendedMode, ht, ht0]
  rw [hfun, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyL]
  have hshift :=
    intervalIntegral.integral_comp_add_right
      (f := fun t : ℝ =>
        localizedMode L m t * conj (localizedMode L n (t - y)))
      (a := 0) (b := L - y) y
  simpa using hshift.symm

/-- The negative shift has the complementary overlap orientation on the same
interval `[0,L-y]`. -/
theorem weilTest_localizedZeroExtendedMode_neg
    (n m : ℤ) {L y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    Zeta23.EF.weilTest
        (localizedZeroExtendedMode L m)
        (localizedZeroExtendedMode L n) (-y) =
      ∫ x in 0..(L - y),
        localizedMode L m x * conj (localizedMode L n (x + y)) := by
  simp only [Zeta23.EF.weilTest, convolution_def,
    ContinuousLinearMap.mul_apply', Zeta23.EF.tilde]
  have hLy0 : 0 ≤ L - y := sub_nonneg.mpr hyL
  have hfun :
      (fun t : ℝ =>
        localizedZeroExtendedMode L m t *
          conj (localizedZeroExtendedMode L n (-((-y) - t)))) =
        (Icc (0 : ℝ) (L - y)).indicator
          (fun t : ℝ =>
            localizedMode L m t * conj (localizedMode L n (t + y))) := by
    funext t
    have harg : -((-y) - t) = t + y := by ring
    rw [harg]
    by_cases ht : t ∈ Icc (0 : ℝ) (L - y)
    · have ht0 : t ∈ Icc (0 : ℝ) L := by
        constructor
        · exact ht.1
        · linarith [ht.2, hy0]
      have hty : t + y ∈ Icc (0 : ℝ) L := by
        constructor
        · linarith [ht.1, hy0]
        · linarith [ht.2]
      simp [localizedZeroExtendedMode, ht, ht0, hty]
    · by_cases ht0 : t ∈ Icc (0 : ℝ) L
      · have hgt : L - y < t := by
          by_contra h
          exact ht ⟨ht0.1, le_of_not_gt h⟩
        have hty : t + y ∉ Icc (0 : ℝ) L := by
          intro hmem
          linarith [hmem.2]
        simp [localizedZeroExtendedMode, ht, ht0, hty]
      · simp [localizedZeroExtendedMode, ht, ht0]
  rw [hfun, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLy0]

/-- Reflection on the finite overlap interval identifies the negative-shift
basis overlap with the conjugate positive-shift integrand. -/
theorem localizedNegativeOverlap_eq_reflected
    (n m : ℤ) {L y : ℝ} (hL : 0 < L) :
    (∫ x in 0..(L - y),
        localizedMode L m x * conj (localizedMode L n (x + y))) =
      ∫ x in 0..(L - y),
        conj (localizedMode L m (x + y)) * localizedMode L n x := by
  have hcomp :=
    intervalIntegral.integral_comp_sub_left
      (f := fun t : ℝ =>
        localizedMode L m t * conj (localizedMode L n (t + y)))
      (a := 0) (b := L - y) (d := L - y)
  calc
    (∫ x in 0..(L - y),
        localizedMode L m x * conj (localizedMode L n (x + y))) =
      ∫ x in 0..(L - y),
        localizedMode L m ((L - y) - x) *
          conj (localizedMode L n (((L - y) - x) + y)) := by
            simpa using hcomp.symm
    _ = ∫ x in 0..(L - y),
        conj (localizedMode L m (x + y)) * localizedMode L n x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change
        localizedMode L m (L - y - x) *
            conj (localizedMode L n (L - y - x + y)) =
          conj (localizedMode L m (x + y)) * localizedMode L n x
      have harg : L - y - x + y = L - x := by ring
      rw [harg]
      exact localizedMode_reflection_product n m (L := L) (y := y) (x := x) hL

/-- The actual source symmetrized convolution of two zero-extended localized
basis modes is exactly the hard-window correlation computed in G0-A. -/
theorem localizedWeilCorrelation_basis_eq_hardWindow
    (n m : ℤ) {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    localizedWeilCorrelation
        (localizedZeroExtendedMode L n)
        (localizedZeroExtendedMode L m) y =
      (hardWindowCharacterCorrelation n m y L : ℂ) := by
  rw [localizedWeilCorrelation,
    weilTest_localizedZeroExtendedMode_pos n m hy0 hyL,
    weilTest_localizedZeroExtendedMode_neg n m hy0 hyL,
    localizedNegativeOverlap_eq_reflected n m hL]
  have hpos : IntervalIntegrable
      (fun x : ℝ =>
        localizedMode L m (x + y) * conj (localizedMode L n x))
      volume 0 (L - y) :=
    (by fun_prop : Continuous
      (fun x : ℝ =>
        localizedMode L m (x + y) * conj (localizedMode L n x))).intervalIntegrable _ _
  have href : IntervalIntegrable
      (fun x : ℝ =>
        conj (localizedMode L m (x + y)) * localizedMode L n x)
      volume 0 (L - y) :=
    (by fun_prop : Continuous
      (fun x : ℝ =>
        conj (localizedMode L m (x + y)) * localizedMode L n x)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hpos href]
  simp_rw [localizedMode_symmetrized_product_eq n m hL]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  rw [hardWindowCharacterCorrelation, intervalIntegral.integral_const_mul]

/-- The G0-B basis theorem: the actual inherited `EF.weilTest` correlation is
the theorem-authoritative CCM `qBasis` entry, not merely a formula-level
surrogate. -/
theorem localizedWeilCorrelation_basis_eq_qBasis
    (n m : ℤ) {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    localizedWeilCorrelation
        (localizedZeroExtendedMode L n)
        (localizedZeroExtendedMode L m) y =
      (qBasis n m y L : ℂ) := by
  rw [localizedWeilCorrelation_basis_eq_hardWindow n m hL hy0 hyL,
    hardWindowCharacterCorrelation_eq_qBasis n m hL hy0 hyL]

end Zeta23.CCM

#print axioms Zeta23.CCM.localizedFiniteVector_eq_indicator
#print axioms Zeta23.CCM.localizedFiniteVector_support_subset
#print axioms Zeta23.CCM.localizedFiniteVector_hasCompactSupport
#print axioms Zeta23.CCM.localizedFiniteVector_memLp_two
#print axioms Zeta23.CCM.localizedWeilCorrelation_neg
