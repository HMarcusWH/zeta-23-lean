import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.DictionaryPoleLift
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace Zeta23.CCM

open Complex Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB02: canonical pole-prime discrepancy

This module rewrites the exact production pole/prime cancellation in a form
adapted to the regular first-bad state retained by FB-01.  The elementary
source matrix is reused directly; no parallel energy framework is introduced.

The endpoint source atom vanishes at `ω = 0`.  The source-atom energy is smooth
in its source coordinate, which permits one integration by parts on the pole
channel and an ordinary finite fundamental-theorem rewrite on the truncated
prime channel.  The final object is the finite cumulative pole-prime
discrepancy tested against the derivative of the exact source-atom energy.

No high-order boundary-flat jet, Riesz smoothing, discrepancy sign, positivity,
negative-root exclusion, finite-to-infinite closure, or RH theorem is claimed
here.
-/

/-- Existing matrix real energy specialized to one elementary source atom. -/
def sourceAtomRealEnergy
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) : ℝ :=
  matrixRealEnergy (sourceMatrix ω K) x

@[simp] theorem sourceAtomRealEnergy_zero
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceAtomRealEnergy K x 0 = 0 := by
  simp [sourceAtomRealEnergy]

private theorem contDiff_ofReal_comp
    {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x : ℝ => (f x : ℂ)) := by
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff.comp hf)

private theorem contDiff_re_comp
    {f : ℝ → ℂ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x : ℝ => Complex.re (f x)) := by
  simpa only [Function.comp_apply, Complex.reCLM_apply] using
    (Complex.reCLM.contDiff.comp hf)

private theorem contDiff_sourcePotential_fb02 (n : ℤ) :
    ContDiff ℝ ⊤ (fun ω : ℝ => sourcePotential ω n) := by
  unfold sourcePotential
  apply contDiff_ofReal_comp
  fun_prop

private theorem contDiff_sourceDiagonal_fb02 (n : ℤ) :
    ContDiff ℝ ⊤ (fun ω : ℝ => sourceDiagonal ω n) := by
  unfold sourceDiagonal
  apply contDiff_ofReal_comp
  fun_prop

/-- Source entries are smooth in the source coordinate. -/
@[fun_prop] theorem contDiff_sourceEntry
    (n m : ℤ) :
    ContDiff ℝ ⊤ (fun ω : ℝ => sourceEntry ω n m) := by
  by_cases hnm : n = m
  · subst m
    simpa only [sourceEntry_self] using contDiff_sourceDiagonal_fb02 n
  · have heq :
        (fun ω : ℝ => sourceEntry ω n m) =
          fun ω =>
            (sourcePotential ω n - sourcePotential ω m) /
              (((n - m : ℤ) : ℂ)) := by
      funext ω
      exact sourceEntry_of_ne ω hnm
    rw [heq]
    exact ((contDiff_sourcePotential_fb02 n).sub
      (contDiff_sourcePotential_fb02 m)).div_const _

/-- The elementary source-atom real energy is `C^∞`.  This is intentionally
stronger than FB-02 needs so FB-03 can reuse the same smoothness spine for its
higher derivatives. -/
@[fun_prop] theorem contDiff_sourceAtomRealEnergy
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) := by
  have hq : ContDiff ℝ ⊤
      (fun ω : ℝ => quadraticForm (sourceMatrix ω K)
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
    unfold quadraticForm
    simp only [sourceMatrix_apply]
    fun_prop
  unfold sourceAtomRealEnergy matrixRealEnergy
  exact contDiff_re_comp hq

/-- Local expansion of the deterministic pole functional into its two physical
exponential weights.  This repeats only generic Fourier bookkeeping already
used by `DictionaryPoleSource`; it does not re-integrate `poleComponent`. -/
private theorem dictionaryPoleRHS_eq_spatial_weights_fb02
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    dictionaryPoleRHS k =
      (∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)) +
        ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ) := by
  have hA_int : Integrable (fun u : ℝ => k u * (Real.exp (-|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB_int : Integrable (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI1 : Integrable
      (fun u : ℝ => k u * Complex.exp (Complex.I * (Complex.I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI2 : Integrable
      (fun u : ℝ => k u * Complex.exp (Complex.I * (-Complex.I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  unfold dictionaryPoleRHS
  rw [← integral_add hA_int hB_int]
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, ← integral_add hI1 hI2]
  congr 1
  ext u
  rw [← mul_add, ← mul_add]
  congr 1
  have ha :
      Complex.I * (Complex.I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hb :
      Complex.I * (-Complex.I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [ha, hb, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 1
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu, neg_div]
  · rw [abs_of_nonpos hu, neg_neg, add_comm, neg_div]

private theorem intervalIntegral_eq_integral_of_support_subset_Icc_fb02
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (h : Function.support f ⊆ Icc a b) :
    (∫ x in a..b, f x) = ∫ x : ℝ, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc, indicator_eq_self.2 h]

private theorem poleWeightSum_eq_twoCosh (y : ℝ) :
    (Real.exp (-y / 2) : ℂ) + (Real.exp (y / 2) : ℂ) =
      ((2 * Real.cosh (y / 2) : ℝ) : ℂ) := by
  have hcomplex := Complex.two_cosh ((y : ℂ) / 2)
  have hcoshC :
      (((2 * Real.cosh (y / 2) : ℝ)) : ℂ) =
        (((Real.exp (y / 2) + Real.exp (-y / 2) : ℝ)) : ℂ) := by
    push_cast
    convert hcomplex using 1
    all_goals ring
  rw [← Complex.ofReal_add]
  convert hcoshC.symm using 1
  ring

/-- The already-proved dictionary pole channel is exactly the source-atom
integral needed by FB-02.  The factor `2*cosh(t/2)` is forced by the two pole
weights together with the production `1/2` in `dictionaryBasisTest`. -/
theorem dictionaryPoleRHS_basis_eq_sourceEntry_integral
    {L : ℝ} (hL : 0 < L)
    (n m : ℤ) :
    dictionaryPoleRHS (dictionaryBasisTest n m L) =
      ∫ t in (0 : ℝ)..L,
        ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
          sourceEntry (1 - t / L) n m := by
  let k := dictionaryBasisTest n m L
  let G : ℝ → ℂ := fun y =>
    k y *
      ((Real.exp (-|y| / 2) : ℂ) + (Real.exp (|y| / 2) : ℂ))
  have hk : Continuous k := continuous_dictionaryBasisTest hL n m
  have hkc : HasCompactSupport k := dictionaryBasisTest_hasCompactSupport n m
  rw [dictionaryPoleRHS_eq_spatial_weights_fb02 hk hkc]
  have hA : Integrable
      (fun y : ℝ => k y * (Real.exp (-|y| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB : Integrable
      (fun y : ℝ => k y * (Real.exp (|y| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  rw [← integral_add hA hB]
  simp_rw [← mul_add]
  change (∫ y : ℝ, G y) = _
  have hGsupp : Function.support G ⊆ Icc (-L) L := by
    intro y hy
    apply dictionaryBasisTest_support_subset n m
    intro hzero
    apply hy
    simp [G, k, hzero]
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc_fb02
    (by linarith : -L ≤ L) hGsupp]
  have hweight : Continuous (fun y : ℝ =>
      (Real.exp (-|y| / 2) : ℂ) + (Real.exp (|y| / 2) : ℂ)) := by
    fun_prop
  have hGcont : Continuous G := by
    dsimp only [G]
    exact hk.mul hweight
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hGcont.intervalIntegrable (-L) 0) (hGcont.intervalIntegrable 0 L)
  rw [← hsplit]
  have hGneg : ∀ y : ℝ, G (-y) = G y := by
    intro y
    simp [G, k, dictionaryBasisTest_neg]
  have hleft : (∫ y in -L..(0 : ℝ), G y) = ∫ y in (0 : ℝ)..L, G y := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) G
    have h2 : (∫ y in (0 : ℝ)..L, G (-y)) = ∫ y in (0 : ℝ)..L, G y := by
      apply intervalIntegral.integral_congr
      intro y _
      exact hGneg y
    rw [← h2, h1]
    norm_num
  rw [hleft]
  have hGint : IntervalIntegrable G volume (0 : ℝ) L :=
    hGcont.intervalIntegrable 0 L
  calc
    (∫ y in (0 : ℝ)..L, G y) + ∫ y in (0 : ℝ)..L, G y =
        ∫ y in (0 : ℝ)..L, (G y + G y) := by
          exact (intervalIntegral.integral_add hGint hGint).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyIcc : y ∈ Icc (0 : ℝ) L := by
        simpa [uIcc_of_le hL.le] using hy
      have hyabs : |y| ≤ L := by
        rw [abs_of_nonneg hyIcc.1]
        exact hyIcc.2
      dsimp [G, k]
      rw [dictionaryBasisTest_eq_sourceEntry_clamped hL n m y,
        dictionaryApertureCoord_eq_one_sub_of_abs_le hL hyabs,
        abs_of_nonneg hyIcc.1, poleWeightSum_eq_twoCosh]
      ring

/-- Entrywise form of the pole/source integral bridge. -/
theorem canonicalPoleMatrix_apply_eq_sourceEntry_integral
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (i j : Fin (2 * K + 1)) :
    canonicalPoleMatrix L K i j =
      ∫ t in (0 : ℝ)..L,
        ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
          sourceEntry (1 - t / L)
            (centeredIndex K i) (centeredIndex K j) := by
  calc
    canonicalPoleMatrix L K i j =
        ((poleComponent (centeredIndex K i) (centeredIndex K j) L : ℝ) : ℂ) := rfl
    _ = dictionaryPoleRHS
          (dictionaryBasisTest (centeredIndex K i) (centeredIndex K j) L) :=
        (dictionaryPoleRHS_basis hL (centeredIndex K i) (centeredIndex K j)).symm
    _ = _ := dictionaryPoleRHS_basis_eq_sourceEntry_integral
      hL (centeredIndex K i) (centeredIndex K j)

/-- Full finite dictionary version of the same pole/source integral.  This is
used to lift directly to matrix energy without redoing a double finite-sum
interchange. -/
private theorem dictionaryPoleRHS_dictionaryTest_eq_sourceContract_integral
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPoleRHS (dictionaryTest K u L) =
      ∫ t in (0 : ℝ)..L,
        ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
          sourceContract K u (1 - t / L) := by
  let k := dictionaryTest K u L
  let G : ℝ → ℂ := fun y =>
    k y *
      ((Real.exp (-|y| / 2) : ℂ) + (Real.exp (|y| / 2) : ℂ))
  have hk : Continuous k := continuous_dictionaryTest K u hL
  have hkc : HasCompactSupport k := dictionaryTest_hasCompactSupport K u L
  rw [dictionaryPoleRHS_eq_spatial_weights_fb02 hk hkc]
  have hA : Integrable
      (fun y : ℝ => k y * (Real.exp (-|y| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB : Integrable
      (fun y : ℝ => k y * (Real.exp (|y| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  rw [← integral_add hA hB]
  simp_rw [← mul_add]
  change (∫ y : ℝ, G y) = _
  have hGsupp : Function.support G ⊆ Icc (-L) L := by
    intro y hy
    apply dictionaryTest_support_subset K u L
    intro hzero
    apply hy
    simp [G, k, hzero]
  rw [← intervalIntegral_eq_integral_of_support_subset_Icc_fb02
    (by linarith : -L ≤ L) hGsupp]
  have hweight : Continuous (fun y : ℝ =>
      (Real.exp (-|y| / 2) : ℂ) + (Real.exp (|y| / 2) : ℂ)) := by
    fun_prop
  have hGcont : Continuous G := by
    dsimp only [G]
    exact hk.mul hweight
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hGcont.intervalIntegrable (-L) 0) (hGcont.intervalIntegrable 0 L)
  rw [← hsplit]
  have hGneg : ∀ y : ℝ, G (-y) = G y := by
    intro y
    simp [G, k, dictionaryTest_neg]
  have hleft : (∫ y in -L..(0 : ℝ), G y) = ∫ y in (0 : ℝ)..L, G y := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) G
    have h2 : (∫ y in (0 : ℝ)..L, G (-y)) = ∫ y in (0 : ℝ)..L, G y := by
      apply intervalIntegral.integral_congr
      intro y _
      exact hGneg y
    rw [← h2, h1]
    norm_num
  rw [hleft]
  have hGint : IntervalIntegrable G volume (0 : ℝ) L :=
    hGcont.intervalIntegrable 0 L
  calc
    (∫ y in (0 : ℝ)..L, G y) + ∫ y in (0 : ℝ)..L, G y =
        ∫ y in (0 : ℝ)..L, (G y + G y) := by
          exact (intervalIntegral.integral_add hGint hGint).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyIcc : y ∈ Icc (0 : ℝ) L := by
        simpa [uIcc_of_le hL.le] using hy
      have hyabs : |y| ≤ L := by
        rw [abs_of_nonneg hyIcc.1]
        exact hyIcc.2
      dsimp [G, k]
      rw [dictionaryTest_eq_clamped K u hL y,
        dictionaryApertureCoord_eq_one_sub_of_abs_le hL hyabs,
        abs_of_nonneg hyIcc.1, poleWeightSum_eq_twoCosh]
      unfold dictionaryKernel
      ring

private theorem quadraticForm_canonicalPoleMatrix_eq_sourceContract_integral
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    quadraticForm (canonicalPoleMatrix L K) u =
      ∫ t in (0 : ℝ)..L,
        ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
          sourceContract K u (1 - t / L) := by
  have hpole := dictionaryPoleRHS_dictionaryTest K u hL
  have hint := dictionaryPoleRHS_dictionaryTest_eq_sourceContract_integral K u hL
  unfold quadraticForm canonicalPoleMatrix
  rw [← hpole]
  exact hint

private theorem re_intervalIntegral_eq_intervalIntegral_re
    {a b : ℝ} {f : ℝ → ℂ} (hf : Continuous f) :
    Complex.re (∫ t in a..b, f t) =
      ∫ t in a..b, Complex.re (f t) := by
  have hint : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  exact (intervalIntegral.intervalIntegral_re hint).symm

/-- Exact pole energy as the continuous source-atom integral. -/
theorem matrixRealEnergy_canonicalPoleMatrix_eq_integral_sourceAtom
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPoleMatrix L K) x =
      ∫ t in (0 : ℝ)..L,
        2 * Real.cosh (t / 2) *
          sourceAtomRealEnergy K x (1 - t / L) := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  have hcomplex :=
    quadraticForm_canonicalPoleMatrix_eq_sourceContract_integral hL K u
  have hcont : Continuous (fun t : ℝ =>
      ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
        sourceContract K u (1 - t / L)) := by
    fun_prop
  have hre := congrArg Complex.re hcomplex
  rw [re_intervalIntegral_eq_intervalIntegral_re hcont] at hre
  have hreal :
      (fun t : ℝ => Complex.re
        (((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
          sourceContract K u (1 - t / L))) =
      fun t => 2 * Real.cosh (t / 2) *
        sourceAtomRealEnergy K x (1 - t / L) := by
    funext t
    unfold sourceAtomRealEnergy matrixRealEnergy sourceContract
    dsimp [u]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hreal] at hre
  exact hre

/-- Finite cumulative von-Mangoldt staircase on the same aperture horizon as
`canonicalPrimeMatrix`. -/
def canonicalPrimeCumulativeWeight (L t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    if Real.log q ≤ t then
      Λ q / Real.sqrt q
    else
      0

/-- Primitive whose derivative is the production pole density
`2 * cosh(t/2)`. -/
def canonicalPoleCumulativeWeight (t : ℝ) : ℝ :=
  4 * Real.sinh (t / 2)

private theorem hasDerivAt_canonicalPoleCumulativeWeight (t : ℝ) :
    HasDerivAt canonicalPoleCumulativeWeight
      (2 * Real.cosh (t / 2)) t := by
  have hinner : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hsinh := (Real.hasDerivAt_sinh (t / 2)).comp t hinner
  have h := hsinh.const_mul 4
  have hcoef :
      4 * (Real.cosh (t / 2) * (1 / 2)) =
        2 * Real.cosh (t / 2) := by
    ring
  simpa only [canonicalPoleCumulativeWeight, hcoef] using h

private theorem hasDerivAt_sourceAtom_composed
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => sourceAtomRealEnergy K x (1 - s / L))
      (-(1 / L) * deriv (sourceAtomRealEnergy K x) (1 - t / L)) t := by
  have hsmooth : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
    contDiff_sourceAtomRealEnergy K x
  have hdiff : Differentiable ℝ (sourceAtomRealEnergy K x) :=
    hsmooth.differentiable (by simp)
  have hinner : HasDerivAt (fun s : ℝ => 1 - s / L) (-(1 / L)) t := by
    simpa only [zero_sub] using
      (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const L)
  have hcomp := (hdiff (1 - t / L)).hasDerivAt.comp t hinner
  simpa only [mul_comm] using hcomp

/-- One integration by parts replaces the pole density by its cumulative
primitive. -/
theorem matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPoleMatrix L K) x =
      (1 / L) *
        ∫ t in (0 : ℝ)..L,
          canonicalPoleCumulativeWeight t *
            deriv (sourceAtomRealEnergy K x) (1 - t / L) := by
  rw [matrixRealEnergy_canonicalPoleMatrix_eq_integral_sourceAtom hL K x]
  let g : ℝ → ℝ := fun t => sourceAtomRealEnergy K x (1 - t / L)
  let gp : ℝ → ℝ := fun t =>
    -(1 / L) * deriv (sourceAtomRealEnergy K x) (1 - t / L)
  let A := canonicalPoleCumulativeWeight
  let Ap : ℝ → ℝ := fun t => 2 * Real.cosh (t / 2)
  have hg : ∀ t ∈ [[(0 : ℝ), L]], HasDerivAt g (gp t) t := by
    intro t ht
    exact hasDerivAt_sourceAtom_composed hL K x t
  have hA : ∀ t ∈ [[(0 : ℝ), L]], HasDerivAt A (Ap t) t := by
    intro t ht
    exact hasDerivAt_canonicalPoleCumulativeWeight t
  have hDcont : Continuous (deriv (sourceAtomRealEnergy K x)) := by
    have hsmooth : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
      contDiff_sourceAtomRealEnergy K x
    exact hsmooth.continuous_deriv (by simp)
  have hgpcont : Continuous gp := by
    dsimp [gp]
    fun_prop
  have hApcont : Continuous Ap := by
    dsimp [Ap]
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hg hA (hgpcont.intervalIntegrable 0 L) (hApcont.intervalIntegrable 0 L)
  have hLend : g L = 0 := by
    dsimp [g]
    rw [div_self hL.ne']
    simp
  have hA0 : A 0 = 0 := by simp [A, canonicalPoleCumulativeWeight]
  have hleft :
      (∫ t in (0 : ℝ)..L, 2 * Real.cosh (t / 2) *
        sourceAtomRealEnergy K x (1 - t / L)) =
      ∫ t in (0 : ℝ)..L, g t * Ap t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [g, Ap]
    ring
  have hgpA :
      (∫ t in (0 : ℝ)..L, gp t * A t) =
        -(1 / L) *
          ∫ t in (0 : ℝ)..L,
            A t * deriv (sourceAtomRealEnergy K x) (1 - t / L) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [gp]
    ring
  rw [hleft, hparts, hLend, hA0, hgpA]
  ring

private theorem sourceAtom_value_eq_deriv_integral
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {a : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L) :
    sourceAtomRealEnergy K x (1 - a / L) =
      (1 / L) *
        ∫ t in a..L,
          deriv (sourceAtomRealEnergy K x) (1 - t / L) := by
  let F : ℝ → ℝ := fun t =>
    -L * sourceAtomRealEnergy K x (1 - t / L)
  let D : ℝ → ℝ := fun t =>
    deriv (sourceAtomRealEnergy K x) (1 - t / L)
  have hF : ∀ t ∈ [[a, L]], HasDerivAt F (D t) t := by
    intro t ht
    have hc := hasDerivAt_sourceAtom_composed hL K x t
    have hs := hc.const_mul (-L)
    have hcoef : (-L) * (-(1 / L)) = (1 : ℝ) := by
      field_simp [hL.ne']
    dsimp [F, D]
    simpa only [← mul_assoc, hcoef, one_mul] using hs
  have hDcont : Continuous D := by
    have hsmooth : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
      contDiff_sourceAtomRealEnergy K x
    have hd := hsmooth.continuous_deriv (by simp)
    dsimp [D]
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := D) hF (hDcont.intervalIntegrable a L)
  calc
    sourceAtomRealEnergy K x (1 - a / L) =
        (1 / L) * (L * sourceAtomRealEnergy K x (1 - a / L)) := by
          field_simp [hL.ne']
    _ = (1 / L) * (F L - F a) := by
          congr 1
          dsimp [F]
          rw [div_self hL.ne']
          simp
    _ = (1 / L) * ∫ t in a..L, D t := by rw [hftc]
    _ = _ := rfl

private theorem prime_log_mem_aperture
    {L : ℝ} {q : ℕ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    0 ≤ Real.log q ∧ Real.log q ≤ L := by
  have hqmem := Finset.mem_Icc.mp hq
  have hqposNat : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have hqexp : (q : ℝ) ≤ Real.exp L :=
    (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
  exact ⟨Real.log_natCast_nonneg q,
    (by rw [← Real.log_exp L]; exact Real.log_le_log hqpos hqexp)⟩

private theorem intervalIntegrable_step_mul_continuous
    {a L c : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L)
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable
      (fun t : ℝ => (if a ≤ t then c else 0) * f t) volume 0 L := by
  let h : ℝ → ℝ := fun t => (if a ≤ t then c else 0) * f t
  have hleft : IntervalIntegrable h volume 0 a := by
    have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a :=
      continuous_const.intervalIntegrable 0 a
    apply hz.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) a := by
      simpa [uIoo_of_le ha0] using ht
    simp [h, not_le.mpr ht'.2]
  have hright : IntervalIntegrable h volume a L := by
    have hc : Continuous (fun t : ℝ => c * f t) := continuous_const.mul hf
    have hi : IntervalIntegrable (fun t : ℝ => c * f t) volume a L :=
      hc.intervalIntegrable a L
    apply hi.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo a L := by
      simpa [uIoo_of_le haL] using ht
    simp [h, le_of_lt ht'.1]
  exact hleft.trans hright

private theorem intervalIntegral_step_mul_continuous
    {a L c : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L)
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in (0 : ℝ)..L, (if a ≤ t then c else 0) * f t) =
      c * ∫ t in a..L, f t := by
  let h : ℝ → ℝ := fun t => (if a ≤ t then c else 0) * f t
  have hleft : IntervalIntegrable h volume 0 a := by
    have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a :=
      continuous_const.intervalIntegrable 0 a
    apply hz.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) a := by
      simpa [uIoo_of_le ha0] using ht
    simp [h, not_le.mpr ht'.2]
  have hright : IntervalIntegrable h volume a L := by
    have hc : Continuous (fun t : ℝ => c * f t) := continuous_const.mul hf
    have hi : IntervalIntegrable (fun t : ℝ => c * f t) volume a L :=
      hc.intervalIntegrable a L
    apply hi.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo a L := by
      simpa [uIoo_of_le haL] using ht
    simp [h, le_of_lt ht'.1]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) hleft hright
  rw [← hsplit]
  have hz : (∫ t in (0 : ℝ)..a, h t) = 0 := by
    calc
      (∫ t in (0 : ℝ)..a, h t) = ∫ t in (0 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        have ht' : t ∈ Ioo (0 : ℝ) a := by
          simpa [uIoo_of_le ha0] using ht
        simp [h, not_le.mpr ht'.2]
      _ = 0 := by simp
  have hr : (∫ t in a..L, h t) = ∫ t in a..L, c * f t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo a L := by
      simpa [uIoo_of_le haL] using ht
    simp [h, le_of_lt ht'.1]
  rw [hz, hr, zero_add, intervalIntegral.integral_const_mul]

/-- The existing finite prime energy is the derivative integral against the
same finite cumulative staircase. -/
theorem matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPrimeMatrix L K) x =
      (1 / L) *
        ∫ t in (0 : ℝ)..L,
          canonicalPrimeCumulativeWeight L t *
            deriv (sourceAtomRealEnergy K x) (1 - t / L) := by
  rw [matrixRealEnergy_canonicalPrimeMatrix_eq_sum_sourceMatrix]
  let D : ℝ → ℝ := fun t =>
    deriv (sourceAtomRealEnergy K x) (1 - t / L)
  have hDcont : Continuous D := by
    have hsmooth : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
      contDiff_sourceAtomRealEnergy K x
    have hd := hsmooth.continuous_deriv (by simp)
    dsimp [D]
    fun_prop
  have hcum :
      (∫ t in (0 : ℝ)..L,
        canonicalPrimeCumulativeWeight L t * D t) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        (Λ q / Real.sqrt q : ℝ) * ∫ t in Real.log q..L, D t := by
    unfold canonicalPrimeCumulativeWeight
    have hfun :
        (fun t : ℝ =>
          (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
            if Real.log q ≤ t then Λ q / Real.sqrt q else 0) * D t) =
        fun t =>
          ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
            (if Real.log q ≤ t then (Λ q / Real.sqrt q : ℝ) else 0) * D t := by
      funext t
      rw [Finset.sum_mul]
    rw [hfun]
    rw [intervalIntegral.integral_finsetSum (fun q hq => by
      obtain ⟨hlog0, hlogL⟩ := prime_log_mem_aperture hq
      exact intervalIntegrable_step_mul_continuous hlog0 hlogL hDcont)]
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hlog0, hlogL⟩ := prime_log_mem_aperture hq
    exact intervalIntegral_step_mul_continuous hlog0 hlogL hDcont
  change
    (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (Λ q / Real.sqrt q : ℝ) *
        sourceAtomRealEnergy K x (primeSourceCoordinate q L)) =
      (1 / L) *
        ∫ t in (0 : ℝ)..L, canonicalPrimeCumulativeWeight L t * D t
  rw [hcum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hlog0, hlogL⟩ := prime_log_mem_aperture hq
  unfold primeSourceCoordinate
  rw [sourceAtom_value_eq_deriv_integral hL K x hlog0 hlogL]
  ring

/-- Cancellation-preserving finite pole-prime discrepancy. -/
def canonicalPolePrimeDiscrepancy (L t : ℝ) : ℝ :=
  canonicalPoleCumulativeWeight t - canonicalPrimeCumulativeWeight L t

/-- FB-02 arithmetic normal form before the remaining archimedean channels are
subtracted. -/
def canonicalPolePrimeDiscrepancyEnergy
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / L) *
    ∫ t in (0 : ℝ)..L,
      canonicalPolePrimeDiscrepancy L t *
        deriv (sourceAtomRealEnergy K x) (1 - t / L)

/-- Headline FB-02 identity: the individually large pole and prime energies are
replaced by their finite cumulative discrepancy, with no infinite interchange. -/
theorem matrixRealEnergy_pole_sub_prime_eq_discrepancy
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPoleMatrix L K) x -
        matrixRealEnergy (canonicalPrimeMatrix L K) x =
      canonicalPolePrimeDiscrepancyEnergy L K x := by
  rw [matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral hL K x,
    matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral hL K x]
  let D : ℝ → ℝ := fun t =>
    deriv (sourceAtomRealEnergy K x) (1 - t / L)
  have hDcont : Continuous D := by
    have hsmooth : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
      contDiff_sourceAtomRealEnergy K x
    have hd := hsmooth.continuous_deriv (by simp)
    dsimp [D]
    fun_prop
  have hpoleInt : IntervalIntegrable
      (fun t : ℝ => canonicalPoleCumulativeWeight t * D t) volume 0 L := by
    have hAcont : Continuous canonicalPoleCumulativeWeight := by
      unfold canonicalPoleCumulativeWeight
      fun_prop
    exact (hAcont.mul hDcont).intervalIntegrable 0 L
  have hprimeInt : IntervalIntegrable
      (fun t : ℝ => canonicalPrimeCumulativeWeight L t * D t) volume 0 L := by
    unfold canonicalPrimeCumulativeWeight
    have hfun :
        (fun t : ℝ =>
          (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
            if Real.log q ≤ t then Λ q / Real.sqrt q else 0) * D t) =
        fun t =>
          ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
            (if Real.log q ≤ t then (Λ q / Real.sqrt q : ℝ) else 0) * D t := by
      funext t
      rw [Finset.sum_mul]
    rw [hfun]
    have hsum : IntervalIntegrable
        (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          fun t : ℝ =>
            (if Real.log q ≤ t then (Λ q / Real.sqrt q : ℝ) else 0) * D t)
        volume 0 L := by
      apply IntervalIntegrable.sum
      intro q hq
      obtain ⟨hlog0, hlogL⟩ := prime_log_mem_aperture hq
      exact intervalIntegrable_step_mul_continuous hlog0 hlogL hDcont
    have hsum_fun :
        (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          fun t : ℝ =>
            (if Real.log q ≤ t then (Λ q / Real.sqrt q : ℝ) else 0) * D t) =
        (fun t : ℝ =>
          ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
            (if Real.log q ≤ t then (Λ q / Real.sqrt q : ℝ) else 0) * D t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [← hsum_fun]
    exact hsum
  have hdisc :
      (∫ t in (0 : ℝ)..L,
        canonicalPolePrimeDiscrepancy L t * D t) =
      (∫ t in (0 : ℝ)..L, canonicalPoleCumulativeWeight t * D t) -
        ∫ t in (0 : ℝ)..L, canonicalPrimeCumulativeWeight L t * D t := by
    unfold canonicalPolePrimeDiscrepancy
    calc
      (∫ t in (0 : ℝ)..L,
        (canonicalPoleCumulativeWeight t - canonicalPrimeCumulativeWeight L t) * D t) =
          ∫ t in (0 : ℝ)..L,
            canonicalPoleCumulativeWeight t * D t -
              canonicalPrimeCumulativeWeight L t * D t := by
                apply intervalIntegral.integral_congr
                intro t ht
                ring
      _ = _ := intervalIntegral.integral_sub hpoleInt hprimeInt
  change
    (1 / L) *
        (∫ t in (0 : ℝ)..L, canonicalPoleCumulativeWeight t * D t) -
      (1 / L) *
        (∫ t in (0 : ℝ)..L, canonicalPrimeCumulativeWeight L t * D t) = _
  unfold canonicalPolePrimeDiscrepancyEnergy
  change _ =
    (1 / L) *
      ∫ t in (0 : ℝ)..L, canonicalPolePrimeDiscrepancy L t * D t
  rw [hdisc]
  ring

/-- Exact production-channel normal form after pole/prime cancellation.  The
only remaining explicit channels are the reduced archimedean diagonal,
off-diagonal, and scalar correction. -/
theorem canonicalSourceChannelEnergy_eq_discrepancy
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalSourceChannelEnergy L K x =
      canonicalPolePrimeDiscrepancyEnergy L K x
        - matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x
        - matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x
        - canonicalArchScalarCorrection L * ‖x‖ ^ 2 := by
  calc
    canonicalSourceChannelEnergy L K x =
        (matrixRealEnergy (canonicalPoleMatrix L K) x -
          matrixRealEnergy (canonicalPrimeMatrix L K) x)
          - matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x
          - matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x
          - canonicalArchScalarCorrection L * ‖x‖ ^ 2 := by
            unfold canonicalSourceChannelEnergy
            rw [matrixRealEnergy_canonicalPrimeMatrix_eq_sum_sourceMatrix L K x]
            ring
    _ = _ := by
      rw [matrixRealEnergy_pole_sub_prime_eq_discrepancy hL K x]

end Zeta23.CCM

#print axioms Zeta23.CCM.contDiff_sourceAtomRealEnergy
#print axioms Zeta23.CCM.dictionaryPoleRHS_basis_eq_sourceEntry_integral
#print axioms Zeta23.CCM.matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral
#print axioms Zeta23.CCM.matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral
#print axioms Zeta23.CCM.matrixRealEnergy_pole_sub_prime_eq_discrepancy
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_eq_discrepancy
