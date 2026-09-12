import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.DictionaryPoleLift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace Zeta23.CCM

open Matrix MeasureTheory Set
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

/-- Source entries are smooth in the source coordinate. -/
@[fun_prop] theorem contDiff_sourceEntry
    (n m : ℤ) :
    ContDiff ℝ ⊤ (fun ω : ℝ => sourceEntry ω n m) := by
  by_cases hnm : n = m
  · subst m
    simp only [sourceEntry_self]
    unfold sourceDiagonal
    fun_prop
  · have heq :
        (fun ω : ℝ => sourceEntry ω n m) =
          fun ω =>
            (sourcePotential ω n - sourcePotential ω m) /
              (((n - m : ℤ) : ℂ)) := by
      funext ω
      exact sourceEntry_of_ne ω hnm
    rw [heq]
    unfold sourcePotential
    fun_prop

/-- The elementary source-atom real energy is `C^∞`.  This is intentionally
stronger than FB-02 needs so FB-03 can reuse the same smoothness spine for its
higher derivatives. -/
theorem contDiff_sourceAtomRealEnergy
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) := by
  unfold sourceAtomRealEnergy matrixRealEnergy quadraticForm
  simp only [sourceMatrix_apply]
  fun_prop

/-- Local public-facing expansion of the deterministic pole functional into
its two physical exponential weights.  This repeats only the generic Fourier
bookkeeping already used by `DictionaryPoleSource`; it does not re-integrate
the closed `poleComponent` formula. -/
private theorem dictionaryPoleRHS_eq_spatial_weights_fb02
    {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    dictionaryPoleRHS k =
      (∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)) +
        ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ) := by
  have hA_int : Integrable (fun u : ℝ => k u * (Real.exp (-|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB_int : Integrable (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI1 : Integrable (fun u : ℝ => k u * Complex.exp (I * (I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI2 : Integrable (fun u : ℝ => k u * Complex.exp (I * (-I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  unfold dictionaryPoleRHS
  rw [← integral_add hA_int hB_int]
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def, ← integral_add hI1 hI2]
  congr 1
  ext u
  rw [← mul_add, ← mul_add]
  congr 1
  have ha : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hb : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
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
  have hk : Continuous k := by
    have heq : k = fun y =>
        (1 / 2 : ℂ) * sourceEntry (dictionaryApertureCoord L y) n m := by
      funext y
      exact dictionaryBasisTest_eq_sourceEntry_clamped hL n m y
    rw [heq]
    fun_prop
  have hkc : HasCompactSupport k := by
    refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
    intro y hy
    by_contra hzero
    exact hy (dictionaryBasisTest_support_subset n m hzero)
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
  have hGcont : Continuous G := by
    dsimp [G, k]
    fun_prop
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
  have hGint := hGcont.intervalIntegrable (0 : ℝ) L
  rw [← intervalIntegral.integral_add hGint hGint]
  apply intervalIntegral.integral_congr
  intro y hy
  have hyIcc : y ∈ Icc (0 : ℝ) L := by
    simpa [uIcc_of_le hL.le] using hy
  have hyabs : |y| ≤ L := by
    rw [abs_of_nonneg hyIcc.1]
    exact hyIcc.2
  have hweights :
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
  dsimp [G, k]
  rw [dictionaryBasisTest_eq_sourceEntry_clamped hL n m y,
    dictionaryApertureCoord_eq_one_sub_of_abs_le hL hyabs,
    abs_of_nonneg hyIcc.1, hweights]
  ring

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

end Zeta23.CCM

#print axioms Zeta23.CCM.contDiff_sourceAtomRealEnergy
#print axioms Zeta23.CCM.dictionaryPoleRHS_basis_eq_sourceEntry_integral