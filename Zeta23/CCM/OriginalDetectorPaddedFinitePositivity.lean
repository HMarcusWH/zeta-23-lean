import Zeta23.CCM.OriginalDetectorPaddedFiniteWindowImageJets
import Zeta23.CCM.OriginalDetectorPositiveFourierPaddingReal

/-! Exact realness, primitive positivity and cancellation of odd DC padding. -/

noncomputable section

open Set Complex
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

theorem originalDetectorPaddedFiniteWindow_eq_real (L x : ℝ) :
    originalDetectorPaddedFiniteWindow L x = (Real.sin (Real.pi * x / L) ^ 8 : ℝ) := by
  unfold originalDetectorPaddedFiniteWindow
  push_cast
  rfl

theorem originalDetectorPaddedFiniteWindow_reflected {L : ℝ} (hL : 0 < L) (x : ℝ) :
    originalDetectorPaddedFiniteWindow L (L - x) = originalDetectorPaddedFiniteWindow L x := by
  rw [originalDetectorPaddedFiniteWindow_eq_real, originalDetectorPaddedFiniteWindow_eq_real]
  have he : Real.pi * (L - x) / L = Real.pi - Real.pi * x / L := by field_simp <;> ring
  rw [he, Real.sin_pi_sub]

theorem originalDetectorPaddedFiniteWindowImage_real
    (s L c : ℝ) (hL : 0 < L) (x : ℝ) :
    conj (originalDetectorPaddedFiniteWindowImage s L c hL x) =
      originalDetectorPaddedFiniteWindowImage s L c hL x := by
  simp only [originalDetectorPaddedFiniteWindowImage, map_mul,
    originalDetectorPaddedFiniteWindow_eq_real, Complex.conj_ofReal,
    originalDetectorPaddedRawFourierPartialSum_real]

theorem originalDetectorPaddedFiniteWindowImage_re_nonneg
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ (originalDetectorPaddedFiniteWindowImage s L c (by linarith) x).re := by
  rw [originalDetectorPaddedFiniteWindowImage, originalDetectorPaddedFiniteWindow_eq_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity)
    (originalDetectorPaddedRawFourierPartialSum_re_nonneg hs hL hleft hright hx)

def originalDetectorPaddedFinitePhasePrimitive (σ s L c : ℝ) (hL : 0 < L) (x : ℝ) : ℂ :=
  originalDetectorPaddedFiniteWindowImage s L c hL x +
    (σ : ℂ) * originalDetectorPaddedFiniteWindowImage s L c hL (L - x)

theorem originalDetectorPaddedFiniteEvenPrimitive_re_nonneg
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ (originalDetectorPaddedFinitePhasePrimitive 1 s L c (by linarith) x).re := by
  have hx' : L - x ∈ Icc (0 : ℝ) L := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simp only [originalDetectorPaddedFinitePhasePrimitive, Complex.ofReal_one, one_mul,
    Complex.add_re]
  exact add_nonneg (originalDetectorPaddedFiniteWindowImage_re_nonneg hs hL hleft hright hx)
    (originalDetectorPaddedFiniteWindowImage_re_nonneg hs hL hleft hright hx')

theorem originalDetectorPaddedFiniteWindowImage_eq_unpadded_add
    (s L c : ℝ) (hL : 0 < L) (x : ℝ) :
    originalDetectorPaddedFiniteWindowImage s L c hL x =
      originalDetectorFiniteWindowImage s L c hL x +
        (originalDetectorPositivePadding s L : ℂ) * originalDetectorFiniteWindow L x := by
  unfold originalDetectorPaddedFiniteWindowImage originalDetectorFiniteWindowImage
  rw [originalDetectorPaddedRawFourierPartialJet_eq]
  simp only [if_true]
  change originalDetectorFiniteWindow L x * (_ + _) = _
  ring

theorem originalDetectorPaddedFiniteOddPrimitive_padding_cancels
    (s L c : ℝ) (hL : 0 < L) (x : ℝ) :
    originalDetectorPaddedFinitePhasePrimitive (-1) s L c hL x =
      originalDetectorFiniteWindowImage s L c hL x -
        originalDetectorFiniteWindowImage s L c hL (L - x) := by
  unfold originalDetectorPaddedFinitePhasePrimitive
  rw [originalDetectorPaddedFiniteWindowImage_eq_unpadded_add,
    originalDetectorPaddedFiniteWindowImage_eq_unpadded_add]
  have hw : originalDetectorFiniteWindow L (L - x) = originalDetectorFiniteWindow L x :=
    originalDetectorPaddedFiniteWindow_reflected hL x
  rw [hw]
  push_cast
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImage_real
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImage_re_nonneg
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteEvenPrimitive_re_nonneg
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteOddPrimitive_padding_cancels
