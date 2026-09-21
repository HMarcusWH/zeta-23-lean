import Mathlib.Analysis.Complex.Norm

noncomputable section

namespace Zeta23.CCM

open Complex
open scoped ComplexConjugate

/-!
# Complex disk / half-plane compatibility

This file contains the denominator-free geometric lemma used by the retained
cross-parity composition layer.

If a complex point `z` lies in a squared-radius disk around `center` and
also satisfies a weighted real half-plane constraint, then either the disk
center already satisfies that half-plane or the squared projection gap is
bounded by the weight norm times the squared disk radius.

No division, phase choice, square root, or nonzero hypothesis is used.
-/

/-- If a disk center misses a weighted half-plane, the squared miss is bounded
by the disk radius in that weighted direction. -/
theorem complexDisk_halfPlane_gap_sq_le
    {z center weight : ℂ}
    {radiusSq floor : ℝ}
    (hdisk : ‖center - z‖ ^ 2 ≤ radiusSq)
    (hhalf : floor ≤ Complex.re (star weight * z))
    (hcenter : Complex.re (star weight * center) < floor) :
    (floor - Complex.re (star weight * center)) ^ 2 ≤
      Complex.normSq weight * radiusSq := by
  let d : ℂ := z - center
  let gap : ℝ := floor - Complex.re (star weight * center)
  have hgap : 0 < gap := by
    simpa [gap] using sub_pos.mpr hcenter
  have hproj :
      gap ≤ Complex.re (star weight * d) := by
    have hdecomp :
        star weight * z =
          star weight * center + star weight * (z - center) := by
      ring
    rw [hdecomp, Complex.add_re] at hhalf
    dsimp [gap, d]
    linarith
  have hprojNonneg :
      0 ≤ Complex.re (star weight * d) :=
    le_trans (le_of_lt hgap) hproj
  have hgapSq :
      gap ^ 2 ≤ (Complex.re (star weight * d)) ^ 2 := by
    nlinarith
  have hrealSq :
      (Complex.re (star weight * d)) ^ 2 ≤
        ‖star weight * d‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (Complex.im (star weight * d))]
  have hnormProd :
      ‖star weight * d‖ ^ 2 =
        Complex.normSq weight * ‖d‖ ^ 2 := by
    rw [Complex.norm_mul, norm_star, Complex.normSq_eq_norm_sq]
    ring
  have hdisk' : ‖d‖ ^ 2 ≤ radiusSq := by
    have hneg :
        center - z = -(z - center) := by ring
    rw [hneg, norm_neg]
    simpa [d] using hdisk
  have hmul :
      Complex.normSq weight * ‖d‖ ^ 2 ≤
        Complex.normSq weight * radiusSq :=
    mul_le_mul_of_nonneg_left hdisk' (Complex.normSq_nonneg weight)
  calc
    (floor - Complex.re (star weight * center)) ^ 2 = gap ^ 2 := by rfl
    _ ≤ (Complex.re (star weight * d)) ^ 2 := hgapSq
    _ ≤ ‖star weight * d‖ ^ 2 := hrealSq
    _ = Complex.normSq weight * ‖d‖ ^ 2 := hnormProd
    _ ≤ Complex.normSq weight * radiusSq := hmul

/-- Disk/half-plane support dichotomy: either the center lies in the half-plane,
or the squared weighted gap is paid for by the disk radius. -/
theorem complexDisk_halfPlane_support_dichotomy
    {z center weight : ℂ}
    {radiusSq floor : ℝ}
    (hdisk : ‖center - z‖ ^ 2 ≤ radiusSq)
    (hhalf : floor ≤ Complex.re (star weight * z)) :
    floor ≤ Complex.re (star weight * center) ∨
      (floor - Complex.re (star weight * center)) ^ 2 ≤
        Complex.normSq weight * radiusSq := by
  by_cases hcenter :
      floor ≤ Complex.re (star weight * center)
  · exact Or.inl hcenter
  · exact Or.inr
      (complexDisk_halfPlane_gap_sq_le
        hdisk hhalf (lt_of_not_ge hcenter))

end Zeta23.CCM

#print axioms Zeta23.CCM.complexDisk_halfPlane_gap_sq_le
#print axioms Zeta23.CCM.complexDisk_halfPlane_support_dichotomy
