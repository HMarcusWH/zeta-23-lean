import Zeta23.OPICARound4.SignedSpectral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators

noncomputable section
namespace Zeta23.OPICARound4
open scoped BigOperators ComplexConjugate

/-- The real part of a cross spectral coefficient. No positive-residue premise
or unsupported assertion that its complex precursor is real is imposed. -/
def realCrossResidue {ι : Type*} [Fintype ι]
    (z g : EuclideanSpace ℂ ι) (i : ι) : ℝ := (g i * star (z i)).re

theorem realCrossResidue_sum {ι : Type*} [Fintype ι]
    (z g : EuclideanSpace ℂ ι) :
    (∑ i, realCrossResidue z g i) = (inner ℂ z g).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [realCrossResidue, dotProduct, Complex.re_sum, Pi.star_apply]

/-- Total variation of the real cross residues costs both physical vector
norms. Complex scaling is therefore charged on both slots. -/
theorem realCrossResidue_variation_le {ι : Type*} [Fintype ι]
    (z g : EuclideanSpace ℂ ι) :
    (∑ i, |realCrossResidue z g i|) ≤ ‖z‖ * ‖g‖ := by
  calc
    _ ≤ ∑ i, ‖z i‖ * ‖g i‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h := Complex.abs_re_le_norm (g i * star (z i))
      simpa only [realCrossResidue, norm_mul, norm_star, mul_comm] using h
    _ ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) * Real.sqrt (∑ i, ‖g i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = _ := by rw [← EuclideanSpace.norm_eq, ← EuclideanSpace.norm_eq]

/-- Diagonal resolvent in arbitrary finite orthonormal spectral coordinates.
Repeated eigenvalues are retained and no gap-independent norm is installed. -/
def diagonalSpectralResolvent {ι : Type*} [Fintype ι]
    (mu : ι → ℝ) (lam : ℝ) (g : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => ((mu i - lam)⁻¹ : ℝ) • g i)

theorem diagonal_resolvent_response {ι : Type*} [Fintype ι]
    (mu : ι → ℝ) (lam : ℝ) (z g : EuclideanSpace ℂ ι) :
    (inner ℂ z (diagonalSpectralResolvent mu lam g)).re =
      signedSpectralResponse mu (realCrossResidue z g) lam := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [diagonalSpectralResolvent, dotProduct, WithLp.ofLp_toLp,
    Complex.re_sum, signedSpectralResponse, realCrossResidue, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- S05's improved signed bound in finite orthonormal spectral coordinates.
This controls the real response one-sidedly; it never asserts smallness of the
right side and never replaces the physical D by a unitary. -/
theorem diagonal_signed_norm_upper {ι : Type*} [Fintype ι]
    (mu : ι → ℝ) (b lam : ℝ) (z g : EuclideanSpace ℂ ι)
    (hbottom : ∀ i, b ≤ mu i) (hlam : lam < b) :
    (b - lam) * (inner ℂ z (diagonalSpectralResolvent mu lam g)).re ≤
      (‖z‖ * ‖g‖ + (inner ℂ z g).re) / 2 := by
  rw [diagonal_resolvent_response]
  have hs := signed_resolvent_upper mu (realCrossResidue z g) b lam hbottom hlam
  rw [realCrossResidue_sum] at hs
  have hv := realCrossResidue_variation_le z g
  linarith

end Zeta23.OPICARound4
