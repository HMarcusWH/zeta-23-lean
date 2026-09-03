import Zeta23.CCM.ParityBadness
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-SPECTRUM: parity-constrained spectral compression

This module builds the exact orthogonal compression of the canonical finite
CCM operator to one Euclidean parity-constrained sector. It proves that the
compression has the same self-quadratic form as the ambient canonical matrix,
is symmetric, and turns ParityBad into a genuine negative eigenmode.

It also theorem-locks the successor-level form of predecessor nonnegativity:
the nonnegative predecessor form from a least bad size is transported by the
exact #100 N-flow into the embedded predecessor subspace of the successor
matrix before any spectral argument is made.

No compressed N-flow intertwining, shell invariance, KKT equation, Schur
formula, positivity theorem, finite-to-infinite theorem, or RH theorem is
claimed.
-/

@[simp] theorem mem_euclideanParityBoundaryFlatSubspace_iff
    (p : ReversalParity) (N : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * N + 1))) :
    x ∈ euclideanParityBoundaryFlatSubspace p N ↔
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x ∈
        parityBoundaryFlatSubspace p N := by
  cases p <;> rfl

def parityCompressedCanonicalCLM
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →L[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  let V := euclideanParityBoundaryFlatSubspace p N
  V.orthogonalProjectionOnto.comp
    ((LinearMap.toContinuousLinearMap
        (canonicalSourceMatrix L N).toEuclideanLin).comp V.subtypeL)

def parityCompressedCanonical
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    euclideanParityBoundaryFlatSubspace p N →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p N :=
  (parityCompressedCanonicalCLM p L N).toLinearMap

@[simp] theorem parityCompressedCanonical_apply
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    parityCompressedCanonical p L N x =
      (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((canonicalSourceMatrix L N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) := rfl

theorem inner_parityCompressedCanonical_self
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    inner ℂ (parityCompressedCanonical p L N x) x =
      inner ℂ
        ((canonicalSourceMatrix L N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1))))
        (x : EuclideanSpace ℂ (Fin (2 * N + 1))) := by
  change
    inner ℂ
      ((euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((canonicalSourceMatrix L N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1))))) x =
    inner ℂ
      ((canonicalSourceMatrix L N).toEuclideanLin
        (x : EuclideanSpace ℂ (Fin (2 * N + 1))))
      (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
  exact
    inner_orthogonalProjectionOnto_eq_of_mem_right
      (K := euclideanParityBoundaryFlatSubspace p N) x _

theorem re_inner_parityCompressedCanonical_self
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    Complex.re (inner ℂ (parityCompressedCanonical p L N x) x) =
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin
            (x : EuclideanSpace ℂ (Fin (2 * N + 1))))
          (x : EuclideanSpace ℂ (Fin (2 * N + 1)))) := by
  exact congrArg Complex.re
    (inner_parityCompressedCanonical_self p L N x)

theorem parityCompressedCanonical_isSymmetric
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    (parityCompressedCanonical p L N).IsSymmetric := by
  intro x y
  change
    inner ℂ
      ((euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((canonicalSourceMatrix L N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1))))) y =
    inner ℂ x
      ((euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((canonicalSourceMatrix L N).toEuclideanLin
          (y : EuclideanSpace ℂ (Fin (2 * N + 1)))))
  rw [
    inner_orthogonalProjectionOnto_eq_of_mem_right,
    inner_orthogonalProjectionOnto_eq_of_mem_left
  ]
  exact canonicalSourceMatrix_toEuclideanLin_isSymmetric L N
    (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
    (y : EuclideanSpace ℂ (Fin (2 * N + 1)))

theorem exists_negative_compressed_direction_of_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hbad : ParityBad p L N) :
    ∃ x : euclideanParityBoundaryFlatSubspace p N,
      x ≠ 0 ∧
      Complex.re
        (inner ℂ (parityCompressedCanonical p L N x) x) < 0 := by
  obtain ⟨u, hune, humem, huneg⟩ := hbad
  let x0 : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).symm u
  have hxcoords :
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x0 = u := by
    exact
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).apply_symm_apply u
  have hxmem : x0 ∈ euclideanParityBoundaryFlatSubspace p N := by
    rw [mem_euclideanParityBoundaryFlatSubspace_iff, hxcoords]
    exact humem
  let x : euclideanParityBoundaryFlatSubspace p N := ⟨x0, hxmem⟩
  have hx0ne : x0 ≠ 0 := by
    intro hx0
    apply hune
    have h := congrArg
      (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) hx0
    simpa [x0] using h
  have hxne : x ≠ 0 := by
    intro hx
    apply hx0ne
    simpa [x] using congrArg Subtype.val hx
  have hambneg :
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin x0)
          x0) < 0 := by
    rw [← quadraticForm_re_eq_re_inner_apply_self
      (canonicalSourceMatrix L N) x0]
    rw [hxcoords]
    exact huneg
  refine ⟨x, hxne, ?_⟩
  rw [re_inner_parityCompressedCanonical_self]
  exact hambneg

theorem exists_negative_eigenmode_of_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hbad : ParityBad p L N) :
    ∃ lam : ℝ, lam < 0 ∧
      ∃ x : euclideanParityBoundaryFlatSubspace p N,
        x ≠ 0 ∧
        parityCompressedCanonical p L N x = (lam : ℂ) • x := by
  obtain ⟨x, hxne, hxneg⟩ :=
    exists_negative_compressed_direction_of_parityBad hbad
  let V := euclideanParityBoundaryFlatSubspace p N
  let T : V →ₗ[ℂ] V := parityCompressedCanonical p L N
  let Tc : V →L[ℂ] V := parityCompressedCanonicalCLM p L N
  letI : Nontrivial V := nontrivial_of_ne x 0 hxne
  let lam : ℝ :=
    ⨅ z : {z : V // z ≠ 0},
      Complex.re (inner ℂ (T z) z) / ‖(z : V)‖ ^ 2
  have hbdd :
      BddBelow
        (Set.range fun z : {z : V // z ≠ 0} =>
          Complex.re (inner ℂ (T z) z) / ‖(z : V)‖ ^ 2) := by
    refine ⟨-‖Tc‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    have habs := Tc.rayleighQuotient_le_norm (z : V)
    exact neg_le_of_abs_le (by
      simpa [ContinuousLinearMap.rayleighQuotient, T, Tc,
        parityCompressedCanonical, parityCompressedCanonicalCLM] using habs)
  have hlamle :
      lam ≤ Complex.re (inner ℂ (T x) x) / ‖(x : V)‖ ^ 2 := by
    exact ciInf_le hbdd ⟨x, hxne⟩
  have hden : 0 < ‖(x : V)‖ ^ 2 := by positivity
  have hrqneg :
      Complex.re (inner ℂ (T x) x) / ‖(x : V)‖ ^ 2 < 0 := by
    exact div_neg_of_neg_of_pos (by simpa [T] using hxneg) hden
  have hlamneg : lam < 0 := lt_of_le_of_lt hlamle hrqneg
  have hsym : T.IsSymmetric := by
    simpa [T] using parityCompressedCanonical_isSymmetric p L N
  have hlameig : T.HasEigenvalue (lam : ℂ) := by
    simpa [lam, T] using hsym.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨v, hv⟩ := hlameig.exists_hasEigenvector
  exact ⟨lam, hlamneg, v, hv.2, hv.apply_eq_smul⟩

theorem re_inner_successor_nonnegative_on_centeredImage
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (x : EuclideanSpace ℂ (Fin (2 * N + 1)))
    (hx : x ∈ euclideanParityBoundaryFlatSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ
        ((canonicalSourceMatrix L (N + 1)).toEuclideanLin
          (euclideanCenteredZeroExtend (Nat.le_succ N) x))
        (euclideanCenteredZeroExtend (Nat.le_succ N) x)) := by
  rw [re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
    hL (Nat.le_succ N) x]
  exact hprev x hx

theorem negative_eigenmode_not_centeredImage
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    ¬ ∃ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
      x ∈ euclideanParityBoundaryFlatSubspace p N ∧
      euclideanCenteredZeroExtend (Nat.le_succ N) x =
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
  rintro ⟨x, hx, hxv⟩
  have hnonneg :=
    re_inner_successor_nonnegative_on_centeredImage
      p hL N hprev x hx
  have hvneg :
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L (N + 1)).toEuclideanLin
            (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
          (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) < 0 := by
    have hcomp :
        Complex.re
          (inner ℂ (parityCompressedCanonical p L (N + 1) v) v) < 0 := by
      rw [hveig]
      have hnorm : 0 < ‖v‖ ^ 2 := by positivity
      simpa [inner_smul_left, inner_self_eq_norm_sq] using
        mul_neg_of_neg_of_pos hlam hnorm
    rw [re_inner_parityCompressedCanonical_self] at hcomp
    exact hcomp
  rw [← hxv] at hvneg
  exact (not_lt_of_ge hnonneg) hvneg

end Zeta23.CCM

#print axioms Zeta23.CCM.parityCompressedCanonical_isSymmetric
#print axioms Zeta23.CCM.exists_negative_compressed_direction_of_parityBad
#print axioms Zeta23.CCM.exists_negative_eigenmode_of_parityBad
#print axioms Zeta23.CCM.re_inner_successor_nonnegative_on_centeredImage
#print axioms Zeta23.CCM.negative_eigenmode_not_centeredImage
