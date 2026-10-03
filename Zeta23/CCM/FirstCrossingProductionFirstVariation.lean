import Zeta23.CCM.FirstCrossingGlobalAlignment
import Zeta23.CCM.FirstCrossingProductionRemainder
import Zeta23.CCM.ConstrainedParitySpectrum
import Zeta23.CCM.ConstrainedEuclideanSector
import Mathlib.Analysis.Calculus.Darboux

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate Topology

/-!
# Post-#281 production first variation

This module introduces an ambient-entry derivative candidate for the
production canonical source and proves those candidate matrices are Hermitian.
At an interior fixed-cutoff point they are intended to agree with the actual
compressed derivative; at a cutoff seam that agreement is a separate theorem
obligation and is never inferred from total `deriv` alone.
It also packages the exact fixed-vector first/second variation scalars and
proves the one-sided sign consequence used at a generated first-negative
boundary whenever the fixed-vector derivative is realized.

The source/arithmetic realization and global C2 seam gluing are separate proof
obligations; no derivative identity is obtained by defining curvature to be the
desired arithmetic expression.
-/

/-- Real scalar entry of the production canonical source matrix. -/
def productionApertureEntryReal
    (K : ℕ) (i j : Fin (2 * K + 1)) (L : ℝ) : ℝ :=
  (canonicalSourceMatrix L K i j).re

/-- Ambient-entry first derivative candidate.

This object is not by itself authoritative at a cutoff seam: downstream
contact theorems require `ProductionContactFirstOperatorRealized`. -/
def productionApertureFirstMatrix
    (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j => ((deriv (productionApertureEntryReal K i j) L : ℝ) : ℂ)

/-- Ambient-entry second derivative candidate, subject to the same seam
realization firewall as the first derivative. -/
def productionApertureSecondMatrix
    (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  fun i j =>
    ((deriv
      (fun s : ℝ => (deriv (productionApertureEntryReal K i j) s : ℝ)) L : ℝ) : ℂ)

private theorem productionApertureEntryReal_comm
    (K : ℕ) (i j : Fin (2 * K + 1)) :
    productionApertureEntryReal K i j =
      productionApertureEntryReal K j i := by
  funext L
  unfold productionApertureEntryReal
  rw [canonicalSourceMatrix_eq_dictionaryMatrix,
      dictionaryMatrix_apply_comm]

/-- The first production derivative is Hermitian. -/
theorem productionApertureFirstMatrix_isHermitian
    (L : ℝ) (K : ℕ) :
    (productionApertureFirstMatrix L K).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  unfold productionApertureFirstMatrix
  rw [productionApertureEntryReal_comm K j i]
  simp

/-- The second production derivative is Hermitian. -/
theorem productionApertureSecondMatrix_isHermitian
    (L : ℝ) (K : ℕ) :
    (productionApertureSecondMatrix L K).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  unfold productionApertureSecondMatrix
  rw [productionApertureEntryReal_comm K j i]
  simp

/-- Orthogonal parity compression of the first production derivative. -/
def parityProductionApertureFirstCLM
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →L[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  let V := euclideanParityBoundaryFlatSubspace p K
  V.orthogonalProjectionOnto.comp
    ((Matrix.toEuclideanCLM
        (n := Fin (2 * K + 1)) (𝕜 := ℂ)
        (productionApertureFirstMatrix L K)).comp
      (V.subtypeL :
        V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1))))

/-- Linear-map form of the first production derivative. -/
def parityProductionApertureFirst
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  (parityProductionApertureFirstCLM p L K).toLinearMap

/-- Orthogonal parity compression of the second production derivative. -/
def parityProductionApertureSecondCLM
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →L[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  let V := euclideanParityBoundaryFlatSubspace p K
  V.orthogonalProjectionOnto.comp
    ((Matrix.toEuclideanCLM
        (n := Fin (2 * K + 1)) (𝕜 := ℂ)
        (productionApertureSecondMatrix L K)).comp
      (V.subtypeL :
        V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1))))

/-- Linear-map form of the second production derivative. -/
def parityProductionApertureSecond
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  (parityProductionApertureSecondCLM p L K).toLinearMap

/-- The compressed first derivative is self-adjoint/symmetric. -/
theorem parityProductionApertureFirst_isSymmetric
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := euclideanParityBoundaryFlatSubspace p K)
      (parityProductionApertureFirst p L K) := by
  intro x y
  change
    inner ℂ
      ((euclideanParityBoundaryFlatSubspace p K).orthogonalProjectionOnto
        ((productionApertureFirstMatrix L K).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * K + 1))))) y =
    inner ℂ x
      ((euclideanParityBoundaryFlatSubspace p K).orthogonalProjectionOnto
        ((productionApertureFirstMatrix L K).toEuclideanLin
          (y : EuclideanSpace ℂ (Fin (2 * K + 1)))))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (productionApertureFirstMatrix_isHermitian L K))
      (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (y : EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- The compressed second derivative is self-adjoint/symmetric. -/
theorem parityProductionApertureSecond_isSymmetric
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := euclideanParityBoundaryFlatSubspace p K)
      (parityProductionApertureSecond p L K) := by
  intro x y
  change
    inner ℂ
      ((euclideanParityBoundaryFlatSubspace p K).orthogonalProjectionOnto
        ((productionApertureSecondMatrix L K).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * K + 1))))) y =
    inner ℂ x
      ((euclideanParityBoundaryFlatSubspace p K).orthogonalProjectionOnto
        ((productionApertureSecondMatrix L K).toEuclideanLin
          (y : EuclideanSpace ℂ (Fin (2 * K + 1)))))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (productionApertureSecondMatrix_isHermitian L K))
      (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (y : EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- Fixed-vector production energy in one parity carrier. -/
def productionContactFixedEnergy
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  Complex.re (inner ℂ (parityCompressedCanonical p L K z) z)

/-- Actual first variation obtained from the entrywise production derivative. -/
def productionContactFirstVariation
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  Complex.re
    (inner ℂ (parityProductionApertureFirst p L K z) z)

/-- Actual fixed-vector second aperture variation. -/
def productionContactFixedSecondVariation
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  Complex.re
    (inner ℂ (parityProductionApertureSecond p L K z) z)

/-- Exact statement that the entrywise derivative realizes the derivative of
the fixed-vector production energy at this aperture. -/
def ProductionContactFirstVariationRealized
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : Prop :=
  HasDerivAt
    (fun s : ℝ => productionContactFixedEnergy p s K z)
    (productionContactFirstVariation p L K z) L

/-- Exact second-order realization statement. -/
def ProductionContactSecondVariationRealized
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : Prop :=
  HasDerivAt
    (fun s : ℝ => productionContactFirstVariation p s K z)
    (productionContactFixedSecondVariation p L K z) L


/-- Fail-closed authorization that the candidate first derivative is the
actual derivative of the compressed legal family in every quadratic
direction.  On an interior cell this should follow from the frozen analytic
family; at a seam it requires the independent legal-carrier gluing theorem. -/
def ProductionContactFirstOperatorRealized
    (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  ∀ z : euclideanParityBoundaryFlatSubspace p K,
    ProductionContactFirstVariationRealized p L K z

/-- Corresponding second-order realization firewall. -/
def ProductionContactSecondOperatorRealized
    (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  ∀ z : euclideanParityBoundaryFlatSubspace p K,
    ProductionContactSecondVariationRealized p L K z

/-- One-sided calculus lemma: a differentiable fixed-vector energy which is
nonnegative to the left of a zero contact has nonpositive first derivative. -/
theorem firstVariation_nonpos_of_leftPrefix
    {f : ℝ → ℝ} {Lsmall Lstar J : ℝ}
    (hLt : Lsmall < Lstar)
    (hzero : f Lstar = 0)
    (hprefix :
      ∀ L : ℝ, Lsmall ≤ L → L ≤ Lstar → 0 ≤ f L)
    (hderiv : HasDerivAt f J Lstar) :
    J ≤ 0 := by
  have hmin : IsMinOn f (Icc Lsmall Lstar) Lstar := by
    intro L hL
    rw [hzero]
    exact hprefix L hL.1 hL.2
  have htangent :
      Lsmall - Lstar ∈ posTangentConeAt (Icc Lsmall Lstar) Lstar :=
    sub_mem_posTangentConeAt_of_segment_subset
      (by rw [segment_symm, segment_eq_Icc (le_of_lt hLt)])
  have hmul :=
    hmin.localize.hasFDerivWithinAt_nonneg
      hderiv.hasDerivWithinAt htangent
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hmul
  nlinarith

/-- Global-prefix positivity supplies fixed-vector nonnegativity at the selected
cutoff. -/
theorem GeneratedGlobalFirstCrossing.selectedFixedEnergy_nonnegative
    (g : GeneratedGlobalFirstCrossing)
    (p : ReversalParity)
    (z : euclideanParityBoundaryFlatSubspace p (g.shell.k + 1))
    {L : ℝ}
    (hsmall : g.shell.Lsmall ≤ L)
    (hstar : L ≤ g.shell.Lstar) :
    0 ≤ productionContactFixedEnergy p L (g.shell.k + 1) z := by
  have hbottom :=
    g.selectedParity_prefix_nonnegative p hsmall hstar
  have h :=
    shiftedParityCompressed_nonnegative_of_le_bottom
      p L (g.shell.k + 1) (lam := 0) hbottom z
  simpa [productionContactFixedEnergy] using h

/-- Generated first-contact sign: once the actual fixed-vector derivative
realization is established, every zero contact kernel direction has J1 <= 0. -/
theorem GeneratedGlobalFirstCrossing.firstVariation_nonpos_of_kernel
    (g : GeneratedGlobalFirstCrossing)
    (p : ReversalParity)
    (z : euclideanParityBoundaryFlatSubspace p (g.shell.k + 1))
    (hkernel :
      parityCompressedCanonical p g.shell.Lstar (g.shell.k + 1) z = 0)
    (hrealized :
      ProductionContactFirstVariationRealized
        p g.shell.Lstar (g.shell.k + 1) z) :
    productionContactFirstVariation
        p g.shell.Lstar (g.shell.k + 1) z ≤ 0 := by
  apply firstVariation_nonpos_of_leftPrefix
    (f := fun L => productionContactFixedEnergy p L (g.shell.k + 1) z)
    g.shell.Lsmall_lt_Lstar
  · simp [productionContactFixedEnergy, hkernel]
  · intro L hsmall hstar
    exact g.selectedFixedEnergy_nonnegative p z hsmall hstar
  · exact hrealized

end Zeta23.CCM

#print axioms Zeta23.CCM.productionApertureFirstMatrix_isHermitian
#print axioms Zeta23.CCM.productionApertureSecondMatrix_isHermitian
#print axioms Zeta23.CCM.parityProductionApertureFirst_isSymmetric
#print axioms Zeta23.CCM.parityProductionApertureSecond_isSymmetric
#print axioms Zeta23.CCM.firstVariation_nonpos_of_leftPrefix
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.firstVariation_nonpos_of_kernel
