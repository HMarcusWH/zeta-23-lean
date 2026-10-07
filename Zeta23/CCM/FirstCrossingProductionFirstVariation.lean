import Zeta23.CCM.FirstCrossingGlobalAlignment
import Zeta23.CCM.CanonicalCompressedApertureC2
import Zeta23.CCM.ProductionWeightedTestCalculus
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


/-- Native strict-even orthogonal compression of the first production
derivative.  Defining this directly on the even carrier keeps the topology and
inner-product instances identical to the strict-even response layer. -/
def evenProductionApertureFirstCLM
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  let V := euclideanEvenBoundaryFlatSubspace K
  V.orthogonalProjectionOnto.comp
    ((Matrix.toEuclideanCLM
        (n := Fin (2 * K + 1)) (𝕜 := ℂ)
        (productionApertureFirstMatrix L K)).comp
      (V.subtypeL :
        V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1))))

/-- Linear-map form of the native strict-even first derivative candidate. -/
def evenProductionApertureFirst
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  (evenProductionApertureFirstCLM L K).toLinearMap

/-- Native strict-even orthogonal compression of the second production
derivative. -/
def evenProductionApertureSecondCLM
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  let V := euclideanEvenBoundaryFlatSubspace K
  V.orthogonalProjectionOnto.comp
    ((Matrix.toEuclideanCLM
        (n := Fin (2 * K + 1)) (𝕜 := ℂ)
        (productionApertureSecondMatrix L K)).comp
      (V.subtypeL :
        V →L[ℂ] EuclideanSpace ℂ (Fin (2 * K + 1))))

/-- Linear-map form of the native strict-even second derivative candidate. -/
def evenProductionApertureSecond
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  (evenProductionApertureSecondCLM L K).toLinearMap

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


/-- Native even-carrier symmetry theorem for the first derivative.  This is
proved directly on the strict-even carrier rather than transported through the
definitionally equivalent parity carrier, avoiding typeclass-instance drift. -/
theorem evenProductionApertureFirst_isSymmetric
    (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := euclideanEvenBoundaryFlatSubspace K)
      (evenProductionApertureFirst L K) := by
  intro x y
  change
    inner ℂ
      ((euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
        ((productionApertureFirstMatrix L K).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * K + 1))))) y =
    inner ℂ x
      ((euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
        ((productionApertureFirstMatrix L K).toEuclideanLin
          (y : EuclideanSpace ℂ (Fin (2 * K + 1)))))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (productionApertureFirstMatrix_isHermitian L K))
      (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
      (y : EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- Native even-carrier symmetry theorem for the second derivative. -/
theorem evenProductionApertureSecond_isSymmetric
    (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := euclideanEvenBoundaryFlatSubspace K)
      (evenProductionApertureSecond L K) := by
  intro x y
  change
    inner ℂ
      ((euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
        ((productionApertureSecondMatrix L K).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * K + 1))))) y =
    inner ℂ x
      ((euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
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

/-- Seam-safe scalar first variation: differentiate the fixed legal-compressed
energy itself.  This does not commute differentiation through the ambient
matrix at a seam. -/
def productionContactFirstVariation
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  deriv (fun s : ℝ => productionContactFixedEnergy p s K z) L

/-- Seam-safe fixed-vector second variation. -/
def productionContactFixedSecondVariation
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  deriv (fun s : ℝ => productionContactFirstVariation p s K z) L

/-- Quadratic form of the ambient-entry first-derivative candidate. -/
def productionContactFirstOperatorQuadratic
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  Complex.re (inner ℂ (parityProductionApertureFirst p L K z) z)

/-- Quadratic form of the ambient-entry second-derivative candidate. -/
def productionContactSecondOperatorQuadratic
    (p : ReversalParity) (L : ℝ) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  Complex.re (inner ℂ (parityProductionApertureSecond p L K z) z)

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
    ProductionContactFirstVariationRealized p L K z ∧
      productionContactFirstOperatorQuadratic p L K z =
        productionContactFirstVariation p L K z

/-- Corresponding second-order realization firewall. -/
def ProductionContactSecondOperatorRealized
    (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  ∀ z : euclideanParityBoundaryFlatSubspace p K,
    ProductionContactSecondVariationRealized p L K z ∧
      productionContactSecondOperatorQuadratic p L K z =
        productionContactFixedSecondVariation p L K z

/-- Complete legal-carrier C2 realization.  This is the seam-safe gate:
ambient-entry total derivatives do not authorize it automatically. -/
def ProductionContactC2Realized
    (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  ProductionContactFirstOperatorRealized p L K ∧
    ProductionContactSecondOperatorRealized p L K


/-- Strict-even first-operator realization on the explicitly typed carrier. -/
def EvenProductionContactFirstOperatorRealized
    (L : ℝ) (K : ℕ) : Prop :=
  ∀ z : euclideanEvenBoundaryFlatSubspace K,
    ProductionContactFirstVariationRealized .even L K z ∧
      Complex.re (inner ℂ (evenProductionApertureFirst L K z) z) =
        productionContactFirstVariation .even L K z

/-- Strict-even second-operator realization on the explicitly typed carrier. -/
def EvenProductionContactSecondOperatorRealized
    (L : ℝ) (K : ℕ) : Prop :=
  ∀ z : euclideanEvenBoundaryFlatSubspace K,
    ProductionContactSecondVariationRealized .even L K z ∧
      Complex.re (inner ℂ (evenProductionApertureSecond L K z) z) =
        productionContactFixedSecondVariation .even L K z

/-- Complete strict-even C2 realization, including the seam-safe operator
identifications. -/
def EvenProductionContactC2Realized
    (L : ℝ) (K : ℕ) : Prop :=
  EvenProductionContactFirstOperatorRealized L K ∧
    EvenProductionContactSecondOperatorRealized L K

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


/-- The fixed legal parity energy has the actual compressed first jet as its
real derivative at every positive aperture. -/
theorem canonicalParity_fixedEnergy_hasDerivAt
    (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) :
    HasDerivAt
      (fun s : ℝ => productionContactFixedEnergy p s K z)
      (Complex.re
        (inner ℂ (canonicalParityApertureFirst p L K z) z)) L := by
  have hOp :=
    hasDerivAt_parityCompressedCanonicalCLM_pos p K hL
  have hz :
      HasDerivAt
        (fun s : ℝ => canonicalParityCompressedFamilyCLM p K s z)
        (canonicalParityApertureFirstCLM p L K z) L := by
    simpa [canonicalParityCompressedFamilyCLM,
      canonicalParityApertureFirstCLM] using
      hasDerivAt_complexCLM_apply_const_real hOp z
  have hinner :
      HasDerivAt
        (fun s : ℝ =>
          inner ℂ (canonicalParityCompressedFamilyCLM p K s z) z)
        (inner ℂ (canonicalParityApertureFirstCLM p L K z) z) L := by
    simpa using hz.inner ℂ (hasDerivAt_const L z)
  have hre :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt L hinner
  simpa [productionContactFixedEnergy, parityCompressedCanonical,
    canonicalParityCompressedFamilyCLM, canonicalParityApertureFirst,
    canonicalParityApertureFirstCLM, Function.comp_def] using hre

/-- Therefore the seam-safe scalar derivative is exactly the quadratic form of
the actual compressed first jet. -/
theorem canonicalParity_firstVariation_eq_inner
    (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) :
    productionContactFirstVariation p L K z =
      Complex.re (inner ℂ (canonicalParityApertureFirst p L K z) z) := by
  unfold productionContactFirstVariation
  exact (canonicalParity_fixedEnergy_hasDerivAt p hL K z).deriv

/-- The first-variation function itself has the actual compressed second jet as
its derivative at every positive aperture. -/
theorem canonicalParity_firstVariation_hasDerivAt
    (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) :
    HasDerivAt
      (fun s : ℝ => productionContactFirstVariation p s K z)
      (Complex.re
        (inner ℂ (canonicalParityApertureSecond p L K z) z)) L := by
  have hOp :=
    hasDerivAt_productionParityFirstJetCLM_pos p K hL
  have hz :
      HasDerivAt
        (fun s : ℝ => canonicalParityApertureFirstCLM p s K z)
        (canonicalParityApertureSecondCLM p L K z) L := by
    simpa [canonicalParityApertureFirstCLM,
      canonicalParityApertureSecondCLM] using
      hasDerivAt_complexCLM_apply_const_real hOp z
  have hinner :
      HasDerivAt
        (fun s : ℝ =>
          inner ℂ (canonicalParityApertureFirstCLM p s K z) z)
        (inner ℂ (canonicalParityApertureSecondCLM p L K z) z) L := by
    simpa using hz.inner ℂ (hasDerivAt_const L z)
  have hre :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt L hinner
  have hevent :
      (fun s : ℝ => productionContactFirstVariation p s K z) =ᶠ[𝓝 L]
        (fun s : ℝ =>
          Complex.re (inner ℂ
            (canonicalParityApertureFirstCLM p s K z) z)) := by
    filter_upwards [Ioi_mem_nhds hL] with s hs
    simpa [canonicalParityApertureFirst,
      canonicalParityApertureFirstCLM] using
      canonicalParity_firstVariation_eq_inner p hs K z
  have htarget :
      HasDerivAt
        (fun s : ℝ =>
          Complex.re (inner ℂ
            (canonicalParityApertureFirstCLM p s K z) z))
        (Complex.re
          (inner ℂ (canonicalParityApertureSecondCLM p L K z) z)) L := by
    simpa [Function.comp_def] using hre
  exact htarget.congr_of_eventuallyEq hevent

/-- The seam-safe fixed second variation is exactly the actual compressed
second-jet quadratic form. -/
theorem canonicalParity_fixedSecond_eq_inner
    (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanParityBoundaryFlatSubspace p K) :
    productionContactFixedSecondVariation p L K z =
      Complex.re (inner ℂ (canonicalParityApertureSecond p L K z) z) := by
  unfold productionContactFixedSecondVariation
  exact (canonicalParity_firstVariation_hasDerivAt p hL K z).deriv

/-- Native-even wrapper for the actual first-variation identity. -/
theorem canonicalEven_firstVariation_eq_inner
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFirstVariation .even L K z =
      Complex.re (inner ℂ (canonicalEvenApertureFirst L K z) z) := by
  have h :=
    canonicalParity_firstVariation_eq_inner .even hL K z
  change
    productionContactFirstVariation .even L K z =
      Complex.re
        (inner ℂ
          (((productionParityFirstJetCLM .even K L) z :
              euclideanParityBoundaryFlatSubspace .even K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) at h
  change
    productionContactFirstVariation .even L K z =
      Complex.re
        (inner ℂ
          (((productionParityFirstJetCLM .even K L) z :
              euclideanParityBoundaryFlatSubspace .even K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))
          (z : EuclideanSpace ℂ (Fin (2 * K + 1))))
  exact h

/-- Native-even wrapper for the actual fixed second-variation identity. -/
theorem canonicalEven_fixedSecond_eq_inner
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFixedSecondVariation .even L K z =
      Complex.re (inner ℂ (canonicalEvenApertureSecond L K z) z) := by
  have h :=
    canonicalParity_fixedSecond_eq_inner .even hL K z
  change
    productionContactFixedSecondVariation .even L K z =
      Complex.re
        (inner ℂ
          (((productionParitySecondJetCLM .even K L) z :
              euclideanParityBoundaryFlatSubspace .even K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) at h
  change
    productionContactFixedSecondVariation .even L K z =
      Complex.re
        (inner ℂ
          (((productionParitySecondJetCLM .even K L) z :
              euclideanParityBoundaryFlatSubspace .even K) :
            EuclideanSpace ℂ (Fin (2 * K + 1)))
          (z : EuclideanSpace ℂ (Fin (2 * K + 1))))
  exact h


/-- Simultaneous unit-phase rotation preserves the seam-safe first variation. -/
theorem productionContactFirstVariation_unitPhase
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : ℂ) (hu : ‖u‖ = 1)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFirstVariation .even L K (u • z) =
      productionContactFirstVariation .even L K z := by
  rw [canonicalEven_firstVariation_eq_inner hL K (u • z),
      canonicalEven_firstVariation_eq_inner hL K z]
  have hunit : star u * u = 1 := by
    change conj u * u = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp [hu]
  have hcomplex :
      inner ℂ (canonicalEvenApertureFirst L K (u • z)) (u • z) =
        inner ℂ (canonicalEvenApertureFirst L K z) z := by
    calc
      inner ℂ (canonicalEvenApertureFirst L K (u • z)) (u • z) =
          inner ℂ (u • canonicalEvenApertureFirst L K z) (u • z) := by
        rw [map_smul]
      _ = star u * inner ℂ (canonicalEvenApertureFirst L K z) (u • z) := by
        rw [inner_smul_left]
      _ = star u * (u * inner ℂ (canonicalEvenApertureFirst L K z) z) := by
        rw [inner_smul_right]
      _ = (star u * u) * inner ℂ (canonicalEvenApertureFirst L K z) z := by
        ring
      _ = inner ℂ (canonicalEvenApertureFirst L K z) z := by
        rw [hunit, one_mul]
  exact congrArg Complex.re hcomplex


end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalParity_fixedEnergy_hasDerivAt
#print axioms Zeta23.CCM.canonicalParity_firstVariation_eq_inner
#print axioms Zeta23.CCM.canonicalParity_firstVariation_hasDerivAt
#print axioms Zeta23.CCM.canonicalParity_fixedSecond_eq_inner
#print axioms Zeta23.CCM.canonicalEven_firstVariation_eq_inner
#print axioms Zeta23.CCM.canonicalEven_fixedSecond_eq_inner
#print axioms Zeta23.CCM.productionApertureFirstMatrix_isHermitian
#print axioms Zeta23.CCM.productionApertureSecondMatrix_isHermitian
#print axioms Zeta23.CCM.parityProductionApertureFirst_isSymmetric
#print axioms Zeta23.CCM.parityProductionApertureSecond_isSymmetric
#print axioms Zeta23.CCM.evenProductionApertureFirst_isSymmetric
#print axioms Zeta23.CCM.evenProductionApertureSecond_isSymmetric
#print axioms Zeta23.CCM.firstVariation_nonpos_of_leftPrefix
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.firstVariation_nonpos_of_kernel
