import Zeta23.CCM.CanonicalFrozenApertureC2
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped Topology ComplexConjugate

/-!
# Post-#282 compressed-first aperture calculus

The authoritative differentiated object is the legal compressed production
family itself.  The ambient entrywise derivative matrices introduced in #282
remain historical candidates and are not used to define the derivatives below.

The Frechet derivative is taken over the real aperture variable.  The codomain
is the finite-dimensional complex-linear endomorphism space regarded as a real
normed space.
-/

/-- The existing parity-compressed production family, exposed as a CLM-valued
real-aperture function. -/
def canonicalParityCompressedFamilyCLM
    (p : ReversalParity) (K : ℕ) (L : ℝ) :
    euclideanParityBoundaryFlatSubspace p K →L[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  parityCompressedCanonicalCLM p L K

/-- Actual first real-aperture derivative of the compressed family. -/
def canonicalParityApertureFirstCLM
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →L[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  productionParityFirstJetCLM p K L

/-- Actual second real-aperture derivative of the compressed family. -/
def canonicalParityApertureSecondCLM
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →L[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  productionParitySecondJetCLM p K L

def canonicalParityApertureFirst
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  (canonicalParityApertureFirstCLM p L K).toLinearMap

def canonicalParityApertureSecond
    (p : ReversalParity) (L : ℝ) (K : ℕ) :
    euclideanParityBoundaryFlatSubspace p K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  (canonicalParityApertureSecondCLM p L K).toLinearMap

/-- Native strict-even compressed family; the generic even parity carrier is
definitionally the historical strict-even carrier. -/
def canonicalEvenCompressedFamilyCLM
    (K : ℕ) (L : ℝ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  parityCompressedCanonicalCLM .even L K

def canonicalEvenApertureFirstCLM
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  productionParityFirstJetCLM .even K L

def canonicalEvenApertureSecondCLM
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →L[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  productionParitySecondJetCLM .even K L

def canonicalEvenApertureFirst
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  (canonicalEvenApertureFirstCLM L K).toLinearMap

def canonicalEvenApertureSecond
    (L : ℝ) (K : ℕ) :
    euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ]
      euclideanEvenBoundaryFlatSubspace K :=
  (canonicalEvenApertureSecondCLM L K).toLinearMap

@[simp] theorem canonicalEvenCompressedFamilyCLM_apply
    (L : ℝ) (K : ℕ) (x : euclideanEvenBoundaryFlatSubspace K) :
    canonicalEvenCompressedFamilyCLM K L x =
      (euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
        ((canonicalSourceMatrix L K).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * K + 1)))) := rfl

/-- Exact semantic target for the new production calculus.  This proposition is
used only by validation tooling; downstream theorem endpoints consume the
proved theorem below rather than a caller-supplied instance. -/
def CanonicalParityCompressedC2 (p : ReversalParity) (K : ℕ) : Prop :=
  ContDiffOn ℝ 2 (canonicalParityCompressedFamilyCLM p K) (Ioi (0 : ℝ))

/-- Exact strict-even native counterpart. -/
def CanonicalEvenCompressedC2 (K : ℕ) : Prop :=
  ContDiffOn ℝ 2 (canonicalEvenCompressedFamilyCLM K) (Ioi (0 : ℝ))

/-!
The following two statements are the critical seam-gluing targets.  They are
proved by freezing the cutoff on each side, using the existing analytic
fixed-cell family and the boundary-flat source-jet cancellations at the
entering atom, then gluing the value/first/second jets.
-/

/-- Production parity compression is C2 on the whole positive aperture axis. -/
theorem canonicalParityCompressedC2_proved
    (p : ReversalParity) (K : ℕ) :
    CanonicalParityCompressedC2 p K := by
  unfold CanonicalParityCompressedC2 canonicalParityCompressedFamilyCLM
  have hdiff :
      DifferentiableOn ℝ
        (fun L : ℝ => parityCompressedCanonicalCLM p L K) (Ioi (0 : ℝ)) := by
    intro L hL
    exact
      (hasDerivAt_parityCompressedCanonicalCLM_pos p K hL)
        .differentiableAt.differentiableWithinAt
  have hfirstDiff :
      DifferentiableOn ℝ (productionParityFirstJetCLM p K) (Ioi (0 : ℝ)) := by
    intro L hL
    exact
      (hasDerivAt_productionParityFirstJetCLM_pos p K hL)
        .differentiableAt.differentiableWithinAt
  have hsecondCont :
      ContinuousOn (productionParitySecondJetCLM p K) (Ioi (0 : ℝ)) := by
    intro L hL
    exact
      (continuousAt_productionParitySecondJetCLM_pos p K hL)
        .continuousWithinAt
  have hfirstC1 :
      ContDiffOn ℝ 1 (productionParityFirstJetCLM p K) (Ioi (0 : ℝ)) := by
    rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
    refine ⟨hfirstDiff, ?_⟩
    exact hsecondCont.congr fun L hL => by
      rw [derivWithin_of_isOpen isOpen_Ioi hL]
      exact (hasDerivAt_productionParityFirstJetCLM_pos p K hL).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨hdiff, by simp, ?_⟩
  exact hfirstC1.congr fun L hL => by
    exact (hasDerivAt_parityCompressedCanonicalCLM_pos p K hL).deriv

/-- Native strict-even production compression is C2 on positive aperture. -/
theorem canonicalEvenCompressedC2_proved
    (K : ℕ) :
    CanonicalEvenCompressedC2 K := by
  simpa [CanonicalEvenCompressedC2, canonicalEvenCompressedFamilyCLM,
    CanonicalParityCompressedC2, canonicalParityCompressedFamilyCLM] using
    canonicalParityCompressedC2_proved .even K

/-- The actual first derivative is self-adjoint at every positive aperture. -/
theorem canonicalEvenApertureFirst_isSymmetric
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := euclideanEvenBoundaryFlatSubspace K)
      (canonicalEvenApertureFirst L K) := by
  intro x y
  have hOp :=
    hasDerivAt_parityCompressedCanonicalCLM_pos .even K hL
  have hx :
      HasDerivAt
        (fun s : ℝ => canonicalEvenCompressedFamilyCLM K s x)
        (canonicalEvenApertureFirstCLM L K x) L := by
    simpa [canonicalEvenCompressedFamilyCLM,
      canonicalEvenApertureFirstCLM] using
      hOp.clm_apply (hasDerivAt_const L x)
  have hy :
      HasDerivAt
        (fun s : ℝ => canonicalEvenCompressedFamilyCLM K s y)
        (canonicalEvenApertureFirstCLM L K y) L := by
    simpa [canonicalEvenCompressedFamilyCLM,
      canonicalEvenApertureFirstCLM] using
      hOp.clm_apply (hasDerivAt_const L y)
  have hxy :
      HasDerivAt
        (fun s : ℝ => inner ℂ
          (canonicalEvenCompressedFamilyCLM K s x) y)
        (inner ℂ (canonicalEvenApertureFirstCLM L K x) y) L := by
    simpa using hx.inner ℂ (hasDerivAt_const L y)
  have hyx :
      HasDerivAt
        (fun s : ℝ => inner ℂ x
          (canonicalEvenCompressedFamilyCLM K s y))
        (inner ℂ x (canonicalEvenApertureFirstCLM L K y)) L := by
    simpa using (hasDerivAt_const L x).inner ℂ hy
  have hfun :
      (fun s : ℝ => inner ℂ
        (canonicalEvenCompressedFamilyCLM K s x) y) =
      (fun s : ℝ => inner ℂ x
        (canonicalEvenCompressedFamilyCLM K s y)) := by
    funext s
    exact parityCompressedCanonical_isSymmetric .even s K x y
  have hyx' :
      HasDerivAt
        (fun s : ℝ => inner ℂ
          (canonicalEvenCompressedFamilyCLM K s x) y)
        (inner ℂ x (canonicalEvenApertureFirstCLM L K y)) L := by
    rw [hfun]
    exact hyx
  have hEq := hxy.unique hyx'
  simpa [canonicalEvenApertureFirst] using hEq

/-- The actual second derivative is self-adjoint at every positive aperture. -/
theorem canonicalEvenApertureSecond_isSymmetric
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ)
      (E := euclideanEvenBoundaryFlatSubspace K)
      (canonicalEvenApertureSecond L K) := by
  intro x y
  have hOp :=
    hasDerivAt_productionParityFirstJetCLM_pos .even K hL
  have hx :
      HasDerivAt
        (fun s : ℝ => canonicalEvenApertureFirstCLM s K x)
        (canonicalEvenApertureSecondCLM L K x) L := by
    simpa [canonicalEvenApertureFirstCLM,
      canonicalEvenApertureSecondCLM] using
      hOp.clm_apply (hasDerivAt_const L x)
  have hy :
      HasDerivAt
        (fun s : ℝ => canonicalEvenApertureFirstCLM s K y)
        (canonicalEvenApertureSecondCLM L K y) L := by
    simpa [canonicalEvenApertureFirstCLM,
      canonicalEvenApertureSecondCLM] using
      hOp.clm_apply (hasDerivAt_const L y)
  have hxy :
      HasDerivAt
        (fun s : ℝ => inner ℂ
          (canonicalEvenApertureFirstCLM s K x) y)
        (inner ℂ (canonicalEvenApertureSecondCLM L K x) y) L := by
    simpa using hx.inner ℂ (hasDerivAt_const L y)
  have hyx :
      HasDerivAt
        (fun s : ℝ => inner ℂ x
          (canonicalEvenApertureFirstCLM s K y))
        (inner ℂ x (canonicalEvenApertureSecondCLM L K y)) L := by
    simpa using (hasDerivAt_const L x).inner ℂ hy
  have hevent :
      (fun s : ℝ => inner ℂ
        (canonicalEvenApertureFirstCLM s K x) y) =ᶠ[𝓝 L]
      (fun s : ℝ => inner ℂ x
        (canonicalEvenApertureFirstCLM s K y)) := by
    filter_upwards [Ioi_mem_nhds hL] with s hs
    exact canonicalEvenApertureFirst_isSymmetric hs K x y
  have hyx' := hyx.congr_of_eventuallyEq hevent.symm
  have hEq := hxy.unique hyx'
  simpa [canonicalEvenApertureSecond] using hEq

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalParityCompressedC2_proved
#print axioms Zeta23.CCM.canonicalEvenCompressedC2_proved
#print axioms Zeta23.CCM.canonicalEvenApertureFirst_isSymmetric
#print axioms Zeta23.CCM.canonicalEvenApertureSecond_isSymmetric
