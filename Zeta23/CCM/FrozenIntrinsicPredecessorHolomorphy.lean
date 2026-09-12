import Zeta23.CCM.CanonicalApertureSourceHolomorphy
import Zeta23.CCM.FrozenIntrinsicPredecessorComplex
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4R3: intrinsic predecessor holomorphy

The frozen source remainder is now known entrywise analytic on one explicit
punctured strip.  This module pushes that fact through the *actual* matrix
application and parity compression, then through arbitrary scalar coordinates
of the intrinsic predecessor projection, and finally lifts those coordinates to
the logarithmic cover through `Complex.exp`.

The scalar-coordinate formulation is exactly what the determinant argument
needs.  It deliberately avoids adding a stronger topology-dependent analytic
structure on the nested intrinsic predecessor subtype itself, while preserving
the actual production projection and block definitions.

No determinant-density, sign, negative-root exclusion, finite-to-infinite
closure, or RH theorem is claimed here.
-/

/-- Applying the frozen source remainder to one fixed Euclidean vector is a
finite sum of analytic scalar entries times fixed standard basis vectors. -/
private theorem complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_eq_sum_single
    (Q K : ℕ) (z : ℂ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (complexFrozenCanonicalSourceRemainder Q z K).toEuclideanLin x =
      ∑ i : Fin (2 * K + 1),
        (∑ j : Fin (2 * K + 1),
          complexFrozenCanonicalSourceRemainder Q z K i j * x j) •
            EuclideanSpace.single i 1 := by
  rw [Matrix.toLpLin_apply]
  ext k
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The actual frozen source remainder, after application to a fixed vector,
is analytic as a Euclidean-space-valued map on the common source domain. -/
theorem analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
    (Q K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        (complexFrozenCanonicalSourceRemainder Q z K).toEuclideanLin x)
      complexFrozenSourceDomain := by
  have hformula :
      (fun z : ℂ =>
        (complexFrozenCanonicalSourceRemainder Q z K).toEuclideanLin x) =
        (fun z : ℂ =>
          ∑ i : Fin (2 * K + 1),
            (∑ j : Fin (2 * K + 1),
              complexFrozenCanonicalSourceRemainder Q z K i j * x j) •
                EuclideanSpace.single i 1) := by
    funext z
    exact complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_eq_sum_single Q K z x
  rw [hformula]
  apply Finset.analyticOnNhd_fun_sum
  intro i _hi
  have hcoeff : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ∑ j : Fin (2 * K + 1),
          complexFrozenCanonicalSourceRemainder Q z K i j * x j)
      complexFrozenSourceDomain := by
    apply Finset.analyticOnNhd_fun_sum
    intro j _hj
    exact
      (analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain Q K i j).mul
        analyticOnNhd_const
  exact hcoeff.smul analyticOnNhd_const

/-- Parity compression preserves source holomorphy after application to a fixed
parity vector.  The orthogonal projection is fixed in the aperture parameter. -/
theorem analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    (x : euclideanParityBoundaryFlatSubspace p N) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => complexFrozenParityCompressedRemainder Q p z N x)
      complexFrozenSourceDomain := by
  intro z hz
  change AnalyticAt ℂ
    (fun w : ℂ =>
      (euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto
        ((complexFrozenCanonicalSourceRemainder Q w N).toEuclideanLin
          (x : EuclideanSpace ℂ (Fin (2 * N + 1))))) z
  exact
    ((euclideanParityBoundaryFlatSubspace p N).orthogonalProjectionOnto.analyticAt _).comp
      (analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
        Q N (x : EuclideanSpace ℂ (Fin (2 * N + 1))) z hz)

/-- Every fixed scalar coordinate of the exact intrinsic predecessor remainder
is analytic on the common source domain.

The scalar functional is composed algebraically with the genuine intrinsic
predecessor projection first.  The resulting map has the already-topologized
successor parity space as its domain and `ℂ` as codomain, so no auxiliary
normed-space structure on the nested intrinsic subtype is required. -/
theorem analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    (φ : intrinsicParityPredecessorSubspace p N →ₗ[ℂ] ℂ)
    (x : intrinsicParityPredecessorSubspace p N) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => φ (complexFrozenIntrinsicPredecessorRemainder Q p N z x))
      complexFrozenSourceDomain := by
  let c : euclideanParityBoundaryFlatSubspace p (N + 1) →ₗ[ℂ] ℂ :=
    φ.comp (intrinsicPredecessorPart p N)
  let cL : euclideanParityBoundaryFlatSubspace p (N + 1) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap c
  have hpar :=
    analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
      Q p (N + 1)
      (x : euclideanParityBoundaryFlatSubspace p (N + 1))
  intro z hz
  have hc :
      AnalyticAt ℂ
        (fun w : ℂ =>
          cL (complexFrozenParityCompressedRemainder Q p w (N + 1)
            (x : euclideanParityBoundaryFlatSubspace p (N + 1)))) z := by
    have hc0 :
        AnalyticAt ℂ cL
          (complexFrozenParityCompressedRemainder Q p z (N + 1)
            (x : euclideanParityBoundaryFlatSubspace p (N + 1))) :=
      cL.analyticAt _
    have hcomp :=
      AnalyticAt.comp
        (f := fun w : ℂ =>
          complexFrozenParityCompressedRemainder Q p w (N + 1)
            (x : euclideanParityBoundaryFlatSubspace p (N + 1)))
        hc0 (hpar z hz)
    simpa [Function.comp_def] using hcomp
  simpa [complexFrozenIntrinsicPredecessorRemainder, c, cL] using hc

/-- Natural analytic domain on the logarithmic cover.  The puncture at zero
disappears upstairs because `Complex.exp` never vanishes. -/
def liftedFrozenPredecessorDomain : Set ℂ :=
  Complex.exp ⁻¹' complexFrozenSourceDomain

/-- The lifted domain is open. -/
theorem isOpen_liftedFrozenPredecessorDomain :
    IsOpen liftedFrozenPredecessorDomain := by
  exact isOpen_complexFrozenSourceDomain.preimage Complex.continuous_exp

/-- The origin belongs to the lifted domain (`exp 0 = 1`). -/
theorem zero_mem_liftedFrozenPredecessorDomain :
    (0 : ℂ) ∈ liftedFrozenPredecessorDomain := by
  change Complex.exp 0 ∈ complexFrozenSourceDomain
  simp only [Complex.exp_zero]
  constructor
  · simpa [complexArchSafeStrip] using Real.pi_pos
  · simp

/-- Membership in the lifted domain is invariant under one deck translation. -/
theorem add_two_pi_I_mem_liftedFrozenPredecessorDomain_iff
    (z : ℂ) :
    z + 2 * (Real.pi : ℂ) * Complex.I ∈ liftedFrozenPredecessorDomain ↔
      z ∈ liftedFrozenPredecessorDomain := by
  change Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I) ∈ complexFrozenSourceDomain ↔
    Complex.exp z ∈ complexFrozenSourceDomain
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Every fixed scalar coordinate of the lifted frozen remainder is analytic on
the logarithmic cover. -/
theorem analyticOnNhd_liftedFrozenIntrinsicPredecessorRemainder_coord
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    (φ : intrinsicParityPredecessorSubspace p N →ₗ[ℂ] ℂ)
    (x : intrinsicParityPredecessorSubspace p N) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => φ (liftedFrozenIntrinsicPredecessorRemainder Q p N z x))
      liftedFrozenPredecessorDomain := by
  intro z hz
  change AnalyticAt ℂ
    (fun w : ℂ =>
      φ (complexFrozenIntrinsicPredecessorRemainder Q p N (Complex.exp w) x)) z
  exact
    (analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
      Q p N φ x (Complex.exp z) hz).comp analyticAt_cexp

/-- Every fixed scalar coordinate of the full lifted predecessor block is
analytic on the logarithmic cover.  This is the exact interface required by the
finite determinant polynomial. -/
theorem analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
    (Q : ℕ) (p : ReversalParity) (N : ℕ)
    (φ : intrinsicParityPredecessorSubspace p N →ₗ[ℂ] ℂ)
    (x : intrinsicParityPredecessorSubspace p N) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => φ (liftedFrozenIntrinsicPredecessorBlock Q p N z x))
      liftedFrozenPredecessorDomain := by
  intro z hz
  have hscalar : AnalyticAt ℂ (fun w : ℂ => (-w) * φ x) z :=
    analyticAt_id.neg.mul analyticAt_const
  have hrem :=
    analyticOnNhd_liftedFrozenIntrinsicPredecessorRemainder_coord
      Q p N φ x z hz
  have hadd :
      AnalyticAt ℂ
        (fun w : ℂ =>
          (-w) * φ x +
            φ (liftedFrozenIntrinsicPredecessorRemainder Q p N w x)) z :=
    hscalar.fun_add hrem
  simpa [liftedFrozenIntrinsicPredecessorBlock, smul_eq_mul] using hadd

end Zeta23.CCM

#print axioms Zeta23.CCM.analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
#print axioms Zeta23.CCM.analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
#print axioms Zeta23.CCM.analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
#print axioms Zeta23.CCM.isOpen_liftedFrozenPredecessorDomain
#print axioms Zeta23.CCM.add_two_pi_I_mem_liftedFrozenPredecessorDomain_iff
#print axioms Zeta23.CCM.analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
