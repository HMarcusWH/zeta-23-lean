import Zeta23.CCM.CubicNormalizedSchur

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A3c: source-explicit cubic defect

The rank-one parity-defect coefficient from PR #112 is canonical, but its
existing definition is an output coordinate of the compressed D-intertwining
defect.  This module identifies that coefficient directly on the source side.

Inside the exact even normal plane `span{1,d^2}`, orthogonalize `d^2` against
the constant normal direction and call the result `n₂`.  For `K >= 2`, the
coefficient of the surviving cubic channel is exactly

  <n₂, M v> / <n₂,n₂>

for every even boundary-flat vector `v`, where `M` is the canonical source
matrix at the same finite size.

Firewalls:
* the matrix is `canonicalSourceMatrix`, not the legacy identity-shifted matrix;
* no sign or nonzeroness is asserted for the source moment on a particular
  trial/eigenvector;
* this is a finite canonical source identity only;
* no branch exclusion, positivity closure, finite-to-infinite closure, or RH
  theorem is claimed.
-/

/-- Constant-direction-normalized quadratic normal vector.  The definition is
made in the ambient Euclidean carrier because the even normal plane is an
ambient orthogonal complement. -/
def centeredQuadraticNormal
    (K : ℕ) : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  centeredPowerVector K 2 -
    (inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 2) /
      inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 0)) •
        centeredPowerVector K 0

/-- The constant centered-power vector has nonzero self inner product. -/
theorem inner_centeredPowerVector_zero_self_ne_zero
    (K : ℕ) :
    inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 0) ≠ 0 := by
  have hvec : centeredPowerVector K 0 ≠ 0 := by
    intro hzero
    have hcoord := congrArg
      (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) =>
        x (boundaryFlatZeroIndex K)) hzero
    simp [centeredPowerVector_apply] at hcoord
  intro hinner
  apply hvec
  exact inner_self_eq_zero.mp hinner

/-- By construction, `n₂` is orthogonal to the constant normal direction. -/
theorem inner_centeredPowerVector_zero_centeredQuadraticNormal_eq_zero
    (K : ℕ) :
    inner ℂ (centeredPowerVector K 0) (centeredQuadraticNormal K) = 0 := by
  have hden := inner_centeredPowerVector_zero_self_ne_zero K
  unfold centeredQuadraticNormal
  rw [inner_sub_right, inner_smul_right]
  field_simp [hden]

/-- Symmetric orientation of the constant/quadratic orthogonality identity. -/
theorem inner_centeredQuadraticNormal_centeredPowerVector_zero_eq_zero
    (K : ℕ) :
    inner ℂ (centeredQuadraticNormal K) (centeredPowerVector K 0) = 0 := by
  rw [inner_eq_zero_symm]
  exact inner_centeredPowerVector_zero_centeredQuadraticNormal_eq_zero K

/-- `n₂` remains inside the exact even normal plane `span{1,d²}`. -/
theorem centeredQuadraticNormal_mem_evenNormalSubspace
    (K : ℕ) :
    centeredQuadraticNormal K ∈ evenNormalSubspace K := by
  unfold centeredQuadraticNormal evenNormalSubspace
  apply Submodule.sub_mem
  · exact
      (show ℂ ∙ centeredPowerVector K 2 ≤
          (ℂ ∙ centeredPowerVector K 0) ⊔
            (ℂ ∙ centeredPowerVector K 2) from le_sup_right)
        (Submodule.mem_span_singleton_self (centeredPowerVector K 2))
  · exact Submodule.smul_mem _ _
      ((show ℂ ∙ centeredPowerVector K 0 ≤
          (ℂ ∙ centeredPowerVector K 0) ⊔
            (ℂ ∙ centeredPowerVector K 2) from le_sup_left)
        (Submodule.mem_span_singleton_self (centeredPowerVector K 0)))

/-- Hence `n₂` is orthogonal to every even boundary-flat vector. -/
theorem centeredQuadraticNormal_mem_evenBoundaryFlat_orthogonal
    (K : ℕ) :
    centeredQuadraticNormal K ∈
      (euclideanEvenBoundaryFlatSubspace K)ᗮ :=
  evenNormalSubspace_le_evenBoundaryFlat_orthogonal K
    (centeredQuadraticNormal_mem_evenNormalSubspace K)

/-- For every nontrivial grid the quadratic normal is genuinely nonzero. -/
theorem centeredQuadraticNormal_ne_zero
    (K : ℕ) (hK : 1 ≤ K) :
    centeredQuadraticNormal K ≠ 0 := by
  intro hzero
  let i0 := boundaryFlatZeroIndex K
  let i1 : Fin (2 * K + 1) := ⟨K + 1, by omega⟩
  have hi0 : centeredIndex K i0 = 0 := by
    simp [i0]
  have hi1 : centeredIndex K i1 = 1 := by
    simp [i1, centeredIndex]
  have hcenter := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) => x i0) hzero
  have hone := congrArg
    (fun x : EuclideanSpace ℂ (Fin (2 * K + 1)) => x i1) hzero
  have hmu :
      inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 2) /
          inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 0) = 0 := by
    simpa [centeredQuadraticNormal, centeredPowerVector_apply, hi0, i0,
      Pi.smul_apply, smul_eq_mul] using hcenter
  simp [centeredQuadraticNormal, centeredPowerVector_apply, hi1, hmu,
    Pi.smul_apply, smul_eq_mul] at hone

/-- The quadratic normal therefore has nonzero self inner product. -/
theorem inner_centeredQuadraticNormal_self_ne_zero
    (K : ℕ) (hK : 1 ≤ K) :
    inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) ≠ 0 := by
  intro hinner
  apply centeredQuadraticNormal_ne_zero K hK
  exact inner_self_eq_zero.mp hinner

/-- Pairing `n₂` with `d²` is the same as pairing it with itself, since the
difference is a constant normal direction. -/
theorem inner_centeredQuadraticNormal_centeredPowerVector_two_eq_self
    (K : ℕ) :
    inner ℂ (centeredQuadraticNormal K) (centeredPowerVector K 2) =
      inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) := by
  let mu : ℂ :=
    inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 2) /
      inner ℂ (centeredPowerVector K 0) (centeredPowerVector K 0)
  have hdecomp :
      centeredPowerVector K 2 =
        centeredQuadraticNormal K + mu • centeredPowerVector K 0 := by
    dsimp [mu]
    unfold centeredQuadraticNormal
    abel
  rw [hdecomp, inner_add_right, inner_smul_right,
    inner_centeredQuadraticNormal_centeredPowerVector_zero_eq_zero]
  simp

/-- Canonical finite source moment in the even quadratic normal channel. -/
def evenQuadraticSourceMoment
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  inner ℂ (centeredQuadraticNormal K)
      ((canonicalSourceMatrix L K).toEuclideanLin
        (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) /
    inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)

/-- The coefficient selected from an explicit normal-space decomposition is
exactly the source moment. -/
theorem evenQuadraticSourceMoment_eq_evenCompressionResidual_a2
    (L : ℝ) (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (a0 a2 : ℂ)
    (hres :
      (canonicalSourceMatrix L K).toEuclideanLin
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) =
        (evenCompressedCanonical L K v :
          EuclideanSpace ℂ (Fin (2 * K + 1))) +
        a0 • centeredPowerVector K 0 +
        a2 • centeredPowerVector K 2) :
    evenQuadraticSourceMoment L K v = a2 := by
  let n2 := centeredQuadraticNormal K
  have hnorth := centeredQuadraticNormal_mem_evenBoundaryFlat_orthogonal K
  have hTv0 :
      inner ℂ n2
          (evenCompressedCanonical L K v :
            EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
    rw [inner_eq_zero_symm]
    exact
      ((euclideanEvenBoundaryFlatSubspace K).mem_orthogonal n2).mp
        hnorth
        (evenCompressedCanonical L K v :
          EuclideanSpace ℂ (Fin (2 * K + 1)))
        (evenCompressedCanonical L K v).property
  have hn20 :
      inner ℂ n2 (centeredPowerVector K 0) = 0 := by
    simpa [n2] using
      inner_centeredQuadraticNormal_centeredPowerVector_zero_eq_zero K
  have hn22 :
      inner ℂ n2 (centeredPowerVector K 2) = inner ℂ n2 n2 := by
    simpa [n2] using
      inner_centeredQuadraticNormal_centeredPowerVector_two_eq_self K
  have hmoment := congrArg
    (fun y : EuclideanSpace ℂ (Fin (2 * K + 1)) => inner ℂ n2 y) hres
  simp only [inner_add_right, inner_smul_right] at hmoment
  rw [hTv0, hn20, hn22] at hmoment
  simp only [zero_add, mul_zero, add_zero] at hmoment
  have hden : inner ℂ n2 n2 ≠ 0 := by
    simpa [n2] using inner_centeredQuadraticNormal_self_ne_zero K hK
  unfold evenQuadraticSourceMoment
  change
    inner ℂ n2
        ((canonicalSourceMatrix L K).toEuclideanLin
          (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) /
      inner ℂ n2 n2 = a2
  rw [hmoment]
  exact mul_div_cancel_right₀ a2 hden

/-- Re-run the already validated parity-defect calculation on a fixed explicit
`a0,a2` decomposition so the same `a2` is connected to the canonical defect
functional rather than merely to an existential coefficient. -/
theorem cubicDefectFunctional_eq_evenCompressionResidual_a2
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (a0 a2 : ℂ)
    (hres :
      (canonicalSourceMatrix L K).toEuclideanLin
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) =
        (evenCompressedCanonical L K v :
          EuclideanSpace ℂ (Fin (2 * K + 1))) +
        a0 • centeredPowerVector K 0 +
        a2 • centeredPowerVector K 2) :
    cubicDefectFunctional L K v = a2 := by
  have hDres := congrArg (euclideanIndexLinearMap K) hres
  have hDres' :
      euclideanIndexLinearMap K
          ((canonicalSourceMatrix L K).toEuclideanLin
            (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        euclideanIndexLinearMap K
            (evenCompressedCanonical L K v :
              EuclideanSpace ℂ (Fin (2 * K + 1))) +
          a0 • centeredPowerVector K 1 +
          a2 • centeredPowerVector K 3 := by
    simpa [map_add, map_smul,
      euclideanIndexLinearMap_centeredPowerVector,
      add_assoc] using hDres
  have hMD :
      (canonicalSourceMatrix L K).toEuclideanLin
          ((euclideanEvenToOddIndexLinearMap K v :
              euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1))) =
        euclideanIndexLinearMap K
            (evenCompressedCanonical L K v :
              EuclideanSpace ℂ (Fin (2 * K + 1))) +
          a0 • centeredPowerVector K 1 +
          a2 • centeredPowerVector K 3 := by
    rw [coe_euclideanEvenToOddIndexLinearMap,
      canonicalSourceMatrix_toEuclideanLin_commutes_index_on_even hL K v]
    exact hDres'
  have hp1 :
      (euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto
          (centeredPowerVector K 1) = 0 := by
    exact
      ((euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto_eq_zero_iff).2
        (centeredPowerVector_one_mem_oddBoundaryFlat_orthogonal K)
  have hproj' :
      oddCompressedCanonical L K
          (euclideanEvenToOddIndexLinearMap K v) =
        euclideanEvenToOddIndexLinearMap K
            (evenCompressedCanonical L K v) +
          a2 • oddCubicCompressionVector K := by
    change
      (euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto
          ((canonicalSourceMatrix L K).toEuclideanLin
            ((euclideanEvenToOddIndexLinearMap K v :
                euclideanOddBoundaryFlatSubspace K) :
              EuclideanSpace ℂ (Fin (2 * K + 1)))) =
        euclideanEvenToOddIndexLinearMap K
            (evenCompressedCanonical L K v) +
          a2 • oddCubicCompressionVector K
    rw [hMD]
    simp only [map_add, map_smul]
    have hindex :
        euclideanIndexLinearMap K
            (evenCompressedCanonical L K v :
              EuclideanSpace ℂ (Fin (2 * K + 1))) =
          ((euclideanEvenToOddIndexLinearMap K
              (evenCompressedCanonical L K v) :
                euclideanOddBoundaryFlatSubspace K) :
            EuclideanSpace ℂ (Fin (2 * K + 1))) :=
      (coe_euclideanEvenToOddIndexLinearMap K
        (evenCompressedCanonical L K v)).symm
    rw [hindex, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, hp1]
    simp [oddCubicCompressionVector, add_assoc]
  have hdef :
      evenOddCompressedIntertwiningDefect L K v =
        a2 • oddCubicCompressionVector K := by
    change
      oddCompressedCanonical L K
          (euclideanEvenToOddIndexLinearMap K v) -
        euclideanEvenToOddIndexLinearMap K
          (evenCompressedCanonical L K v) =
        a2 • oddCubicCompressionVector K
    rw [hproj']
    abel
  have hfac :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL K hK v
  have heq :
      a2 • oddCubicCompressionVector K =
        cubicDefectFunctional L K v • oddCubicCompressionVector K :=
    hdef.symm.trans hfac
  have hg : oddCubicCompressionVector K ≠ 0 :=
    oddCubicCompressionVector_ne_zero K hK
  have hgg :
      inner ℂ (oddCubicCompressionVector K) (oddCubicCompressionVector K) ≠ 0 := by
    intro hinner
    apply hg
    exact inner_self_eq_zero.mp hinner
  have hcoeff := congrArg
    (fun y : euclideanOddBoundaryFlatSubspace K =>
      inner ℂ (oddCubicCompressionVector K) y) heq
  rw [inner_smul_right, inner_smul_right] at hcoeff
  apply Eq.symm
  apply (mul_right_cancel₀ hgg)
  exact hcoeff.symm

/-- Main source-explicit endpoint: the canonical cubic parity-defect functional
is exactly the actual canonical-source quadratic normal moment. -/
theorem cubicDefectFunctional_eq_evenQuadraticSourceMoment
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    cubicDefectFunctional L K v = evenQuadraticSourceMoment L K v := by
  obtain ⟨a0, a2, hres⟩ :=
    exists_evenCompressionResidual_coefficients L K v
  have hsource :=
    evenQuadraticSourceMoment_eq_evenCompressionResidual_a2
      L K (by omega) v a0 a2 hres
  have hdefect :=
    cubicDefectFunctional_eq_evenCompressionResidual_a2
      hL K hK v a0 a2 hres
  exact hdefect.trans hsource.symm

end Zeta23.CCM

#print axioms Zeta23.CCM.centeredQuadraticNormal_ne_zero
#print axioms Zeta23.CCM.cubicDefectFunctional_eq_evenCompressionResidual_a2
#print axioms Zeta23.CCM.cubicDefectFunctional_eq_evenQuadraticSourceMoment
