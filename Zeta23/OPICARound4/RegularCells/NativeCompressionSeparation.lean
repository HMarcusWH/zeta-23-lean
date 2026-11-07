import Zeta23.OPICARound4.RegularCells.NativeDiagonalSeparation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section

namespace Zeta23.OPICARound4.NativeParitySeparation

open scoped BigOperators ComplexConjugate

def nativeConstantVector (K : ℕ) : EuclideanSpace ℂ (Fin K) :=
  WithLp.toLp 2 (fun _ => 1)

def nativeIndexVector (K : ℕ) : EuclideanSpace ℂ (Fin K) :=
  WithLp.toLp 2 (fun i => (i.val + 1 : ℂ))

def nativeSquareVector (K : ℕ) : EuclideanSpace ℂ (Fin K) :=
  WithLp.toLp 2 (fun i => (i.val + 1 : ℂ) ^ 2)

def nativeReciprocalVector (K : ℕ) : EuclideanSpace ℂ (Fin K) :=
  WithLp.toLp 2 (fun i => (i.val + 1 : ℂ)⁻¹)

/-- Actual positive-coordinate limiting even carrier, with the inherited norm. -/
def nativeLimitingEvenCarrier (K : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin K)) :=
  (Submodule.span ℂ ({nativeConstantVector K, nativeSquareVector K} :
    Set (EuclideanSpace ℂ (Fin K))))ᗮ

/-- Actual positive-coordinate limiting odd carrier, with the inherited norm. -/
def nativeLimitingOddCarrier (K : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin K)) :=
  (Submodule.span ℂ ({nativeReciprocalVector K, nativeIndexVector K} :
    Set (EuclideanSpace ℂ (Fin K))))ᗮ

def nativeSquaredIndexDiagonal (K : ℕ) :
    Module.End ℂ (EuclideanSpace ℂ (Fin K)) :=
  (Matrix.diagonal (fun i : Fin K => (i.val + 1 : ℂ) ^ 2)).toEuclideanLin

def nativeSquaredIndexCompression (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin K))) : Module.End ℂ S :=
  S.orthogonalProjectionOnto.toLinearMap.comp ((nativeSquaredIndexDiagonal K).comp S.subtype)

private theorem compression_eigen_normal_pair
    {K : ℕ} (u v : EuclideanSpace ℂ (Fin K))
    (T : Module.End ℂ (EuclideanSpace ℂ (Fin K))) (lam : ℂ)
    (x : (Submodule.span ℂ ({u, v} : Set (EuclideanSpace ℂ (Fin K))))ᗮ)
    (hx : (Submodule.span ℂ ({u, v} : Set (EuclideanSpace ℂ (Fin K))))ᗮ.orthogonalProjectionOnto
      (T x) = lam • x) :
    ∃ c d : ℂ, T x - lam • (x : EuclideanSpace ℂ (Fin K)) = c • u + d • v := by
  let S := Submodule.span ℂ ({u, v} : Set (EuclideanSpace ℂ (Fin K)))
  have hproj : Sᗮ.starProjection (T x) = lam • (x : EuclideanSpace ℂ (Fin K)) :=
    congrArg (fun z : Sᗮ => (z : EuclideanSpace ℂ (Fin K))) hx
  have hm := Sᗮ.sub_starProjection_mem_orthogonal (T x)
  rw [hproj, Submodule.orthogonal_orthogonal] at hm
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hm
  exact ⟨c, d, hcd.symm⟩

/-- Operator-level noncollision for the actual two limiting parity carriers.
The orthogonal projections themselves supply every normal residual in the
finite algebra theorem; no residual-span premise is left to the caller. -/
theorem native_limiting_compressed_squared_index_no_common_eigenvalue
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (x : nativeLimitingEvenCarrier K) (y : nativeLimitingOddCarrier K)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxe : nativeSquaredIndexCompression K (nativeLimitingEvenCarrier K) x = (lam : ℂ) • x)
    (hyo : nativeSquaredIndexCompression K (nativeLimitingOddCarrier K) y = (lam : ℂ) • y) :
    False := by
  have hx0 : ∑ i, x.val i = 0 := by
    have h := (Submodule.mem_orthogonal _ _).mp x.property (nativeConstantVector K)
      (Submodule.subset_span (by simp))
    simpa [nativeConstantVector, PiLp.inner_apply] using h
  have hx2 : ∑ i, (i.val + 1 : ℂ) ^ 2 * x.val i = 0 := by
    have h := (Submodule.mem_orthogonal _ _).mp x.property (nativeSquareVector K)
      (Submodule.subset_span (by simp))
    simpa [nativeSquareVector, PiLp.inner_apply, mul_comm] using h
  have hyinv : ∑ i, y.val i / (i.val + 1 : ℂ) = 0 := by
    have h := (Submodule.mem_orthogonal _ _).mp y.property (nativeReciprocalVector K)
      (Submodule.subset_span (by simp))
    simpa [nativeReciprocalVector, PiLp.inner_apply, div_eq_mul_inv, mul_comm] using h
  have hy1 : ∑ i, (i.val + 1 : ℂ) * y.val i = 0 := by
    have h := (Submodule.mem_orthogonal _ _).mp y.property (nativeIndexVector K)
      (Submodule.subset_span (by simp))
    simpa [nativeIndexVector, PiLp.inner_apply, mul_comm] using h
  have hxf : (fun i => x.val i) ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    apply PiLp.ext
    intro i
    exact congrFun h i
  have hyf : (fun i => y.val i) ≠ 0 := by
    intro h
    apply hy
    apply Subtype.ext
    apply PiLp.ext
    intro i
    exact congrFun h i
  obtain ⟨c, d, hcd⟩ := compression_eigen_normal_pair
    (nativeConstantVector K) (nativeSquareVector K) (nativeSquaredIndexDiagonal K)
    (lam : ℂ) x hxe
  obtain ⟨e, f, hef⟩ := compression_eigen_normal_pair
    (nativeReciprocalVector K) (nativeIndexVector K) (nativeSquaredIndexDiagonal K)
    (lam : ℂ) y hyo
  apply native_squared_index_compressions_disjoint K hK lam
    (fun i => x.val i) (fun i => y.val i) hxf hyf hx0 hx2 hyinv hy1 c d e f
  · intro i
    have hi := congrArg (fun w : EuclideanSpace ℂ (Fin K) => w i) hcd
    simp [nativeSquaredIndexDiagonal, Matrix.toLpLin_apply, Matrix.mulVec_diagonal,
      nativeConstantVector, nativeSquareVector] at hi
    linear_combination hi
  · intro i
    have hi := congrArg (fun w : EuclideanSpace ℂ (Fin K) => w i) hef
    simp [nativeSquaredIndexDiagonal, Matrix.toLpLin_apply, Matrix.mulVec_diagonal,
      nativeReciprocalVector, nativeIndexVector, div_eq_mul_inv] at hi
    linear_combination hi

end Zeta23.OPICARound4.NativeParitySeparation
