import Zeta23.OPICARound4.RegularCells.NativeParityPencils
import Zeta23.OPICARound4.RegularCells.NativeCosineSeparation

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells NativeZeroFrame NativeParitySeparation PrimeSourceLaurent
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup

theorem diagonal_rawFrame_zero_even (K : ℕ) (u : zeroCarrier .even K) :
    (physicalDiagonal K 0).toEuclideanLin (rawFrame .even K u) =
      WithLp.toLp 2 (foldLift K 0 u.val.ofLp u.val.ofLp) := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, physicalDiagonal_apply]
  change WithLp.toLp 2 (fixedSeedDiagonal 0 K (rawEvenLift K u.val.ofLp)) = _
  rw [zero_diagonal_rawEvenLift]
  simp only [Complex.ofReal_zero]

theorem diagonal_rawFrame_zero_odd (K : ℕ) (u : zeroCarrier .odd K) :
    (physicalDiagonal K 0).toEuclideanLin (rawFrame .odd K u) =
      WithLp.toLp 2 (foldLift K 0 u.val.ofLp (-u.val.ofLp)) := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, physicalDiagonal_apply]
  change WithLp.toLp 2 (fixedSeedDiagonal 0 K (rawOddLift K u.val.ofLp)) = _
  rw [zero_diagonal_rawOddLift]
  simp only [Complex.ofReal_zero]

theorem diagonal_fold_even (K : ℕ) (c : ℂ) (q x : Fin K → ℂ) :
    (Matrix.diagonal (foldLift K c q q)).toEuclideanLin
      (WithLp.toLp 2 (foldLift K 0 x x)) =
        WithLp.toLp 2 (foldLift K 0 (q*x) (q*x)) := by
  change WithLp.toLp 2 ((Matrix.diagonal (foldLift K c q q)).mulVec _) = _
  congr 1
  apply fold_ext
  · simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  · intro i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  · intro i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem diagonal_fold_odd (K : ℕ) (c : ℂ) (q x : Fin K → ℂ) :
    (Matrix.diagonal (foldLift K c q q)).toEuclideanLin
      (WithLp.toLp 2 (foldLift K 0 x (-x))) =
        WithLp.toLp 2 (foldLift K 0 (q*x) (-(q*x))) := by
  change WithLp.toLp 2 ((Matrix.diagonal (foldLift K c q q)).mulVec _) = _
  congr 1
  apply fold_ext
  · simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  · intro i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  · intro i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem frameEnergy_zero_weighted (p : ReversalParity) (K : ℕ) (c : ℂ) (q : Fin K → ℂ) :
    frameEnergy p K 0 (Matrix.diagonal (foldLift K c q q)) =
      (2 : ℂ) • (nativeWeightedCompression K (zeroCarrier p K) q).toLinearMap := by
  ext x : 1
  apply ext_inner_right ℂ
  intro y
  simp only [frameEnergy, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, physicalDiagonal_real_isSymmetric K 0]
  simp only [Complex.ofReal_zero]
  have hr : inner ℂ ((2 : ℂ) • (nativeWeightedCompression K (zeroCarrier p K) q).toLinearMap x) y =
      2 * inner ℂ ((Matrix.diagonal q).toEuclideanLin x.val) y.val := by
    change inner ℂ ((2 : ℂ) •
      ((nativeWeightedCompression K (zeroCarrier p K) q).toLinearMap x).val) y.val = _
    rw [_root_.inner_smul_left]
    have hc : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_natCast 2
    rw [hc]
    congr 1
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
      (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin K))
      (K := zeroCarrier p K) y ((Matrix.diagonal q).toEuclideanLin x.val)
  change _ = inner ℂ ((2 : ℂ) • (nativeWeightedCompression K (zeroCarrier p K) q).toLinearMap x) y
  rw [hr]
  cases p
  · rw [diagonal_rawFrame_zero_even, diagonal_rawFrame_zero_even, diagonal_fold_even, inner_even_fold]
    congr 2
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  · rw [diagonal_rawFrame_zero_odd, diagonal_rawFrame_zero_odd, diagonal_fold_odd, inner_odd_fold]
    congr 2
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem centered_cosine_eq_fold (K : ℕ) (theta : ℝ) :
    (fun i => (Real.cos ((centeredIndex K i : ℝ) * theta) : ℂ)) =
      foldLift K 1 (nativeCosineWeights K theta) (nativeCosineWeights K theta) := by
  apply fold_ext
  · simp
  · intro i
    simp [nativeCosineWeights]
  · intro i
    simp [nativeCosineWeights]
    rw [← neg_add_rev, neg_mul, Complex.cos_neg]

theorem frameEnergy_zero_cosine (p : ReversalParity) (K : ℕ) (theta : ℝ) :
    frameEnergy p K 0 (Matrix.diagonal
      (fun i => (Real.cos ((centeredIndex K i : ℝ) * theta) : ℂ))) =
      (2 : ℂ) • (nativeWeightedCompression K (zeroCarrier p K)
        (nativeCosineWeights K theta)).toLinearMap := by
  rw [centered_cosine_eq_fold, frameEnergy_zero_weighted]

end Zeta23.OPICARound4.NativeParityPencils
