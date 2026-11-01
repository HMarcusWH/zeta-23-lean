import Zeta23.OPICARound4.RegularCells.NativeCompressionSeparation
import Zeta23.OPICARound4.RegularCells.SylvesterSeparation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Hermitian

noncomputable section
namespace Zeta23.OPICARound4.NativeParitySeparation

open Module.End Filter
open scoped BigOperators ComplexConjugate Topology

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup

def nativeWeightedCompression (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin K))) (q : Fin K → ℂ) : S →L[ℂ] S :=
  LinearMap.toContinuousLinearMap
    (S.orthogonalProjectionOnto.toLinearMap.comp
      ((Matrix.diagonal q).toEuclideanLin.comp S.subtype))

theorem nativeWeightedCompression_isSymmetric (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin K))) (q : Fin K → ℂ)
    (hq : ∀ i, conj (q i) = q i) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := S)
      (nativeWeightedCompression K S q).toLinearMap := by
  have hd : (Matrix.diagonal q).toEuclideanLin.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.isHermitian_diagonal_iff.mpr
    simpa [isSelfAdjoint_iff] using hq
  intro x y
  change inner ℂ (S.orthogonalProjectionOnto ((Matrix.diagonal q).toEuclideanLin x)) y =
    inner ℂ x (S.orthogonalProjectionOnto ((Matrix.diagonal q).toEuclideanLin y))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hd x y

private def weightedHomOperator (K : ℕ) (q : Fin K → ℂ) :
    Module.End ℂ (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K) where
  toFun X := (nativeWeightedCompression K (nativeLimitingOddCarrier K) q).comp X -
    X.comp (nativeWeightedCompression K (nativeLimitingEvenCarrier K) q)
  map_add' X Y := by ext x; simp [sub_eq_add_neg]; abel
  map_smul' c X := by ext x; simp [smul_sub]

private theorem weightedCompression_add (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin K))) (q r : Fin K → ℂ) :
    nativeWeightedCompression K S (q + r) =
      nativeWeightedCompression K S q + nativeWeightedCompression K S r := by
  apply ContinuousLinearMap.ext
  intro x
  change S.orthogonalProjectionOnto ((Matrix.diagonal (q + r)).toEuclideanLin x) =
    S.orthogonalProjectionOnto ((Matrix.diagonal q).toEuclideanLin x) +
    S.orthogonalProjectionOnto ((Matrix.diagonal r).toEuclideanLin x)
  rw [show Matrix.diagonal (q + r) = Matrix.diagonal q + Matrix.diagonal r from
    (Matrix.diagonal_add q r).symm, map_add, LinearMap.add_apply, map_add]

def nativeWeightedSylvester (K : ℕ) (q : Fin K → ℂ) :
    (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K) →L[ℂ]
      (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K) :=
  LinearMap.toContinuousLinearMap (weightedHomOperator K q)

private def weightedSylvesterLinear (K : ℕ) :
    (Fin K → ℂ) →ₗ[ℂ]
      ((nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K) →L[ℂ]
        (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K)) where
  toFun := nativeWeightedSylvester K
  map_add' q r := by
    apply ContinuousLinearMap.ext
    intro X
    apply ContinuousLinearMap.ext
    intro x
    change nativeWeightedCompression K _ (q + r) (X x) -
      X (nativeWeightedCompression K _ (q + r) x) = _
    rw [weightedCompression_add, weightedCompression_add]
    change _ = (nativeWeightedCompression K _ q (X x) -
      X (nativeWeightedCompression K _ q x)) +
      (nativeWeightedCompression K _ r (X x) - X (nativeWeightedCompression K _ r x))
    simp only [map_add, add_apply]
    abel
  map_smul' c q := by
    ext X x
    simp [nativeWeightedSylvester, weightedHomOperator, nativeWeightedCompression,
      Matrix.diagonal_smul, map_smul, smul_sub]

theorem continuous_nativeWeightedSylvester (K : ℕ) : Continuous (nativeWeightedSylvester K) :=
  show Continuous (weightedSylvesterLinear K) from
    LinearMap.continuous_of_finiteDimensional (𝕜 := ℂ) (E := Fin K → ℂ)
      (F' := (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K) →L[ℂ]
        (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K))
      (weightedSylvesterLinear K)

def nativeWeightedSeparationDet (K : ℕ) (q : Fin K → ℂ) : ℂ :=
  (nativeWeightedSylvester K q).det

theorem continuous_nativeWeightedSeparationDet (K : ℕ) :
    Continuous (nativeWeightedSeparationDet K) := by
  change Continuous (fun q => (nativeWeightedSylvester K q).det)
  exact (ContinuousLinearMap.continuous_det (𝕜 := ℂ)
    (E := nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K)).comp
      (continuous_nativeWeightedSylvester K)

private theorem weightedSquared_disjoint (K : ℕ) (hK : 3 ≤ K) :
    ∀ lam : ℂ,
      HasEigenvalue (nativeWeightedCompression K (nativeLimitingEvenCarrier K)
        (fun i => (i.val + 1 : ℂ) ^ 2)).toLinearMap lam →
      ¬ HasEigenvalue (nativeWeightedCompression K (nativeLimitingOddCarrier K)
        (fun i => (i.val + 1 : ℂ) ^ 2)).toLinearMap lam := by
  let q : Fin K → ℂ := fun i => (i.val + 1 : ℂ) ^ 2
  let A := (nativeWeightedCompression K (nativeLimitingEvenCarrier K) q).toLinearMap
  let B := (nativeWeightedCompression K (nativeLimitingOddCarrier K) q).toLinearMap
  have hA : LinearMap.IsSymmetric (𝕜 := ℂ) (E := nativeLimitingEvenCarrier K) A :=
    nativeWeightedCompression_isSymmetric K _ q (by intro i; simp [q])
  change ∀ lam : ℂ, HasEigenvalue A lam → ¬ HasEigenvalue B lam
  intro lam hae hbo
  obtain ⟨x, hxe, hx⟩ := hae.exists_hasEigenvector
  obtain ⟨y, hyo, hy⟩ := hbo.exists_hasEigenvector
  have hr : (lam.re : ℂ) = lam := RCLike.conj_eq_iff_re.mp (hA.conj_eigenvalue_eq_self hae)
  apply native_limiting_compressed_squared_index_no_common_eigenvalue K hK lam.re x y hx hy
  · rw [hr]
    exact mem_eigenspace_iff.mp hxe
  · rw [hr]
    exact mem_eigenspace_iff.mp hyo
private theorem clm_det_nezero_of_sylvester
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (T : (E →L[ℂ] F) →L[ℂ] (E →L[ℂ] F))
    (hT : ∀ X x, T X x = B (X x) - X (A x))
    (hinj : Function.Injective (nativeSylvester A B)) : T.det ≠ 0 := by
  change LinearMap.det T.toLinearMap ≠ 0
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  have hxlin : X.toLinearMap = 0 := by
    apply hinj
    rw [map_zero]
    ext x
    have h := congrArg (fun Y : E →L[ℂ] F => Y x) hX
    change T X x = 0 at h
    rw [hT] at h
    exact h
  ext x
  exact congrArg (fun Y : E →ₗ[ℂ] F => Y x) hxlin

theorem nativeWeightedSeparationDet_squared_ne_zero (K : ℕ) (hK : 3 ≤ K) :
    nativeWeightedSeparationDet K (fun i => (i.val + 1 : ℂ) ^ 2) ≠ 0 := by
  unfold nativeWeightedSeparationDet
  apply clm_det_nezero_of_sylvester
    (E := nativeLimitingEvenCarrier K) (F := nativeLimitingOddCarrier K)
    (nativeWeightedCompression K (nativeLimitingEvenCarrier K)
      (fun i => (i.val + 1 : ℂ) ^ 2)).toLinearMap
    (nativeWeightedCompression K (nativeLimitingOddCarrier K)
      (fun i => (i.val + 1 : ℂ) ^ 2)).toLinearMap
    (nativeWeightedSylvester K (fun i => (i.val + 1 : ℂ) ^ 2)) (by intros; rfl)
  exact nativeSylvester_injective_of_disjoint _ _
    (nativeWeightedCompression_isSymmetric K _ _ (by intro i; simp))
    (weightedSquared_disjoint K hK)

def nativeScaledCosineWeights (K : ℕ) (theta : ℝ) (i : Fin K) : ℂ :=
  ((((i.val : ℝ) + 1) ^ 2 * Real.sinc (((i.val : ℝ) + 1) * theta / 2) ^ 2 : ℝ) : ℂ)

theorem continuous_nativeScaledCosineWeights (K : ℕ) :
    Continuous (nativeScaledCosineWeights K) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_const.mul
    ((Real.continuous_sinc.comp ((continuous_const.mul continuous_id).div_const 2)).pow 2))

theorem nativeScaledCosineWeights_zero (K : ℕ) :
    nativeScaledCosineWeights K 0 = fun i => (i.val + 1 : ℂ) ^ 2 := by
  funext i
  simp [nativeScaledCosineWeights]

/-- The actual scaled cosine compression has nonzero separation determinant
throughout a neighborhood of zero, with its value at zero supplied by the
unconditional all-cutoff diagonal theorem. -/
theorem eventually_nativeScaledCosine_separation (K : ℕ) (hK : 3 ≤ K) :
    ∀ᶠ theta in 𝓝 (0 : ℝ),
      nativeWeightedSeparationDet K (nativeScaledCosineWeights K theta) ≠ 0 := by
  have hc := (continuous_nativeWeightedSeparationDet K).comp
    (continuous_nativeScaledCosineWeights K)
  apply hc.continuousAt.eventually_ne
  change nativeWeightedSeparationDet K (nativeScaledCosineWeights K 0) ≠ 0
  rw [nativeScaledCosineWeights_zero]
  exact nativeWeightedSeparationDet_squared_ne_zero K hK


private theorem real_cos_sinc_identity (u : ℝ) :
    Real.cos u = 1 - u ^ 2 / 2 * Real.sinc (u / 2) ^ 2 := by
  have hs : (u / 2) * Real.sinc (u / 2) = Real.sin (u / 2) := by
    by_cases hu : u / 2 = 0
    · simp [hu]
    · rw [Real.sinc_of_ne_zero hu]
      have hu0 : u ≠ 0 := by
        intro h
        apply hu
        simp [h]
      field_simp [hu0]
  have hc := Real.cos_two_mul (u / 2)
  have ht := Real.sin_sq_add_cos_sq (u / 2)
  have hs2 := congrArg (fun z : ℝ => z ^ 2) hs
  have he : 2 * (u / 2) = u := by ring
  rw [he] at hc
  nlinarith

def nativeCosineWeights (K : ℕ) (theta : ℝ) (i : Fin K) : ℂ :=
  (Real.cos (((i.val : ℝ) + 1) * theta) : ℂ)

theorem nativeCosineWeights_affine (K : ℕ) (theta : ℝ) :
    nativeCosineWeights K theta = (fun _ => 1) +
      (-(theta : ℂ) ^ 2 / 2) • nativeScaledCosineWeights K theta := by
  funext i
  simp only [nativeCosineWeights, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    nativeScaledCosineWeights]
  rw [real_cos_sinc_identity]
  push_cast
  ring

private theorem nativeWeightedCompression_const (K : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin K))) (c : ℂ) :
    nativeWeightedCompression K S (fun _ => c) = c • ContinuousLinearMap.id ℂ S := by
  apply ContinuousLinearMap.ext
  intro x
  change S.orthogonalProjectionOnto ((Matrix.diagonal (fun _ => c)).toEuclideanLin x) = c • x
  have hd : (Matrix.diagonal (fun _ : Fin K => c)).toEuclideanLin (x : EuclideanSpace ℂ (Fin K)) =
      c • (x : EuclideanSpace ℂ (Fin K)) := by
    ext i
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.diagonal_const_mulVec]
  rw [hd, map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem nativeWeightedSylvester_const (K : ℕ) (c : ℂ) :
    nativeWeightedSylvester K (fun _ => c) = 0 := by
  apply ContinuousLinearMap.ext
  intro X
  apply ContinuousLinearMap.ext
  intro x
  change (nativeWeightedCompression K (nativeLimitingOddCarrier K) (fun _ => c)) (X x) -
    X ((nativeWeightedCompression K (nativeLimitingEvenCarrier K) (fun _ => c)) x) = 0
  rw [nativeWeightedCompression_const, nativeWeightedCompression_const]
  simp

theorem nativeWeightedSylvester_cosine (K : ℕ) (theta : ℝ) :
    nativeWeightedSylvester K (nativeCosineWeights K theta) =
      (-(theta : ℂ) ^ 2 / 2) •
        nativeWeightedSylvester K (nativeScaledCosineWeights K theta) := by
  rw [nativeCosineWeights_affine]
  change weightedSylvesterLinear K ((fun _ => 1) +
    (-(theta : ℂ) ^ 2 / 2) • nativeScaledCosineWeights K theta) = _
  rw [map_add, map_smul]
  change nativeWeightedSylvester K (fun _ => 1) + _ = _
  apply ContinuousLinearMap.ext
  intro X
  apply ContinuousLinearMap.ext
  intro x
  change nativeWeightedSylvester K (fun _ => 1) X x +
    (-(theta : ℂ) ^ 2 / 2) • nativeWeightedSylvester K (nativeScaledCosineWeights K theta) X x = _
  rw [nativeWeightedSylvester_const]
  exact zero_add _

theorem nativeWeightedSeparationDet_cosine (K : ℕ) (theta : ℝ) :
    nativeWeightedSeparationDet K (nativeCosineWeights K theta) =
      (-(theta : ℂ) ^ 2 / 2) ^
        Module.finrank ℂ (nativeLimitingEvenCarrier K →L[ℂ] nativeLimitingOddCarrier K) *
      nativeWeightedSeparationDet K (nativeScaledCosineWeights K theta) := by
  unfold nativeWeightedSeparationDet
  rw [nativeWeightedSylvester_cosine]
  exact LinearMap.det_smul _ _

theorem eventually_nativeCosine_separation (K : ℕ) (hK : 3 ≤ K) :
    ∀ᶠ theta in 𝓝 (0 : ℝ), theta ≠ 0 →
      nativeWeightedSeparationDet K (nativeCosineWeights K theta) ≠ 0 := by
  filter_upwards [eventually_nativeScaledCosine_separation K hK] with theta htheta hzero
  rw [nativeWeightedSeparationDet_cosine]
  apply mul_ne_zero _ htheta
  apply pow_ne_zero
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hzero)))
    (by norm_num)


private theorem linear_injective_of_clm_sylvester
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (T : (E →L[ℂ] F) →L[ℂ] (E →L[ℂ] F))
    (hT : ∀ X x, T X x = B (X x) - X (A x)) (hdet : T.det ≠ 0) :
    Function.Injective (nativeSylvester A B) := by
  change LinearMap.det T.toLinearMap ≠ 0 at hdet
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot] at hdet
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  have hc : T X.toContinuousLinearMap = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    rw [hT]
    have h := congrArg (fun Y : E →ₗ[ℂ] F => Y x) hX
    exact h
  have hz : X.toContinuousLinearMap = 0 := by
    apply hdet
    change T X.toContinuousLinearMap = T 0
    rw [map_zero]
    exact hc
  ext x
  exact congrArg (fun Y : E →L[ℂ] F => Y x) hz

theorem nativeWeightedSeparationDet_injective (K : ℕ) (q : Fin K → ℂ)
    (hdet : nativeWeightedSeparationDet K q ≠ 0) :
    Function.Injective (nativeSylvester
      (E := nativeLimitingEvenCarrier K) (F := nativeLimitingOddCarrier K)
      (nativeWeightedCompression K (nativeLimitingEvenCarrier K) q).toLinearMap
      (nativeWeightedCompression K (nativeLimitingOddCarrier K) q).toLinearMap) := by
  apply linear_injective_of_clm_sylvester
    (E := nativeLimitingEvenCarrier K) (F := nativeLimitingOddCarrier K)
    _ _ (nativeWeightedSylvester K q) (by intros; rfl)
  exact hdet

theorem exists_nativeCosine_separation (K : ℕ) (hK : 3 ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ theta : ℝ, 0 < theta ∧ theta < epsilon ∧
      nativeWeightedSeparationDet K (nativeCosineWeights K theta) ≠ 0 := by
  obtain ⟨delta, hd, hh⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nativeCosine_separation K hK)
  have hm : 0 < min delta epsilon := lt_min hd hepsilon
  have ht : 0 < min delta epsilon / 2 := by positivity
  refine ⟨min delta epsilon / 2, ht, ?_, ?_⟩
  · nlinarith [min_le_right delta epsilon]
  · apply hh _ (ne_of_gt ht)
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    nlinarith [min_le_left delta epsilon]

theorem exists_nativeCosine_sylvester_injective (K : ℕ) (hK : 3 ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ theta : ℝ, 0 < theta ∧ theta < epsilon ∧
      Function.Injective (nativeSylvester
        (E := nativeLimitingEvenCarrier K) (F := nativeLimitingOddCarrier K)
        (nativeWeightedCompression K (nativeLimitingEvenCarrier K)
          (nativeCosineWeights K theta)).toLinearMap
        (nativeWeightedCompression K (nativeLimitingOddCarrier K)
          (nativeCosineWeights K theta)).toLinearMap) := by
  obtain ⟨theta, ht, he, hd⟩ := exists_nativeCosine_separation K hK epsilon hepsilon
  exact ⟨theta, ht, he, nativeWeightedSeparationDet_injective K _ hd⟩

end Zeta23.OPICARound4.NativeParitySeparation
