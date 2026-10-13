import Zeta23.CCM.CanonicalPoleNeutralGeometry

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

-- Expose the canonical inherited subtype structures during elaboration.
-- This changes transparency only; the metric remains the coefficient metric.
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Actual canonical trial residuals and their full signed channel Gram matrix.

The four matrices are the same signed pole, Archimedean, prime, and scalar
channels used by the native observation runner. Their sum is the unchanged
`canonicalSourceMatrix`. Every compression below uses the existing legal
parity carrier, or its native elementary-pole kernel.

This is supporting M14 mathematics: orthogonality, variance, and all complex
cross terms for an arbitrary unit trial vector. A trial vector is not asserted
to be a ground state or a generated detector. No negative depth, spectral gap,
resolvent bound, or RH conclusion is assumed or supplied.
-/

section ResidualAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Complex Rayleigh coefficient, with the mathlib convention that the inner
product is linear in its second argument. -/
def nativeTrialRayleigh (T : E →ₗ[ℂ] E) (u : E) : ℂ := inner ℂ u (T u)

/-- The actual operator residual after removing its component along a unit
trial vector. The definition itself also accepts nonunit vectors. -/
def nativeTrialResidual (T : E →ₗ[ℂ] E) (u : E) : E :=
  T u - nativeTrialRayleigh T u • u

theorem nativeTrialResidual_orthogonal (T : E →ₗ[ℂ] E) (u : E)
    (hu : ‖u‖ = 1) : inner ℂ u (nativeTrialResidual T u) = 0 := by
  have hs : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  simp only [nativeTrialResidual, nativeTrialRayleigh, inner_sub_right,
    inner_smul_right, hs, mul_one, sub_self]

/-- Unit residual variance, valid even before imposing operator symmetry. -/
theorem nativeTrialResidual_variance (T : E →ₗ[ℂ] E) (u : E)
    (hu : ‖u‖ = 1) :
    ‖nativeTrialResidual T u‖ ^ 2 =
      ‖T u‖ ^ 2 - ‖nativeTrialRayleigh T u‖ ^ 2 := by
  have hr : inner ℂ (nativeTrialResidual T u) u = 0 :=
    inner_eq_zero_symm.mp (nativeTrialResidual_orthogonal T u hu)
  have ho : inner ℂ (nativeTrialResidual T u) (nativeTrialRayleigh T u • u) = 0 := by
    rw [inner_smul_right, hr, mul_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (nativeTrialResidual T u) (nativeTrialRayleigh T u • u) ho
  have hsum : nativeTrialResidual T u + nativeTrialRayleigh T u • u = T u := by
    exact sub_add_cancel _ _
  rw [hsum, norm_smul, hu, mul_one] at hp
  linarith

/-- Symmetry makes the actual Rayleigh coefficient real. -/
theorem nativeTrialRayleigh_im_eq_zero (T : E →ₗ[ℂ] E)
    (hT : LinearMap.IsSymmetric T) (u : E) :
    (nativeTrialRayleigh T u).im = 0 := by
  have hs := hT u u
  have hc := inner_conj_symm (𝕜 := ℂ) (T u) u
  have hi := congrArg Complex.im (hc.trans hs)
  simp only [Complex.conj_im] at hi
  change -(nativeTrialRayleigh T u).im = (nativeTrialRayleigh T u).im at hi
  linarith

/-- The spectral second-moment form of the same variance identity. -/
theorem nativeTrialResidual_symmetric_variance (T : E →ₗ[ℂ] E)
    (hT : LinearMap.IsSymmetric T) (u : E) (hu : ‖u‖ = 1) :
    ‖nativeTrialResidual T u‖ ^ 2 =
      (inner ℂ u (T (T u))).re - ‖nativeTrialRayleigh T u‖ ^ 2 := by
  rw [nativeTrialResidual_variance T u hu, norm_sq_eq_re_inner (𝕜 := ℂ),
    hT u (T u), RCLike.re_eq_complex_re]

theorem nativeTrialResidual_sum {ι : Type*} [Fintype ι]
    (C : ι → E →ₗ[ℂ] E) (u : E) :
    nativeTrialResidual (∑ i, C i) u = ∑ i, nativeTrialResidual (C i) u := by
  simp only [nativeTrialResidual, nativeTrialRayleigh, LinearMap.sum_apply,
    inner_sum, Finset.sum_sub_distrib, Finset.sum_smul]

/-- The full complex Gram entry, including phases and off-diagonal terms. -/
def nativeTrialChannelGram {ι : Type*} (C : ι → E →ₗ[ℂ] E)
    (u : E) (i j : ι) : ℂ :=
  inner ℂ (nativeTrialResidual (C i) u) (nativeTrialResidual (C j) u)

/-- The complete Gram sum is the squared residual norm. Retaining only the
diagonal entries would require additional orthogonality which is not assumed. -/
theorem nativeTrialResidual_gram_sum {ι : Type*} [Fintype ι]
    (C : ι → E →ₗ[ℂ] E) (u : E) :
    ‖nativeTrialResidual (∑ i, C i) u‖ ^ 2 =
      (∑ i, ∑ j, nativeTrialChannelGram C u i j).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), nativeTrialResidual_sum,
    RCLike.re_eq_complex_re]
  congr 1
  simp only [sum_inner, inner_sum, nativeTrialChannelGram]
  rw [Finset.sum_comm]

/-- Scalar shifts disappear from the unit trial residual. -/
theorem nativeTrialResidual_add_scalar (T : E →ₗ[ℂ] E) (c : ℂ)
    (u : E) (hu : ‖u‖ = 1) :
    nativeTrialResidual (T + c • LinearMap.id) u = nativeTrialResidual T u := by
  have hs : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  simp only [nativeTrialResidual, nativeTrialRayleigh, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, inner_add_right, inner_smul_right,
    hs, mul_one, add_smul]
  abel

/-- Orthogonal compression, as a linear operation on actual endomorphisms. -/
def nativeOrthogonalCompression (V : Submodule ℂ E) [V.HasOrthogonalProjection] :
    (E →ₗ[ℂ] E) →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun T := V.orthogonalProjectionOnto.toLinearMap.comp (T.comp V.subtype)
  map_add' T U := by ext v; simp
  map_smul' c T := by ext v; simp

theorem nativeOrthogonalCompression_isSymmetric (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] (T : E →ₗ[ℂ] E)
    (hT : LinearMap.IsSymmetric T) :
    LinearMap.IsSymmetric (nativeOrthogonalCompression V T) := by
  intro x y
  change inner ℂ (V.orthogonalProjectionOnto (T x.val)) y =
    inner ℂ x (V.orthogonalProjectionOnto (T y.val))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT x.val y.val

end ResidualAlgebra

/-- The exact scalar matrix used in the native four-channel representation. -/
def canonicalTrialScalarShiftMatrix (L : ℝ) (K : ℕ) :
    Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  ((2 * cCorrection L : ℝ) : ℂ) • 1

/-- Signed native channels in observation-runner order: pole, Archimedean,
prime, scalar shift. The Archimedean channel includes the opposite shift. -/
def signedCanonicalTrialChannel (L : ℝ) (K : ℕ) :
    Fin 4 → Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ :=
  ![canonicalPoleMatrix L K,
    -canonicalArchMatrix L K - canonicalTrialScalarShiftMatrix L K,
    -canonicalPrimeMatrix L K,
    canonicalTrialScalarShiftMatrix L K]

/-- This channel representation sums to the unchanged canonical matrix. -/
theorem signedCanonicalTrialChannel_sum (L : ℝ) (K : ℕ) :
    (∑ c, signedCanonicalTrialChannel L K c) = canonicalSourceMatrix L K := by
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime]
  simp [signedCanonicalTrialChannel, Fin.sum_univ_succ]
  abel

/-- Actual channel compression on an existing legal parity carrier. -/
def parityCanonicalTrialChannel (p : ReversalParity) (L : ℝ) (K : ℕ)
    (c : Fin 4) :
    euclideanParityBoundaryFlatSubspace p K →ₗ[ℂ]
      euclideanParityBoundaryFlatSubspace p K :=
  nativeOrthogonalCompression (euclideanParityBoundaryFlatSubspace p K)
    ((signedCanonicalTrialChannel L K c).toEuclideanLin)

theorem parityCanonicalTrialChannel_sum (p : ReversalParity) (L : ℝ) (K : ℕ) :
    (∑ c, parityCanonicalTrialChannel p L K c) = parityCompressedCanonical p L K := by
  unfold parityCanonicalTrialChannel
  rw [← map_sum, ← map_sum, signedCanonicalTrialChannel_sum]
  rfl

/-- The trial residual of the actual legal parity block. -/
def canonicalTrialResidual (p : ReversalParity) (L : ℝ) (K : ℕ)
    (u : euclideanParityBoundaryFlatSubspace p K) :=
  nativeTrialResidual (parityCompressedCanonical p L K) u

theorem canonicalTrialResidual_variance (p : ReversalParity) (L : ℝ) (K : ℕ)
    (u : euclideanParityBoundaryFlatSubspace p K) (hu : ‖u‖ = 1) :
    ‖canonicalTrialResidual p L K u‖ ^ 2 =
      (inner ℂ u (parityCompressedCanonical p L K
        (parityCompressedCanonical p L K u))).re -
      ‖nativeTrialRayleigh (parityCompressedCanonical p L K) u‖ ^ 2 :=
  nativeTrialResidual_symmetric_variance (E := euclideanParityBoundaryFlatSubspace p K) _
    (parityCompressedCanonical_isSymmetric p L K) u hu

theorem canonicalTrialResidual_channelGram (p : ReversalParity) (L : ℝ) (K : ℕ)
    (u : euclideanParityBoundaryFlatSubspace p K) :
    ‖canonicalTrialResidual p L K u‖ ^ 2 =
      (∑ i, ∑ j, nativeTrialChannelGram (parityCanonicalTrialChannel p L K) u i j).re := by
  unfold canonicalTrialResidual
  rw [← parityCanonicalTrialChannel_sum]
  exact nativeTrialResidual_gram_sum _ u

/-- Actual signed channels on the native even pole-neutral compression. -/
def poleNeutralEvenCanonicalTrialChannel (L : ℝ) (K : ℕ) (c : Fin 4) :
    poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K :=
  nativeOrthogonalCompression (E := euclideanEvenBoundaryFlatSubspace K)
    (poleNeutralEvenSubspace L K)
    (parityCanonicalTrialChannel .even L K c)

/-- Actual signed channels on the native odd pole-neutral compression. -/
def poleNeutralOddCanonicalTrialChannel (L : ℝ) (K : ℕ) (c : Fin 4) :
    poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K :=
  nativeOrthogonalCompression (E := euclideanOddBoundaryFlatSubspace K)
    (poleNeutralOddSubspace L K)
    (parityCanonicalTrialChannel .odd L K c)

theorem poleNeutralEvenCanonicalTrialChannel_sum (L : ℝ) (K : ℕ) :
    (∑ c, poleNeutralEvenCanonicalTrialChannel L K c) =
      poleNeutralEvenCompressedCanonical L K := by
  unfold poleNeutralEvenCanonicalTrialChannel
  rw [← map_sum, parityCanonicalTrialChannel_sum]
  rfl

theorem poleNeutralOddCanonicalTrialChannel_sum (L : ℝ) (K : ℕ) :
    (∑ c, poleNeutralOddCanonicalTrialChannel L K c) =
      poleNeutralOddCompressedCanonical L K := by
  unfold poleNeutralOddCanonicalTrialChannel
  rw [← map_sum, parityCanonicalTrialChannel_sum]
  rfl

theorem poleNeutralEvenCompressedCanonical_isSymmetric (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenCompressedCanonical L K) := by
  intro x y
  change inner ℂ ((Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanEvenBoundaryFlatSubspace K) (poleNeutralEvenSubspace L K))
        (evenCompressedCanonical L K x.val)) y =
    inner ℂ x ((Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanEvenBoundaryFlatSubspace K) (poleNeutralEvenSubspace L K))
        (evenCompressedCanonical L K y.val))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
      (𝕜 := ℂ) (E := euclideanEvenBoundaryFlatSubspace K)
      (K := poleNeutralEvenSubspace L K),
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (𝕜 := ℂ) (E := euclideanEvenBoundaryFlatSubspace K)
      (K := poleNeutralEvenSubspace L K)]
  exact parityCompressedCanonical_isSymmetric .even L K x.val y.val

theorem poleNeutralOddCompressedCanonical_isSymmetric (L : ℝ) (K : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (poleNeutralOddCompressedCanonical L K) := by
  intro x y
  change inner ℂ ((Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
        (oddCompressedCanonical L K x.val)) y =
    inner ℂ x ((Submodule.orthogonalProjectionOnto (𝕜 := ℂ)
      (E := euclideanOddBoundaryFlatSubspace K) (poleNeutralOddSubspace L K))
        (oddCompressedCanonical L K y.val))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
      (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
      (K := poleNeutralOddSubspace L K),
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (𝕜 := ℂ) (E := euclideanOddBoundaryFlatSubspace K)
      (K := poleNeutralOddSubspace L K)]
  exact parityCompressedCanonical_isSymmetric .odd L K x.val y.val

theorem poleNeutralEvenTrialResidual_variance (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (hu : ‖u‖ = 1) :
    ‖nativeTrialResidual (poleNeutralEvenCompressedCanonical L K) u‖ ^ 2 =
      (inner ℂ u (poleNeutralEvenCompressedCanonical L K
        (poleNeutralEvenCompressedCanonical L K u))).re -
      ‖nativeTrialRayleigh (poleNeutralEvenCompressedCanonical L K) u‖ ^ 2 :=
  @nativeTrialResidual_symmetric_variance (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) (poleNeutralEvenCompressedCanonical L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K) u hu

theorem poleNeutralOddTrialResidual_variance (L : ℝ) (K : ℕ)
    (u : poleNeutralOddSubspace L K) (hu : ‖u‖ = 1) :
    ‖nativeTrialResidual (poleNeutralOddCompressedCanonical L K) u‖ ^ 2 =
      (inner ℂ u (poleNeutralOddCompressedCanonical L K
        (poleNeutralOddCompressedCanonical L K u))).re -
      ‖nativeTrialRayleigh (poleNeutralOddCompressedCanonical L K) u‖ ^ 2 :=
  @nativeTrialResidual_symmetric_variance (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) (poleNeutralOddCompressedCanonical L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K) u hu

theorem poleNeutralEvenTrialResidual_channelGram (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    ‖nativeTrialResidual (poleNeutralEvenCompressedCanonical L K) u‖ ^ 2 =
      (∑ i, ∑ j, nativeTrialChannelGram
        (poleNeutralEvenCanonicalTrialChannel L K) u i j).re := by
  rw [← poleNeutralEvenCanonicalTrialChannel_sum]
  exact nativeTrialResidual_gram_sum _ u

theorem poleNeutralOddTrialResidual_channelGram (L : ℝ) (K : ℕ)
    (u : poleNeutralOddSubspace L K) :
    ‖nativeTrialResidual (poleNeutralOddCompressedCanonical L K) u‖ ^ 2 =
      (∑ i, ∑ j, nativeTrialChannelGram
        (poleNeutralOddCanonicalTrialChannel L K) u i j).re := by
  rw [← poleNeutralOddCanonicalTrialChannel_sum]
  exact nativeTrialResidual_gram_sum _ u

end Zeta23.CCM

#print axioms Zeta23.CCM.signedCanonicalTrialChannel_sum
#print axioms Zeta23.CCM.parityCanonicalTrialChannel_sum
#print axioms Zeta23.CCM.nativeTrialResidual_add_scalar
#print axioms Zeta23.CCM.canonicalTrialResidual_variance
#print axioms Zeta23.CCM.canonicalTrialResidual_channelGram
#print axioms Zeta23.CCM.poleNeutralEvenCompressedCanonical_isSymmetric
#print axioms Zeta23.CCM.poleNeutralOddCompressedCanonical_isSymmetric
#print axioms Zeta23.CCM.poleNeutralEvenTrialResidual_variance
#print axioms Zeta23.CCM.poleNeutralOddTrialResidual_variance
#print axioms Zeta23.CCM.poleNeutralEvenTrialResidual_channelGram
#print axioms Zeta23.CCM.poleNeutralOddTrialResidual_channelGram
