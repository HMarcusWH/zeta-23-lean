import Zeta23.CCM.CanonicalPoleExponentialMoments
import Zeta23.CCM.CanonicalPoleNeutralTiePackage
import Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie
import Zeta23.CCM.CanonicalPoleNeutralNesting

noncomputable section
namespace Zeta23.CCM
open scoped BigOperators ComplexConjugate

-- Expose only inherited metric instances, retaining the actual coefficient
-- metric and keeping legal carrier definitions opaque.
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace

/-- The actual native carrier; the inherited coefficient metric is unchanged. -/
abbrev canonicalPoleNeutralEven := poleNeutralEvenSubspace
abbrev canonicalPoleNeutralOdd := poleNeutralOddSubspace
abbrev poleNormalCoefficient := poleNeutralEvenOutputCoefficient
abbrev correctedCanonicalSource := poleNeutralCorrectedCubicSource
abbrev poleNeutralOddShiftedRay := @poleNeutralOddAdjointShiftedRay
alias poleNormal_index_projection_eq := poleNeutralOddProjection_index_evenNormal_eq_cubic
alias canonicalPoleNeutral_rankOneIntertwining := canonicalPoleNeutralRankOneIntertwining

theorem poleNeutral_iff_exponentialMoments {L : ℝ} (hL : 0 < L) (K : ℕ) :
    (∀ u : euclideanEvenBoundaryFlatSubspace K,
      u ∈ poleNeutralEvenSubspace L K ↔
        canonicalPoleExponentialMoment 1 L K (evenBoundaryFlatRawCoefficients K u) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K (evenBoundaryFlatRawCoefficients K u) = 0) ∧
    (∀ u : euclideanOddBoundaryFlatSubspace K,
      u ∈ poleNeutralOddSubspace L K ↔
        canonicalPoleExponentialMoment 1 L K
          ((EuclideanSpace.equiv (Fin (2*K+1)) ℂ) u.val) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K
          ((EuclideanSpace.equiv (Fin (2*K+1)) ℂ) u.val) = 0) :=
  ⟨poleNeutralEven_iff_exponentialMoments hL K,
    poleNeutralOdd_iff_exponentialMoments hL K⟩

theorem poleNeutral_parity_finrank {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    Module.finrank ℂ (poleNeutralEvenSubspace L K) = K-2 ∧
    Module.finrank ℂ (poleNeutralOddSubspace L K) = K-2 :=
  ⟨finrank_poleNeutralEvenSubspace hL K (by omega),
    finrank_poleNeutralOddSubspace hL K (by omega)⟩

/-- This tag compares native neutral bottoms. It does not select an eigenvector
or impose a selected parity at a tie. -/
inductive PoleNeutralGroundBranch (L : ℝ) (K : ℕ) (hL : 0 < L) (hK : 3 ≤ K) where
  | strictEven (gap : poleNeutralEvenRayleighBottom L K hL hK <
      poleNeutralOddRayleighBottom L K hL hK)
  | strictOdd (gap : poleNeutralOddRayleighBottom L K hL hK <
      poleNeutralEvenRayleighBottom L K hL hK)
  | tie (equal : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)

theorem poleNeutralGround_branch_exhaustive {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) : Nonempty (PoleNeutralGroundBranch L K hL hK) := by
  rcases lt_trichotomy (poleNeutralEvenRayleighBottom L K hL hK)
      (poleNeutralOddRayleighBottom L K hL hK) with h | h | h
  · exact ⟨.strictEven h⟩
  · exact ⟨.tie h⟩
  · exact ⟨.strictOdd h⟩

theorem poleNeutral_evenShifted_eigen_iff {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    (∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) ↔
    correctedCanonicalSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam) = 1 := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    exact poleNeutral_even_eigen_shiftedRay_source_eq_one hL K hK lam hlam u hu0 hu
  · intro hs
    let x := poleNeutralEvenShiftedRay hL K hK lam hlam
    have hx : x ≠ 0 := by
      intro hz
      have h := hs
      change poleNeutralCorrectedCubicFunctional L K x = 1 at h
      rw [hz, map_zero] at h
      exact zero_ne_one h
    refine ⟨x, hx, ?_⟩
    have h := apply_secularResolventRay
      (Bi := poleNeutralOddShiftedCanonicalEquiv hL K hK lam hlam)
      (poleNeutral_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)
    change poleNeutralEvenShiftedCanonical L K lam x =
      (1 - correctedCanonicalSource L K x) • _ at h
    rw [hs, sub_self, zero_smul] at h
    exact sub_eq_zero.mp h

theorem poleNeutral_evenShifted_det_eq {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) =
      LinearMap.det (poleNeutralOddShiftedCanonical L K lam) *
        (1 - correctedCanonicalSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam)) :=
  det_eq_det_mul_one_sub_secularResolventScalar
    (poleNeutral_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)

theorem poleNeutral_oddShifted_eigen_iff {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    (∃ w : poleNeutralOddSubspace L K, w ≠ 0 ∧
      poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) ↔
    poleNeutralCubicPairingFunctional L K (poleNeutralOddShiftedRay hL K hK lam hlam) = 1 := by
  constructor
  · rintro ⟨w, hw0, hw⟩
    exact poleNeutral_odd_eigen_adjointRay_pairing_eq_one hL K hK lam hlam w hw0 hw
  · intro hs
    let y := poleNeutralOddShiftedRay hL K hK lam hlam
    have hy : y ≠ 0 := by
      intro hz
      have h := hs
      change poleNeutralCubicPairingFunctional L K y = 1 at h
      rw [hz, map_zero] at h
      exact zero_ne_one h
    refine ⟨y, hy, ?_⟩
    have h := apply_secularResolventRay
      (Bi := poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam)
      (poleNeutral_odd_adjoint_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)
    change poleNeutralOddShiftedCanonical L K lam y =
      (1 - poleNeutralCubicPairingFunctional L K y) • _ at h
    rw [hs, sub_self, zero_smul] at h
    exact sub_eq_zero.mp h

theorem poleNeutral_oddShifted_det_eq {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    LinearMap.det (poleNeutralOddShiftedCanonical L K lam) =
      LinearMap.det (poleNeutralEvenShiftedCanonical L K lam) *
        (1 - poleNeutralCubicPairingFunctional L K (poleNeutralOddShiftedRay hL K hK lam hlam)) :=
  det_eq_det_mul_one_sub_secularResolventScalar
    (poleNeutral_odd_adjoint_shifted_rankOneIntertwining hL K hK lam) (fun _ => rfl)


section ComplementInverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Every symmetric output belongs to the orthogonal kernel complement. -/
theorem nativeSymmetric_output_mem_kernelOrthogonal (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (x : E) :
    T x ∈ (LinearMap.ker T)ᗮ := by
  intro z hz
  rw [← hT z x, LinearMap.mem_ker.mp hz, inner_zero_left]

def nativeKernelComplementMap (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    (LinearMap.ker T)ᗮ →ₗ[ℂ] (LinearMap.ker T)ᗮ where
  toFun x := ⟨T x.val, nativeSymmetric_output_mem_kernelOrthogonal T hT x.val⟩
  map_add' x y := Subtype.ext (map_add T x.val y.val)
  map_smul' c x := Subtype.ext (map_smul T c x.val)

theorem nativeKernelComplementMap_injective (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    Function.Injective (nativeKernelComplementMap T hT) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hxT : T x.val = 0 :=
    congrArg Subtype.val hx
  have hz : inner ℂ x.val x.val = 0 :=
    x.property x.val (LinearMap.mem_ker.mpr hxT)
  exact Subtype.ext ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)

/-- Only the actual kernel complement is inverted, never the singular map. -/
def nativeKernelComplementEquiv (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    (LinearMap.ker T)ᗮ ≃ₗ[ℂ] (LinearMap.ker T)ᗮ :=
  LinearEquiv.ofInjectiveEndo (nativeKernelComplementMap T hT)
    (nativeKernelComplementMap_injective T hT)

def nativeKernelComplementResponse (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (f : E) (hf : f ∈ LinearMap.range T) : E :=
  ((nativeKernelComplementEquiv T hT).symm
    ⟨f, by
      obtain ⟨x, hx⟩ := hf
      rw [← hx]
      exact nativeSymmetric_output_mem_kernelOrthogonal T hT x⟩).val

theorem nativeKernelComplementResponse_eq (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (x f : E) (hf : f ∈ LinearMap.range T) (hx : T x = f) :
    nativeKernelComplementResponse T hT f hf =
      x - (LinearMap.ker T).starProjection x := by
  let y : (LinearMap.ker T)ᗮ :=
    ⟨x - (LinearMap.ker T).starProjection x,
      Submodule.sub_starProjection_mem_orthogonal _⟩
  have hy : nativeKernelComplementMap T hT y =
      ⟨f, by
        obtain ⟨z, hz⟩ := hf
        rw [← hz]
        exact nativeSymmetric_output_mem_kernelOrthogonal T hT z⟩ := by
    apply Subtype.ext
    change T (x - (LinearMap.ker T).starProjection x) = f
    rw [map_sub, LinearMap.mem_ker.mp
      ((LinearMap.ker T).starProjection_apply_mem x), sub_zero, hx]
  have hinv := congrArg (nativeKernelComplementEquiv T hT).symm hy
  change (nativeKernelComplementEquiv T hT).symm
    ((nativeKernelComplementEquiv T hT) y) = _ at hinv
  rw [LinearEquiv.symm_apply_apply] at hinv
  exact (congrArg Subtype.val hinv).symm

/-- Positivity is strict on precisely that complement; no nonzero source
functional or simplicity is needed. -/
theorem nativeKernelComplement_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (x : (LinearMap.ker T)ᗮ) (hx : x ≠ 0) :
    0 < (inner ℂ (T x.val) x.val).re := by
  by_contra hn
  have hz : (inner ℂ (T x.val) x.val).re = 0 :=
    le_antisymm (le_of_not_gt hn) (hT.2 _)
  have hTx := nativePositive_apply_eq_zero_of_energy_eq_zero T hT x.val hz
  have hself := x.property x.val (LinearMap.mem_ker.mpr hTx)
  exact hx (Subtype.ext ((inner_self_eq_zero (𝕜 := ℂ)).mp hself))

theorem nativeKernelComplement_decomposition (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (x f : E) (hf : f ∈ LinearMap.range T) (hx : T x = f) :
    x = (LinearMap.ker T).starProjection x + nativeKernelComplementResponse T hT f hf := by
  rw [nativeKernelComplementResponse_eq T hT x f hf hx]
  abel

theorem nativeSymmetric_kernelProjection_output_eq_zero
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) :
    (LinearMap.ker T).orthogonalProjectionOnto (T x) = 0 := by
  exact (Submodule.orthogonalProjectionOnto_eq_zero_iff
    (𝕜 := ℂ) (E := E) (K := LinearMap.ker T)).mpr
      (nativeSymmetric_output_mem_kernelOrthogonal T hT x)


theorem nativeKernelComplementResponse_eq_of_mem
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x f : E)
    (hf : f ∈ LinearMap.range T) (horth : x ∈ (LinearMap.ker T)ᗮ) (hx : T x = f) :
    nativeKernelComplementResponse T hT f hf = x := by
  have hp : (LinearMap.ker T).orthogonalProjectionOnto x = 0 :=
    (Submodule.orthogonalProjectionOnto_eq_zero_iff
      (𝕜 := ℂ) (E := E) (K := LinearMap.ker T)).mpr horth
  have hs : (LinearMap.ker T).starProjection x = 0 := congrArg Subtype.val hp
  simpa only [hs, sub_zero] using nativeKernelComplementResponse_eq T hT x f hf hx

end ComplementInverse

theorem poleNeutralEvenShiftedCanonical_isSymmetric (L : ℝ) (K : ℕ) (lam : ℝ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenShiftedCanonical L K lam) :=
  (poleNeutralEvenCompressedCanonical_isSymmetric L K).sub
    (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id)

def poleNeutralEvenShiftedKernelProjection (L : ℝ) (K : ℕ) (lam : ℝ) :
    poleNeutralEvenSubspace L K →L[ℂ]
      (LinearMap.ker (poleNeutralEvenShiftedCanonical L K lam) :
        Submodule ℂ (poleNeutralEvenSubspace L K)) :=
  Submodule.orthogonalProjectionOnto (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
    (LinearMap.ker (poleNeutralEvenShiftedCanonical L K lam) :
      Submodule ℂ (poleNeutralEvenSubspace L K))

/-- Actual odd-vector counterpart, with the required negative adjoint source. -/
theorem poleNeutral_odd_eigen_source_mem_even_shifted_range {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K ∈
      LinearMap.range (poleNeutralEvenShiftedCanonical L K lam) :=
  ⟨(LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
    (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w,
    poleNeutral_odd_eigen_adjoint_competitor_eq_source hL K hK lam w hw⟩

theorem poleNeutral_odd_eigen_shifted_kernel_compatibility {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    -poleNeutralCubicPairingFunctional L K w •
      poleNeutralEvenShiftedKernelProjection L K lam (poleNeutralCorrectedCubicRieszVector L K) = 0 := by
  have heq := poleNeutral_odd_eigen_adjoint_competitor_eq_source hL K hK lam w hw
  have hp := @nativeSymmetric_kernelProjection_output_eq_zero
    (poleNeutralEvenSubspace L K) inferInstance (poleNeutralEven_innerProductSpace L K) inferInstance
    (poleNeutralEvenShiftedCanonical L K lam)
    (poleNeutralEvenShiftedCanonical_isSymmetric L K lam)
    ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w)
  change poleNeutralEvenShiftedKernelProjection L K lam
    (poleNeutralEvenShiftedCanonical L K lam
      ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
        (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w)) = 0 at hp
  rw [heq, map_smul] at hp
  exact hp

/-- Universal compatibility applies to the stored vector in either parity;
no new ground is selected and no source scalar is declared nonzero. -/
theorem poleNeutral_tied_kernel_compatibility {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) :
    (∀ u : poleNeutralEvenSubspace L K,
      poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u →
      poleNeutralCorrectedCubicSource L K u •
        poleNeutralOddShiftedKernelProjection L K lam (poleNeutralCubicCompressionVector L K) = 0) ∧
    (∀ w : poleNeutralOddSubspace L K,
      poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w →
      -poleNeutralCubicPairingFunctional L K w •
        poleNeutralEvenShiftedKernelProjection L K lam (poleNeutralCorrectedCubicRieszVector L K) = 0) :=
  ⟨poleNeutral_even_eigen_shifted_kernel_compatibility hL K hK lam,
    poleNeutral_odd_eigen_shifted_kernel_compatibility hL K hK lam⟩


/-- Typed native adapters pin the inherited metric before the generic
kernel-complement inverse is elaborated. -/
def poleNeutralOddKernelComplementResponse (L : ℝ) (K : ℕ) (lam : ℝ)
    (f : poleNeutralOddSubspace L K)
    (hf : f ∈ LinearMap.range (poleNeutralOddShiftedCanonical L K lam)) :
    poleNeutralOddSubspace L K :=
  @nativeKernelComplementResponse (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) inferInstance
    (poleNeutralOddShiftedCanonical L K lam)
    (poleNeutralOddShiftedCanonical_isSymmetric L K lam) f hf

def poleNeutralEvenKernelComplementResponse (L : ℝ) (K : ℕ) (lam : ℝ)
    (f : poleNeutralEvenSubspace L K)
    (hf : f ∈ LinearMap.range (poleNeutralEvenShiftedCanonical L K lam)) :
    poleNeutralEvenSubspace L K :=
  @nativeKernelComplementResponse (poleNeutralEvenSubspace L K) inferInstance
    (poleNeutralEven_innerProductSpace L K) inferInstance
    (poleNeutralEvenShiftedCanonical L K lam)
    (poleNeutralEvenShiftedCanonical_isSymmetric L K lam) f hf

/-- Both complementary responses retain the actual transformed vector's
kernel projection. These identities also hold away from a bottom tie. -/
theorem poleNeutral_tied_complementary_response {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ) :
    (∀ u : poleNeutralEvenSubspace L K,
      (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) →
      ∃ hr : poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K ∈
          LinearMap.range (poleNeutralOddShiftedCanonical L K lam),
        poleNeutralIndexLinearMap hL K u =
          (LinearMap.ker (poleNeutralOddShiftedCanonical L K lam)).starProjection
            (poleNeutralIndexLinearMap hL K u) +
          poleNeutralOddKernelComplementResponse L K lam
            (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) hr) ∧
    (∀ w : poleNeutralOddSubspace L K,
      (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) →
      ∃ hr : -poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K ∈
          LinearMap.range (poleNeutralEvenShiftedCanonical L K lam),
        (LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
          (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w =
          (LinearMap.ker (poleNeutralEvenShiftedCanonical L K lam)).starProjection
            ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
              (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w) +
          poleNeutralEvenKernelComplementResponse L K lam
            (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K) hr) := by
  constructor
  · intro u hu
    have hr := poleNeutral_even_eigen_source_mem_odd_shifted_range hL K hK lam u hu
    refine ⟨hr, ?_⟩
    have hc := poleNeutral_even_eigen_complement_source_eq hL K hK lam u hu
    have ho := poleNeutralEvenEigen_indexComplement_mem_kernel_orthogonal hL K lam u
    have hresponse := @nativeKernelComplementResponse_eq_of_mem (poleNeutralOddSubspace L K)
        (poleNeutralOddSubspace L K).normedAddCommGroup
        (poleNeutralOdd_innerProductSpace L K) inferInstance
        (poleNeutralOddShiftedCanonical L K lam)
        (poleNeutralOddShiftedCanonical_isSymmetric L K lam)
        (poleNeutralEvenEigen_indexComplementComponent hL K lam u)
        (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) hr ho hc
    change poleNeutralOddKernelComplementResponse L K lam
        (poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K) hr =
          poleNeutralEvenEigen_indexComplementComponent hL K lam u at hresponse
    rw [hresponse]
    simpa only [poleNeutralEvenEigen_indexKernelComponent,
      poleNeutralOddShiftedKernelProjection, Submodule.coe_orthogonalProjectionOnto_apply] using
      poleNeutralEvenEigen_index_eq_kernel_add_complement hL K lam u
  · intro w hw
    have hr := poleNeutral_odd_eigen_source_mem_even_shifted_range hL K hK lam w hw
    refine ⟨hr, ?_⟩
    have hresponse := @nativeKernelComplement_decomposition (poleNeutralEvenSubspace L K)
      (poleNeutralEvenSubspace L K).normedAddCommGroup
      (poleNeutralEven_innerProductSpace L K) inferInstance
      (poleNeutralEvenShiftedCanonical L K lam)
      (poleNeutralEvenShiftedCanonical_isSymmetric L K lam)
      ((LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
        (F := poleNeutralOddSubspace L K) (poleNeutralIndexLinearMap hL K)) w)
      (-poleNeutralCubicPairingFunctional L K w • poleNeutralCorrectedCubicRieszVector L K) hr
      (poleNeutral_odd_eigen_adjoint_competitor_eq_source hL K hK lam w hw)
    exact hresponse


/-- Below K=3 both native carriers really are zero. No empty bottom is defined. -/
theorem poleNeutral_smallCutoff_eq_zero {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : K < 3) :
    (∀ u : poleNeutralEvenSubspace L K, u = 0) ∧
    (∀ w : poleNeutralOddSubspace L K, w = 0) := by
  have he : ∀ u : poleNeutralEvenSubspace L 2, u = 0 :=
    (finrank_zero_iff_forall_zero (K := ℂ)).mp
      (finrank_poleNeutralEvenSubspace hL 2 (by omega))
  have ho : ∀ w : poleNeutralOddSubspace L 2, w = 0 :=
    (finrank_zero_iff_forall_zero (K := ℂ)).mp
      (finrank_poleNeutralOddSubspace hL 2 (by omega))
  constructor
  · intro u
    let J := poleNeutralEvenCenteredZeroExtend L (show K ≤ 2 by omega)
    apply J.injective
    exact (he (J u)).trans J.map_zero.symm
  · intro w
    let J := poleNeutralOddCenteredZeroExtend L (show K ≤ 2 by omega)
    apply J.injective
    exact (ho (J w)).trans J.map_zero.symm

theorem poleNeutralEvenShifted_isPositive_of_le_bottom {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam ≤ poleNeutralEvenRayleighBottom L K hL hK) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenShiftedCanonical L K lam) := by
  refine ⟨poleNeutralEvenShiftedCanonical_isSymmetric L K lam, ?_⟩
  intro u
  have h := poleNeutralEvenShiftedCanonical_coercive hL K hK lam u
  exact (mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg _)).trans h

/-- At a native bottom tie the two actual shifted operators are positive;
their constructed kernel complements are strictly positive by
nativeKernelComplement_positive, with arbitrary kernel multiplicity. -/
theorem poleNeutral_tied_complements_positive {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)) ∧
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (poleNeutralOddShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)) := by
  exact ⟨poleNeutralEvenShifted_isPositive_of_le_bottom hL K hK _ le_rfl,
    poleNeutralOddShifted_isPositive_of_le_bottom hL K hK _ (le_of_eq htie)⟩

end Zeta23.CCM
#print axioms Zeta23.CCM.poleNeutral_iff_exponentialMoments
#print axioms Zeta23.CCM.poleNeutral_parity_finrank
#print axioms Zeta23.CCM.poleNeutralGround_branch_exhaustive
#print axioms Zeta23.CCM.poleNeutral_evenShifted_eigen_iff
#print axioms Zeta23.CCM.poleNeutral_evenShifted_det_eq
#print axioms Zeta23.CCM.poleNeutral_oddShifted_eigen_iff
#print axioms Zeta23.CCM.poleNeutral_oddShifted_det_eq
#print axioms Zeta23.CCM.nativeKernelComplementMap_injective
#print axioms Zeta23.CCM.nativeKernelComplementResponse_eq
#print axioms Zeta23.CCM.nativeKernelComplement_positive
#print axioms Zeta23.CCM.poleNeutral_tied_kernel_compatibility
#print axioms Zeta23.CCM.poleNeutral_tied_complementary_response
#print axioms Zeta23.CCM.poleNeutral_smallCutoff_eq_zero
#print axioms Zeta23.CCM.poleNeutral_tied_complements_positive

