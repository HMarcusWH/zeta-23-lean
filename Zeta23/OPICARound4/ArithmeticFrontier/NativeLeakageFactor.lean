import Zeta23.OPICARound4.ArithmeticFrontier.NativeMomentDisplacement
import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices

/-!
# The explicit rank-one leakage factor and the native rank-two commutator

`NativeMomentDisplacement` (M57) shows that `D₀ = diag(n²)` maps each actual moment
slice into the pole-neutral boundary-flat sector, leaving the slice only through
`M₆` (even) or `M₇` (odd). This module constructs the leakage factor explicitly
and composes it with the native commutator cancellation (NC).

A **Riesz slice** is `S = F ⊓ ker ⟪q, ·⟫` inside a subspace `F`. With
`r = P_F q` (the Riesz vector of `⟪q, ·⟫` on `F`), every `x ∈ F` decomposes as
`x = P_S x + c(x) r` with `c(x) = ⟪r, x⟫ / ‖r‖²` and `r ⟂ S`. For symmetric `D`, `A`
with `D u, D v ∈ F` and `⟪D u, A v⟫ = ⟪A u, D v⟫` on the slice, the compressed
commutator is exactly rank two:

`⟪u, P D P A v - P A P D v⟫ = c(D v) · conj ⟪r, A u⟫ - conj (c(D u)) · ⟪r, A v⟫`.

Native instances:

* even: `F` = even boundary-flat pole-neutral vectors, `q = (n⁴)`, so `S` is the
  actual even moment slice and `⟪r, D₀ u⟫ = M₆(u)`;
* odd: `F` = odd boundary-flat pole-neutral vectors with `M₃ = 0`, `q = (n⁵)`, so
  `S` is the actual odd moment slice and `⟪r, D₀ u⟫ = M₇(u)`.

The commutator hypothesis is supplied by NC for the full canonical source. In the
notation of the 8 November geometry report, `w = r/‖r‖`, `ℓ = P D₀ w` and
`z = P A w`; this is `[J, H] = z ℓᴴ - ℓ zᴴ` on the actual slices. These are exact
identities. They supply no sign, and they hold for any real prime weights.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open Matrix CCM

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

section RieszSlice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable (F : Submodule ℂ E) (q : E)

/-- The Riesz slice `F ⊓ ker ⟪q, ·⟫`. -/
def rieszSlice : Submodule ℂ E := F ⊓ LinearMap.ker (innerₛₗ ℂ q)

/-- The Riesz vector of `⟪q, ·⟫` on `F`: the orthogonal projection of `q` onto `F`. -/
def rieszVec : E := F.starProjection q

/-- The leakage coefficient `⟪r, x⟫ / ‖r‖²`. -/
def rieszCoeff (x : E) : ℂ := ⟪rieszVec F q, x⟫ / ((‖rieszVec F q‖ : ℂ) ^ 2)

omit [FiniteDimensional ℂ E] in
theorem mem_rieszSlice_iff (x : E) : x ∈ rieszSlice F q ↔ x ∈ F ∧ ⟪q, x⟫ = 0 := by
  simp [rieszSlice, Submodule.mem_inf, LinearMap.mem_ker, innerₛₗ_apply_apply]

theorem rieszVec_mem : rieszVec F q ∈ F := Submodule.starProjection_apply_mem _ _

theorem inner_rieszVec {x : E} (hx : x ∈ F) : ⟪rieszVec F q, x⟫ = ⟪q, x⟫ := by
  have h := Submodule.starProjection_inner_eq_zero q x hx
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem inner_rieszVec_of_mem_slice {s : E} (hs : s ∈ rieszSlice F q) :
    ⟪rieszVec F q, s⟫ = 0 := by
  obtain ⟨hsF, hq⟩ := (mem_rieszSlice_iff F q s).mp hs
  rw [inner_rieszVec F q hsF, hq]

theorem sub_rieszCoeff_mem {x : E} (hx : x ∈ F) :
    x - rieszCoeff F q x • rieszVec F q ∈ rieszSlice F q := by
  have hmem : x - rieszCoeff F q x • rieszVec F q ∈ F :=
    F.sub_mem hx (F.smul_mem _ (rieszVec_mem F q))
  refine (mem_rieszSlice_iff F q _).mpr ⟨hmem, ?_⟩
  rw [← inner_rieszVec F q hmem, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  unfold rieszCoeff
  by_cases h0 : rieszVec F q = 0
  · simp [h0]
  · have hn : ((‖rieszVec F q‖ : ℂ)) ^ 2 ≠ 0 := by
      have : (‖rieszVec F q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      exact pow_ne_zero 2 this
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hn).symm

/-- **Rank-one decomposition.** For `x ∈ F`, `P_S x = x - c(x) r`. -/
theorem starProjection_rieszSlice {x : E} (hx : x ∈ F) :
    (rieszSlice F q).starProjection x = x - rieszCoeff F q x • rieszVec F q := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (sub_rieszCoeff_mem F q hx)
  intro w hw
  rw [sub_sub_cancel, inner_smul_left, inner_rieszVec_of_mem_slice F q hw, mul_zero]

/-- **Rank-one leakage.** For `x ∈ F`, `x - P_S x = c(x) r` with `r ⟂ S`. -/
theorem sub_starProjection_rieszSlice {x : E} (hx : x ∈ F) :
    x - (rieszSlice F q).starProjection x = rieszCoeff F q x • rieszVec F q := by
  rw [starProjection_rieszSlice F q hx, sub_sub_cancel]

/-- **Rank-two compressed commutator.** For symmetric `D`, `A`, a slice vector `u`, any `v`,
with `D u, D v ∈ F` and `⟪D u, A v⟫ = ⟪A u, D v⟫`, the commutator of the compressions
`P D` and `P A` is the rank-two form built from the leakage coefficient and the
source response `⟪r, A ·⟫`. -/
theorem rieszSlice_compressed_commutator (D A : E →ₗ[ℂ] E) (hD : D.IsSymmetric)
    (hA : A.IsSymmetric) {u v : E} (hu : u ∈ rieszSlice F q)
    (hDu : D u ∈ F) (hDv : D v ∈ F) (hnc : ⟪D u, A v⟫ = ⟪A u, D v⟫) :
    ⟪u, (rieszSlice F q).starProjection (D ((rieszSlice F q).starProjection (A v))) -
        (rieszSlice F q).starProjection (A ((rieszSlice F q).starProjection (D v)))⟫ =
      rieszCoeff F q (D v) * star ⟪rieszVec F q, A u⟫ -
        star (rieszCoeff F q (D u)) * ⟪rieszVec F q, A v⟫ := by
  set P := (rieszSlice F q).starProjection
  have hPu : P u = u := (Submodule.starProjection_eq_self_iff).mpr hu
  have h1 : ⟪u, P (D (P (A v)))⟫ = ⟪P (D u), A v⟫ := by
    rw [← Submodule.inner_starProjection_left_eq_right, hPu, ← hD,
      Submodule.inner_starProjection_left_eq_right]
  have h2 : ⟪u, P (A (P (D v)))⟫ = ⟪A u, P (D v)⟫ := by
    rw [← Submodule.inner_starProjection_left_eq_right, hPu, ← hA]
  rw [inner_sub_right, h1, h2, starProjection_rieszSlice F q hDu,
    starProjection_rieszSlice F q hDv, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, hnc, ← inner_conj_symm (A u) (rieszVec F q)]
  simp only [RCLike.star_def]
  ring

end RieszSlice

/-! ## Native instances -/

/-- The real centered power vector `(nᵏ)` in the ambient Euclidean space. -/
def centeredPowerVec (K k : ℕ) : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  WithLp.toLp 2 (fun i => ((centeredIndex K i : ℤ) : ℂ) ^ k)

theorem inner_centeredPowerVec (K k : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ⟪centeredPowerVec K k, x⟫ = centeredMoment K k (WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [centeredPowerVec, centeredMoment, dotProduct, mul_comm]

/-- The even pole-neutral boundary-flat sector (ambient). -/
def evenFlatPoleAmb (L : ℝ) (K : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))) :=
  euclideanEvenBoundaryFlatSubspace K ⊓ LinearMap.ker (canonicalPoleEvenFunctional L K)

/-- The odd pole-neutral boundary-flat sector with `M₃ = 0` (ambient). -/
def oddFlatPoleM3Amb (L : ℝ) (K : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))) :=
  euclideanOddBoundaryFlatSubspace K ⊓ LinearMap.ker (canonicalPoleOddFunctional L K) ⊓
    LinearMap.ker (innerₛₗ ℂ (centeredPowerVec K 3))

/-- The actual even moment slice in the ambient space. -/
abbrev evenSliceAmb (L : ℝ) (K : ℕ) := rieszSlice (evenFlatPoleAmb L K) (centeredPowerVec K 4)

/-- The actual odd moment slice in the ambient space. -/
abbrev oddSliceAmb (L : ℝ) (K : ℕ) := rieszSlice (oddFlatPoleM3Amb L K) (centeredPowerVec K 5)

/-- The even leakage vector `r_e` (Riesz vector of `M₄` on the even sector). -/
abbrev evenLeakageVec (L : ℝ) (K : ℕ) := rieszVec (evenFlatPoleAmb L K) (centeredPowerVec K 4)

/-- The odd leakage vector `r_o` (Riesz vector of `M₅` on the odd sector). -/
abbrev oddLeakageVec (L : ℝ) (K : ℕ) := rieszVec (oddFlatPoleM3Amb L K) (centeredPowerVec K 5)

/-- The ambient even slice is exactly the existing `evenMomentSlice`. -/
theorem mem_evenSliceAmb_iff (L : ℝ) (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    ((u : euclideanEvenBoundaryFlatSubspace K) : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        evenSliceAmb L K ↔ u ∈ evenMomentSlice L K := by
  rw [mem_rieszSlice_iff, mem_evenMomentSlice_iff, inner_centeredPowerVec]
  have hF : ((u : euclideanEvenBoundaryFlatSubspace K) : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
      evenFlatPoleAmb L K :=
    Submodule.mem_inf.mpr ⟨u.val.property, by
      rw [LinearMap.mem_ker]; exact (mem_poleNeutralEvenSubspace L K u.val).mp u.property⟩
  exact ⟨fun h => h.2, fun h => ⟨hF, h⟩⟩

/-- The ambient odd slice is exactly the existing `oddMomentSlice`. -/
theorem mem_oddSliceAmb_iff (L : ℝ) (K : ℕ) (v : poleNeutralOddSubspace L K) :
    ((v : euclideanOddBoundaryFlatSubspace K) : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        oddSliceAmb L K ↔ v ∈ oddMomentSlice L K := by
  rw [mem_rieszSlice_iff, mem_oddMomentSlice_iff, inner_centeredPowerVec]
  have hv : canonicalPoleOddFunctional L K
      ((v : euclideanOddBoundaryFlatSubspace K) : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 :=
    (mem_poleNeutralOddSubspace L K v.val).mp v.property
  have hF : ((v : euclideanOddBoundaryFlatSubspace K) : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
      oddFlatPoleM3Amb L K ↔
        centeredMoment K 3 ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 := by
    simp only [oddFlatPoleM3Amb, Submodule.mem_inf, LinearMap.mem_ker, innerₛₗ_apply_apply,
      inner_centeredPowerVec]
    exact ⟨fun h => h.2, fun h => ⟨⟨v.val.property, hv⟩, h⟩⟩
  rw [hF]
  rfl


/-- The squared-index geometry `D₀` as an ambient operator. -/
abbrev squaredIndexOp (K : ℕ) := (squaredIndexMatrix K).toEuclideanLin

/-- The full canonical source as an ambient operator. -/
abbrev canonicalSourceOp (L : ℝ) (K : ℕ) := (canonicalSourceMatrix L K).toEuclideanLin

theorem squaredIndexOp_isSymmetric (K : ℕ) : (squaredIndexOp K).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (squaredIndexMatrix_conjTranspose K)

theorem canonicalSourceOp_isSymmetric (L : ℝ) (K : ℕ) : (canonicalSourceOp L K).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (canonicalSourceMatrix_isHermitian L K)

/-- (NC) on the ambient space: `⟪D₀ u, A v⟫ = ⟪A u, D₀ v⟫` for boundary-flat `u`, `v`. -/
theorem squaredIndexOp_source_commute_form {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u v : EuclideanSpace ℂ (Fin (2 * K + 1))}
    (hu : WithLp.ofLp u ∈ boundaryFlatSubspace K) (hv : WithLp.ofLp v ∈ boundaryFlatSubspace K) :
    ⟪squaredIndexOp K u, canonicalSourceOp L K v⟫ = ⟪canonicalSourceOp L K u, squaredIndexOp K v⟫ := by
  rw [squaredIndexOp_isSymmetric, canonicalSourceOp_isSymmetric, ← sub_eq_zero, ← inner_sub_right,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have h := squaredIndex_commutator_form_eq_zero_of_boundaryFlat hL K hv hu
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at h
  exact h

/-- `D₀` maps the even slice into the even pole-neutral boundary-flat sector. -/
theorem squaredIndexOp_mem_evenFlatPole {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ evenSliceAmb L K) :
    squaredIndexOp K u ∈ evenFlatPoleAmb L K := by
  obtain ⟨hF, h4⟩ := (mem_rieszSlice_iff _ _ u).mp hu
  obtain ⟨hflat, hpole⟩ := Submodule.mem_inf.mp hF
  rw [inner_centeredPowerVec] at h4
  have hp : ∑ i, poleEvenProfile L K i * WithLp.ofLp u i = 0 := by
    simpa [canonicalPoleEvenFunctional] using hpole
  obtain ⟨hmem, hpole', _⟩ := squaredIndex_mulVec_even_slice_leakage hL K hflat hp h4
  refine Submodule.mem_inf.mpr ⟨hmem, ?_⟩
  rw [LinearMap.mem_ker]
  exact hpole'

/-- `D₀` maps the odd slice into the odd pole-neutral boundary-flat sector with `M₃ = 0`. -/
theorem squaredIndexOp_mem_oddFlatPoleM3 {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ oddSliceAmb L K) :
    squaredIndexOp K u ∈ oddFlatPoleM3Amb L K := by
  obtain ⟨hF, h5⟩ := (mem_rieszSlice_iff _ _ u).mp hu
  simp only [oddFlatPoleM3Amb, Submodule.mem_inf, LinearMap.mem_ker, innerₛₗ_apply_apply,
    inner_centeredPowerVec] at hF ⊢
  obtain ⟨⟨hflat, hpole⟩, h3⟩ := hF
  rw [inner_centeredPowerVec] at h5
  have hp : ∑ i, poleOddProfile L K i * WithLp.ofLp u i = 0 := by
    simpa [canonicalPoleOddFunctional] using hpole
  obtain ⟨hmem, hpole', h3', _⟩ := squaredIndex_mulVec_odd_slice_leakage hL K hflat hp h3 h5
  exact ⟨⟨hmem, hpole'⟩, h3'⟩

/-- The even leakage numerator is the sixth centered moment: `⟪r_e, D₀ u⟫ = M₆(u)`. -/
theorem inner_evenLeakageVec_squaredIndexOp {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ evenSliceAmb L K) :
    ⟪evenLeakageVec L K, squaredIndexOp K u⟫ = centeredMoment K 6 (WithLp.ofLp u) := by
  rw [inner_rieszVec _ _ (squaredIndexOp_mem_evenFlatPole hL K hu), inner_centeredPowerVec]
  exact centeredMoment_squaredIndex_mulVec K 4 (WithLp.ofLp u)

/-- The odd leakage numerator is the seventh centered moment: `⟪r_o, D₀ u⟫ = M₇(u)`. -/
theorem inner_oddLeakageVec_squaredIndexOp {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ oddSliceAmb L K) :
    ⟪oddLeakageVec L K, squaredIndexOp K u⟫ = centeredMoment K 7 (WithLp.ofLp u) := by
  rw [inner_rieszVec _ _ (squaredIndexOp_mem_oddFlatPoleM3 hL K hu), inner_centeredPowerVec]
  exact centeredMoment_squaredIndex_mulVec K 5 (WithLp.ofLp u)

/-- **Explicit even rank-one leakage.** On the actual even slice,
`D₀ u - P_S D₀ u = (M₆(u) / ‖r_e‖²) r_e` with `r_e ⟂ S`. -/
theorem even_slice_rank_one_leakage {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ evenSliceAmb L K) :
    squaredIndexOp K u - (evenSliceAmb L K).starProjection (squaredIndexOp K u) =
      (centeredMoment K 6 (WithLp.ofLp u) / ((‖evenLeakageVec L K‖ : ℂ) ^ 2)) •
        evenLeakageVec L K := by
  rw [sub_starProjection_rieszSlice _ _ (squaredIndexOp_mem_evenFlatPole hL K hu), rieszCoeff,
    inner_evenLeakageVec_squaredIndexOp hL K hu]

/-- **Explicit odd rank-one leakage.** On the actual odd slice,
`D₀ u - P_S D₀ u = (M₇(u) / ‖r_o‖²) r_o` with `r_o ⟂ S`. -/
theorem odd_slice_rank_one_leakage {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ oddSliceAmb L K) :
    squaredIndexOp K u - (oddSliceAmb L K).starProjection (squaredIndexOp K u) =
      (centeredMoment K 7 (WithLp.ofLp u) / ((‖oddLeakageVec L K‖ : ℂ) ^ 2)) •
        oddLeakageVec L K := by
  rw [sub_starProjection_rieszSlice _ _ (squaredIndexOp_mem_oddFlatPoleM3 hL K hu), rieszCoeff,
    inner_oddLeakageVec_squaredIndexOp hL K hu]

/-- **Native even rank-two commutator.** For `u, v` in the actual even slice, with
`P` the slice projection, `J = P D₀` and `H = P A` (full canonical source),
`⟪u, (J H - H J) v⟫ = c(v) · conj ⟪r_e, A u⟫ - conj (c(u)) · ⟪r_e, A v⟫`,
`c(x) = M₆(x) / ‖r_e‖²`. Every source term is retained. -/
theorem even_native_rank_two_commutator {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u v : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ evenSliceAmb L K)
    (hv : v ∈ evenSliceAmb L K) :
    ⟪u, (evenSliceAmb L K).starProjection (squaredIndexOp K
          ((evenSliceAmb L K).starProjection (canonicalSourceOp L K v))) -
        (evenSliceAmb L K).starProjection (canonicalSourceOp L K
          ((evenSliceAmb L K).starProjection (squaredIndexOp K v)))⟫ =
      (centeredMoment K 6 (WithLp.ofLp v) / ((‖evenLeakageVec L K‖ : ℂ) ^ 2)) *
          star ⟪evenLeakageVec L K, canonicalSourceOp L K u⟫ -
        star (centeredMoment K 6 (WithLp.ofLp u) / ((‖evenLeakageVec L K‖ : ℂ) ^ 2)) *
          ⟪evenLeakageVec L K, canonicalSourceOp L K v⟫ := by
  have hflat : ∀ {x}, x ∈ evenSliceAmb L K → WithLp.ofLp x ∈ boundaryFlatSubspace K :=
    fun hx => (Submodule.mem_inf.mp (Submodule.mem_inf.mp ((mem_rieszSlice_iff _ _ _).mp hx).1).1).1
  have h := rieszSlice_compressed_commutator (evenFlatPoleAmb L K) (centeredPowerVec K 4)
    (squaredIndexOp K) (canonicalSourceOp L K) (squaredIndexOp_isSymmetric K)
    (canonicalSourceOp_isSymmetric L K) hu (squaredIndexOp_mem_evenFlatPole hL K hu)
    (squaredIndexOp_mem_evenFlatPole hL K hv)
    (squaredIndexOp_source_commute_form hL K (hflat hu) (hflat hv))
  rw [h, rieszCoeff, rieszCoeff, inner_evenLeakageVec_squaredIndexOp hL K hu,
    inner_evenLeakageVec_squaredIndexOp hL K hv]

/-- **Native odd rank-two commutator**, with `c(x) = M₇(x) / ‖r_o‖²`. -/
theorem odd_native_rank_two_commutator {L : ℝ} (hL : 0 < L) (K : ℕ)
    {u v : EuclideanSpace ℂ (Fin (2 * K + 1))} (hu : u ∈ oddSliceAmb L K)
    (hv : v ∈ oddSliceAmb L K) :
    ⟪u, (oddSliceAmb L K).starProjection (squaredIndexOp K
          ((oddSliceAmb L K).starProjection (canonicalSourceOp L K v))) -
        (oddSliceAmb L K).starProjection (canonicalSourceOp L K
          ((oddSliceAmb L K).starProjection (squaredIndexOp K v)))⟫ =
      (centeredMoment K 7 (WithLp.ofLp v) / ((‖oddLeakageVec L K‖ : ℂ) ^ 2)) *
          star ⟪oddLeakageVec L K, canonicalSourceOp L K u⟫ -
        star (centeredMoment K 7 (WithLp.ofLp u) / ((‖oddLeakageVec L K‖ : ℂ) ^ 2)) *
          ⟪oddLeakageVec L K, canonicalSourceOp L K v⟫ := by
  have hflat : ∀ {x}, x ∈ oddSliceAmb L K → WithLp.ofLp x ∈ boundaryFlatSubspace K := by
    intro x hx
    have h1 := ((mem_rieszSlice_iff _ _ _).mp hx).1
    simp only [oddFlatPoleM3Amb, Submodule.mem_inf] at h1
    exact (Submodule.mem_inf.mp h1.1.1).1
  have h := rieszSlice_compressed_commutator (oddFlatPoleM3Amb L K) (centeredPowerVec K 5)
    (squaredIndexOp K) (canonicalSourceOp L K) (squaredIndexOp_isSymmetric K)
    (canonicalSourceOp_isSymmetric L K) hu (squaredIndexOp_mem_oddFlatPoleM3 hL K hu)
    (squaredIndexOp_mem_oddFlatPoleM3 hL K hv)
    (squaredIndexOp_source_commute_form hL K (hflat hu) (hflat hv))
  rw [h, rieszCoeff, rieszCoeff, inner_oddLeakageVec_squaredIndexOp hL K hu,
    inner_oddLeakageVec_squaredIndexOp hL K hv]

end Zeta23.OPICARound4.ArithmeticFrontier
