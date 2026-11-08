import Zeta23.OPICARound4.ArithmeticFrontier.NativeLeakageFactor
import Zeta23.OPICARound4.ArithmeticFrontier.GrowthClosure

/-!
# The geometry-diagonal reconstruction bound (abstract form of the (SG) reduction)

Work in an orthonormal eigenbasis of a self-adjoint geometry `J` with eigenvalues `θᵢ`.
If a matrix `H` satisfies the rank-two commutator relation
`(θᵢ - θⱼ) Hᵢⱼ = zᵢ conj(ℓⱼ) - ℓᵢ conj(zⱼ)` for `i ≠ j`, every gap `|θᵢ - θⱼ|` is at least
`g > 0`, and every diagonal entry has real part at least `h₀`, then

`Re (x* H x) ≥ (h₀ - 2 ‖z‖ ‖ℓ‖ / g) ‖x‖²`

for every vector `x`. The off-diagonal part is bounded entrywise by Cauchy–Schwarz,
not through a Frobenius norm, so no dimension factor appears. With the native
identity of `NativeLeakageFactor` (M58) this is the reconstruction step of the
8 November geometry report: a polynomial geometry gap, a polynomial source response
`‖z‖` and a polynomial lower bound on the geometry diagonal give a polynomial lower
bound on the whole slice energy. Both source estimates and the native gap bound
remain OPEN; no sign is supplied.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open Matrix CCM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- One off-diagonal entry: `g ‖Hᵢⱼ‖ ≤ ‖zᵢ‖ ‖ℓⱼ‖ + ‖ℓᵢ‖ ‖zⱼ‖`. -/
theorem reconstruction_offdiag_entry_le (H : Matrix ι ι ℂ) (θ : ι → ℝ) (z ℓ : ι → ℂ) {g : ℝ}
    {i j : ι} (hgap : g ≤ |θ i - θ j|)
    (hcomm : ((θ i : ℂ) - θ j) * H i j = z i * star (ℓ j) - ℓ i * star (z j)) :
    g * ‖H i j‖ ≤ ‖z i‖ * ‖ℓ j‖ + ‖ℓ i‖ * ‖z j‖ := by
  have hn := congrArg norm hcomm
  rw [norm_mul] at hn
  have hθ : ‖(θ i : ℂ) - θ j‖ = |θ i - θ j| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hθ] at hn
  have hle : ‖z i * star (ℓ j) - ℓ i * star (z j)‖ ≤ ‖z i‖ * ‖ℓ j‖ + ‖ℓ i‖ * ‖z j‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_star, norm_star]
  calc g * ‖H i j‖ ≤ |θ i - θ j| * ‖H i j‖ :=
        mul_le_mul_of_nonneg_right hgap (norm_nonneg _)
    _ = ‖z i * star (ℓ j) - ℓ i * star (z j)‖ := hn
    _ ≤ _ := hle

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for the weighted sums used below. -/
theorem sum_norm_mul_le {x y : ι → ℂ} {X Y : ℝ} (hX : ∑ i, ‖x i‖ ^ 2 ≤ X)
    (hY : ∑ i, ‖y i‖ ^ 2 ≤ Y) :
    (∑ i, ‖x i‖ * ‖y i‖) ^ 2 ≤ X * Y := by
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  exact mul_le_mul hX hY (Finset.sum_nonneg fun i _ => sq_nonneg _)
    ((Finset.sum_nonneg fun i _ => sq_nonneg _).trans hX)

/-- **Reconstruction bound.** Under the rank-two commutator relation with gaps at
least `g > 0` and diagonal real parts at least `h₀`,
`(h₀ - 2 n_z n_ℓ / g) ‖x‖² ≤ Re (x* H x)` whenever `‖z‖ ≤ n_z` and `‖ℓ‖ ≤ n_ℓ`. -/
theorem reconstruction_lower_bound (H : Matrix ι ι ℂ) (θ : ι → ℝ) (z ℓ : ι → ℂ)
    {g h₀ nz nl : ℝ} (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ |θ i - θ j|)
    (hcomm : ∀ i j, i ≠ j → ((θ i : ℂ) - θ j) * H i j = z i * star (ℓ j) - ℓ i * star (z j))
    (hdiag : ∀ i, h₀ ≤ (H i i).re) (hnz : 0 ≤ nz) (hnl : 0 ≤ nl)
    (hz : ∑ i, ‖z i‖ ^ 2 ≤ nz ^ 2) (hl : ∑ i, ‖ℓ i‖ ^ 2 ≤ nl ^ 2) (x : ι → ℂ) :
    (h₀ - 2 * nz * nl / g) * ∑ i, ‖x i‖ ^ 2 ≤ (star x ⬝ᵥ (H *ᵥ x)).re := by
  set X := ∑ i, ‖x i‖ ^ 2 with hXdef
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- entrywise majorant of the off-diagonal terms
  set B : ι → ι → ℝ := fun i j => ‖x i‖ * (‖z i‖ * ‖ℓ j‖ + ‖ℓ i‖ * ‖z j‖) * ‖x j‖ with hB
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => by positivity
  have hexp : star x ⬝ᵥ (H *ᵥ x) = ∑ i, ∑ j, star (x i) * H i j * x j := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrow : ∀ i, h₀ * ‖x i‖ ^ 2 - (∑ j, B i j) / g ≤
      ∑ j, (star (x i) * H i j * x j).re := by
    intro i
    rw [← Finset.add_sum_erase _ (fun j => (star (x i) * H i j * x j).re) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => B i j) (Finset.mem_univ i)]
    have hdi : h₀ * ‖x i‖ ^ 2 ≤ (star (x i) * H i i * x i).re := by
      have hxx : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, ← Complex.conj_mul']
        rfl
      have : star (x i) * H i i * x i = H i i * ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hxx]
        ring
      rw [this, Complex.re_mul_ofReal]
      exact mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg _)
    have hoff : -(∑ j ∈ Finset.univ.erase i, B i j) / g ≤
        ∑ j ∈ Finset.univ.erase i, (star (x i) * H i j * x j).re := by
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
      have he := reconstruction_offdiag_entry_le H θ z ℓ (hgap i j hij) (hcomm i j hij)
      have hnorm : ‖star (x i) * H i j * x j‖ ≤ B i j / g := by
        rw [norm_mul, norm_mul, norm_star, le_div_iff₀ hg]
        calc ‖x i‖ * ‖H i j‖ * ‖x j‖ * g = ‖x i‖ * (g * ‖H i j‖) * ‖x j‖ := by ring
          _ ≤ ‖x i‖ * (‖z i‖ * ‖ℓ j‖ + ‖ℓ i‖ * ‖z j‖) * ‖x j‖ := by
              gcongr
          _ = B i j := rfl
      have hre := (abs_le.mp (Complex.abs_re_le_norm (star (x i) * H i j * x j))).1
      linarith [neg_le_neg hnorm]
    have hBi := hB0 i i
    have : (B i i + ∑ j ∈ Finset.univ.erase i, B i j) / g ≥
        (∑ j ∈ Finset.univ.erase i, B i j) / g :=
      div_le_div_of_nonneg_right (by linarith) hg.le
    rw [neg_div] at hoff
    linarith
  -- the double sum of the majorant
  set P := ∑ i, ‖x i‖ * ‖z i‖ with hP
  set Q := ∑ i, ‖x i‖ * ‖ℓ i‖ with hQ
  have hBsum : ∑ i, ∑ j, B i j = 2 * (P * Q) := by
    have : ∀ i j, B i j = (‖x i‖ * ‖z i‖) * (‖x j‖ * ‖ℓ j‖) + (‖x i‖ * ‖ℓ i‖) * (‖x j‖ * ‖z j‖) :=
      fun i j => by simp only [hB]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul_sum, hP, hQ]
    ring
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => by positivity
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => by positivity
  have hPQ : P * Q ≤ X * (nz * nl) := by
    have h1 := sum_norm_mul_le (le_refl X) hz
    have h2 := sum_norm_mul_le (le_refl X) hl
    have hsq : (P * Q) ^ 2 ≤ (X * (nz * nl)) ^ 2 := by
      calc (P * Q) ^ 2 = P ^ 2 * Q ^ 2 := by ring
        _ ≤ (X * nz ^ 2) * (X * nl ^ 2) :=
            mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
        _ = (X * (nz * nl)) ^ 2 := by ring
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have htotal : h₀ * X - (∑ i, ∑ j, B i j) / g ≤ (star x ⬝ᵥ (H *ᵥ x)).re := by
    rw [hexp, Complex.re_sum]
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i
    simp only [Complex.re_sum] at this ⊢
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div] at this
    exact this
  have hfin : (h₀ - 2 * nz * nl / g) * X ≤ h₀ * X - (∑ i, ∑ j, B i j) / g := by
    rw [hBsum]
    have : 2 * (P * Q) / g ≤ 2 * (X * (nz * nl)) / g :=
      div_le_div_of_nonneg_right (by linarith) hg.le
    have heq : (h₀ - 2 * nz * nl / g) * X = h₀ * X - 2 * (X * (nz * nl)) / g := by
      field_simp
    linarith
  linarith


/-! ## The reconstruction on a Riesz slice, in a geometry eigenbasis -/

section Slice

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- In a geometry eigenbasis `b` of the compressed geometry `P D` on a Riesz slice,
the source entries `⟪bᵢ, A bⱼ⟫` satisfy the rank-two commutator relation with
`zᵢ = conj ⟪r, A bᵢ⟫` and `ℓᵢ = conj (c(D bᵢ))`. -/
theorem rieszSlice_eigen_commutator (F : Submodule ℂ E) (q : E) (D A : E →ₗ[ℂ] E)
    (hD : D.IsSymmetric) (hA : A.IsSymmetric)
    (hDF : ∀ u, u ∈ rieszSlice F q → D u ∈ F)
    (hnc : ∀ u v, u ∈ rieszSlice F q → v ∈ rieszSlice F q → ⟪D u, A v⟫ = ⟪A u, D v⟫)
    {bi bj : E} {θi θj : ℝ} (hbi : bi ∈ rieszSlice F q) (hbj : bj ∈ rieszSlice F q)
    (hJi : (rieszSlice F q).starProjection (D bi) = (θi : ℂ) • bi)
    (hJj : (rieszSlice F q).starProjection (D bj) = (θj : ℂ) • bj) :
    ((θi : ℂ) - θj) * ⟪bi, A bj⟫ =
      star ⟪rieszVec F q, A bi⟫ * star (star (rieszCoeff F q (D bj))) -
        star (rieszCoeff F q (D bi)) * star (star ⟪rieszVec F q, A bj⟫) := by
  set P := (rieszSlice F q).starProjection
  have hPi : P bi = bi := (Submodule.starProjection_eq_self_iff).mpr hbi
  have h := rieszSlice_compressed_commutator F q D A hD hA hbi (hDF bi hbi) (hDF bj hbj)
    (hnc bi bj hbi hbj)
  have h1 : ⟪bi, P (D (P (A bj)))⟫ = (θi : ℂ) * ⟪bi, A bj⟫ := by
    rw [← Submodule.inner_starProjection_left_eq_right, hPi, ← hD,
      ← Submodule.inner_starProjection_left_eq_right, hJi, inner_smul_left, Complex.conj_ofReal]
  have h2 : ⟪bi, P (A (P (D bj)))⟫ = (θj : ℂ) * ⟪bi, A bj⟫ := by
    rw [hJj, map_smul, ← Submodule.inner_starProjection_left_eq_right, hPi, inner_smul_right]
  rw [inner_sub_right, h1, h2] at h
  rw [sub_mul, h, star_star, star_star]
  ring

/-- **Reconstruction on a Riesz slice.** Let `b` be an orthonormal eigenbasis family of
the compressed geometry `P D` in the slice, with eigenvalue gaps at least `g > 0`,
geometry-diagonal real parts at least `h₀`, source response `Σ ‖⟪r, A bᵢ⟫‖² ≤ n_z²` and
leakage `Σ ‖c(D bᵢ)‖² ≤ n_ℓ²`. Then every combination `x = Σ cᵢ bᵢ` satisfies
`(h₀ - 2 n_z n_ℓ / g) ‖x‖² ≤ Re ⟪x, A x⟫`. -/
theorem rieszSlice_form_lower_of_geometry_basis (F : Submodule ℂ E) (q : E) (D A : E →ₗ[ℂ] E)
    (hD : D.IsSymmetric) (hA : A.IsSymmetric)
    (hDF : ∀ u, u ∈ rieszSlice F q → D u ∈ F)
    (hnc : ∀ u v, u ∈ rieszSlice F q → v ∈ rieszSlice F q → ⟪D u, A v⟫ = ⟪A u, D v⟫)
    {n : ℕ} (b : Fin n → E) (hb : Orthonormal ℂ b) (hbS : ∀ i, b i ∈ rieszSlice F q)
    (θ : Fin n → ℝ) (hJ : ∀ i, (rieszSlice F q).starProjection (D (b i)) = (θ i : ℂ) • b i)
    {g h₀ nz nl : ℝ} (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ |θ i - θ j|)
    (hdiag : ∀ i, h₀ ≤ (⟪b i, A (b i)⟫).re) (hnz : 0 ≤ nz) (hnl : 0 ≤ nl)
    (hz : ∑ i, ‖⟪rieszVec F q, A (b i)⟫‖ ^ 2 ≤ nz ^ 2)
    (hl : ∑ i, ‖rieszCoeff F q (D (b i))‖ ^ 2 ≤ nl ^ 2) (c : Fin n → ℂ) :
    (h₀ - 2 * nz * nl / g) * ‖∑ i, c i • b i‖ ^ 2 ≤
      (⟪∑ i, c i • b i, A (∑ i, c i • b i)⟫).re := by
  set H : Matrix (Fin n) (Fin n) ℂ := fun i j => ⟪b i, A (b j)⟫ with hH
  have hform : ⟪∑ i, c i • b i, A (∑ i, c i • b i)⟫ = star c ⬝ᵥ (H *ᵥ c) := by
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      dotProduct, mulVec, Pi.star_apply, hH, Finset.mul_sum, RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnorm : ‖∑ i, c i • b i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have h := hb.inner_sum c c Finset.univ
    rw [inner_self_eq_norm_sq_to_K] at h
    have h1 : (((‖∑ i, c i • b i‖ ^ 2 : ℝ)) : ℂ) = ∑ i, (starRingEnd ℂ) (c i) * c i := by
      rw [Complex.ofReal_pow]; exact h
    have h2 : ∑ i, (starRingEnd ℂ) (c i) * c i = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_pow, Complex.conj_mul']
    exact_mod_cast h1.trans h2
  rw [hform, hnorm]
  refine reconstruction_lower_bound H θ (fun i => star ⟪rieszVec F q, A (b i)⟫)
    (fun i => star (rieszCoeff F q (D (b i)))) hg hgap (fun i j _ => ?_) hdiag hnz hnl
    (by simp only [norm_star]; exact hz) (by simp only [norm_star]; exact hl) c
  exact rieszSlice_eigen_commutator F q D A hD hA hDF hnc (hbS i) (hbS j) (hJ i) (hJ j)

end Slice

/-! ## Native geometry-response certificates and the (SG) consumer -/

section Native

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- A **geometry-response certificate** for the actual even slice at `(L, K)` with floor
`m`. It consists of:
* an orthonormal geometry eigenbasis `b` of the slice for `P D₀`, with gaps at least `g > 0`;
* geometry-diagonal real parts `Re ⟪bᵢ, A bᵢ⟫` at least `h₀`;
* source response `Σ ‖⟪r_e, A bᵢ⟫‖² ≤ n_z²` and leakage `Σ ‖c(D₀ bᵢ)‖² ≤ n_ℓ²`, where
  `c(D₀ x) = M₆(x)/‖r_e‖²`;
* reconstruction floor `h₀ - 2 n_z n_ℓ / g ≥ -m`.

These are the terms of the candidate (SG). The certificate is a premise, not a
theorem. -/
def EvenGeometryResponseCertificate (L : ℝ) (K : ℕ) (m : ℝ) : Prop :=
  ∃ (n : ℕ) (b : Fin n → EuclideanSpace ℂ (Fin (2 * K + 1))) (θ : Fin n → ℝ) (g h₀ nz nl : ℝ),
    Orthonormal ℂ b ∧ (∀ i, b i ∈ evenSliceAmb L K) ∧
    (∀ x, x ∈ evenSliceAmb L K → x = ∑ i, ⟪b i, x⟫ • b i) ∧
    (∀ i, (evenSliceAmb L K).starProjection (squaredIndexOp K (b i)) = (θ i : ℂ) • b i) ∧
    0 < g ∧ (∀ i j, i ≠ j → g ≤ |θ i - θ j|) ∧
    (∀ i, h₀ ≤ (⟪b i, canonicalSourceOp L K (b i)⟫).re) ∧ 0 ≤ nz ∧ 0 ≤ nl ∧
    (∑ i, ‖⟪evenLeakageVec L K, canonicalSourceOp L K (b i)⟫‖ ^ 2 ≤ nz ^ 2) ∧
    (∑ i, ‖rieszCoeff (evenFlatPoleAmb L K) (centeredPowerVec K 4)
        (squaredIndexOp K (b i))‖ ^ 2 ≤ nl ^ 2) ∧
    -m ≤ h₀ - 2 * nz * nl / g

/-- The odd geometry-response certificate, with `r_o` and `c(D₀ x) = M₇(x)/‖r_o‖²`. -/
def OddGeometryResponseCertificate (L : ℝ) (K : ℕ) (m : ℝ) : Prop :=
  ∃ (n : ℕ) (b : Fin n → EuclideanSpace ℂ (Fin (2 * K + 1))) (θ : Fin n → ℝ) (g h₀ nz nl : ℝ),
    Orthonormal ℂ b ∧ (∀ i, b i ∈ oddSliceAmb L K) ∧
    (∀ x, x ∈ oddSliceAmb L K → x = ∑ i, ⟪b i, x⟫ • b i) ∧
    (∀ i, (oddSliceAmb L K).starProjection (squaredIndexOp K (b i)) = (θ i : ℂ) • b i) ∧
    0 < g ∧ (∀ i j, i ≠ j → g ≤ |θ i - θ j|) ∧
    (∀ i, h₀ ≤ (⟪b i, canonicalSourceOp L K (b i)⟫).re) ∧ 0 ≤ nz ∧ 0 ≤ nl ∧
    (∑ i, ‖⟪oddLeakageVec L K, canonicalSourceOp L K (b i)⟫‖ ^ 2 ≤ nz ^ 2) ∧
    (∑ i, ‖rieszCoeff (oddFlatPoleM3Amb L K) (centeredPowerVec K 5)
        (squaredIndexOp K (b i))‖ ^ 2 ≤ nl ^ 2) ∧
    -m ≤ h₀ - 2 * nz * nl / g

/-- **An even certificate gives the even slice bound** with the same floor, on the
existing native energy and physical norm. -/
theorem evenMomentSliceLowerBound_of_certificate {L : ℝ} (hL : 0 < L) {K : ℕ} {m : ℝ}
    (h : EvenGeometryResponseCertificate L K m) : EvenMomentSliceLowerBound L K m := by
  obtain ⟨n, b, θ, g, h₀, nz, nl, hb, hbS, hspan, hJ, hg, hgap, hdiag, hnz, hnl, hz, hl, hm⟩ := h
  intro u hu
  set x : EuclideanSpace ℂ (Fin (2 * K + 1)) := ((u : euclideanEvenBoundaryFlatSubspace K) :
    EuclideanSpace ℂ (Fin (2 * K + 1))) with hxdef
  have hx : x ∈ evenSliceAmb L K := (mem_evenSliceAmb_iff L K u).mpr hu
  have hflat : ∀ {y}, y ∈ evenSliceAmb L K → WithLp.ofLp y ∈ boundaryFlatSubspace K :=
    fun hy => (Submodule.mem_inf.mp (Submodule.mem_inf.mp ((mem_rieszSlice_iff _ _ _).mp hy).1).1).1
  have hrec := rieszSlice_form_lower_of_geometry_basis (evenFlatPoleAmb L K) (centeredPowerVec K 4)
    (squaredIndexOp K) (canonicalSourceOp L K) (squaredIndexOp_isSymmetric K)
    (canonicalSourceOp_isSymmetric L K) (fun y hy => squaredIndexOp_mem_evenFlatPole hL K hy)
    (fun y w hy hw => squaredIndexOp_source_commute_form hL K (hflat hy) (hflat hw))
    b hb hbS θ hJ hg hgap hdiag hnz hnl hz hl (fun i => ⟪b i, x⟫)
  rw [← hspan x hx] at hrec
  have hE : evenNativeEnergy L K u = (⟪x, canonicalSourceOp L K x⟫).re := by
    unfold evenNativeEnergy
    rw [inner_poleNeutralEvenCompressedCanonical_self, ← canonicalSourceOp_isSymmetric]
  have hn : ‖u‖ = ‖x‖ := rfl
  rw [hE, hn]
  have hsq : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **An odd certificate gives the odd slice bound** with the same floor. -/
theorem oddMomentSliceLowerBound_of_certificate {L : ℝ} (hL : 0 < L) {K : ℕ} {m : ℝ}
    (h : OddGeometryResponseCertificate L K m) : OddMomentSliceLowerBound L K m := by
  obtain ⟨n, b, θ, g, h₀, nz, nl, hb, hbS, hspan, hJ, hg, hgap, hdiag, hnz, hnl, hz, hl, hm⟩ := h
  intro v hv
  set x : EuclideanSpace ℂ (Fin (2 * K + 1)) := ((v : euclideanOddBoundaryFlatSubspace K) :
    EuclideanSpace ℂ (Fin (2 * K + 1))) with hxdef
  have hx : x ∈ oddSliceAmb L K := (mem_oddSliceAmb_iff L K v).mpr hv
  have hflat : ∀ {y}, y ∈ oddSliceAmb L K → WithLp.ofLp y ∈ boundaryFlatSubspace K := by
    intro y hy
    have h1 := ((mem_rieszSlice_iff _ _ _).mp hy).1
    simp only [oddFlatPoleM3Amb, Submodule.mem_inf] at h1
    exact (Submodule.mem_inf.mp h1.1.1).1
  have hrec := rieszSlice_form_lower_of_geometry_basis (oddFlatPoleM3Amb L K) (centeredPowerVec K 5)
    (squaredIndexOp K) (canonicalSourceOp L K) (squaredIndexOp_isSymmetric K)
    (canonicalSourceOp_isSymmetric L K) (fun y hy => squaredIndexOp_mem_oddFlatPoleM3 hL K hy)
    (fun y w hy hw => squaredIndexOp_source_commute_form hL K (hflat hy) (hflat hw))
    b hb hbS θ hJ hg hgap hdiag hnz hnl hz hl (fun i => ⟪b i, x⟫)
  rw [← hspan x hx] at hrec
  have hE : oddNativeEnergy L K v = (⟪x, canonicalSourceOp L K x⟫).re := by
    unfold oddNativeEnergy
    rw [inner_poleNeutralOddCompressedCanonical_self, ← canonicalSourceOp_isSymmetric]
  have hn : ‖v‖ = ‖x‖ := rfl
  rw [hE, hn]
  have hsq : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **(SG) with explicit geometry.** In one fixed parity, a geometry-response
certificate with polynomial floor `C (1 + L)^d` at every late aperture and the literal
quartic cutoff. The gap, diagonal and response estimates inside it are OPEN. -/
def FixedParityGeometryResponsePolynomial : Prop :=
  (∃ (C : ℝ) (d : ℕ) (L₀ : ℝ), 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      EvenGeometryResponseCertificate L (originalDetectorQuarticCutoff L) (C * (1 + L) ^ d)) ∨
    (∃ (C : ℝ) (d : ℕ) (L₀ : ℝ), 0 < C ∧ ∀ L : ℝ, L₀ ≤ L →
      OddGeometryResponseCertificate L (originalDetectorQuarticCutoff L) (C * (1 + L) ^ d))

/-- (SG) with explicit geometry implies (PG). -/
theorem fixed_parity_polynomial_of_geometry_response (h : FixedParityGeometryResponsePolynomial) :
    FixedParityPolynomialMomentSliceBounds := by
  rcases h with ⟨C, d, L₀, hC, hb⟩ | ⟨C, d, L₀, hC, hb⟩
  · refine Or.inl ⟨C, d, max L₀ 1, hC, fun L hL => ?_⟩
    have hL0 : 0 < L := by linarith [le_max_right L₀ 1]
    exact evenMomentSliceLowerBound_of_certificate hL0 (hb L ((le_max_left _ _).trans hL))
  · refine Or.inr ⟨C, d, max L₀ 1, hC, fun L hL => ?_⟩
    have hL0 : 0 < L := by linarith [le_max_right L₀ 1]
    exact oddMomentSliceLowerBound_of_certificate hL0 (hb L ((le_max_left _ _).trans hL))

/-- **Conditional reduction (SG) → (PG) → RH.** The premise is OPEN. -/
theorem riemannHypothesis_of_geometry_response_polynomial
    (h : FixedParityGeometryResponsePolynomial) : RiemannHypothesis :=
  riemannHypothesis_of_fixed_parity_polynomial (fixed_parity_polynomial_of_geometry_response h)

end Native

end Zeta23.OPICARound4.ArithmeticFrontier
