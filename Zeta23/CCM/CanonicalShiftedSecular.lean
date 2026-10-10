import Zeta23.CCM.CanonicalSecularResolvent

noncomputable section

namespace Zeta23.CCM

open scoped ComplexConjugate

/-!
# POST285 (Steps 58–60, 64; M26–M28) and branch analysis (M14 / M77):
shifted secular equation, simple even roots, odd-first and tied contacts

`CanonicalSecularResolvent.lean` (M74) proves the secular algebra of the
rank-one relation `B_L D - D A_L = g ⊗ H_L` at the spectral value `0`.  The
relation is unchanged by a common spectral shift,
`(B_L - λ) D - D (A_L - λ) = g ⊗ H_L`, and by exchanging the two sectors,
`A_L D⁻¹ - D⁻¹ B_L = (-D⁻¹ g) ⊗ (H_L ∘ D⁻¹)`.  This module records both and
instantiates them on the actual canonical parity compressions.  Proved:

* (Steps 58–59, 64) for real `λ` below the odd Rayleigh bottom, with
  `v_L(λ) = D⁻¹ (B_L - λ)⁻¹ g` and `T_L(λ) = S_L(v_L(λ))`:
  `(A_L - λ) v_L(λ) = (1 - T_L(λ)) • D⁻¹ g`,
  `det (A_L - λ) = det (B_L - λ) · (1 - T_L(λ))`,
  `λ` is an even eigenvalue iff `T_L(λ) = 1`, every even eigenvector at `λ`
  is `S_L(z) • v_L(λ)`, and the even eigenspace at `λ` has dimension `≤ 1`
  (simple even roots below the odd floor; geometric simplicity, which for the
  symmetric `A_L` is the full multiplicity);
* (Step 60) at an even contact with positive odd bottom, with `x_L = v_L(0)`,
  `d = D⁻¹ g` and `w_L = D⁻¹ B_L⁻¹ B_L⁻¹ g`: the exact overlap identity
  `⟪x_L, d⟫ · S_L(w_L) = ‖x_L‖²`, so `⟪x_L, d⟫ ≠ 0` and `S_L(w_L) ≠ 0`;
* (odd-first branch) when the even bottom is positive, every odd zero mode lies
  on the line `ℂ ∙ D A_L⁻¹ D⁻¹ g`, `B_L` is singular iff
  `S_L(A_L⁻¹ D⁻¹ g) = -1`, and `det B_L = det A_L · (1 + S_L(A_L⁻¹ D⁻¹ g))`;
* (tied branch) for all `L > 0`, `K ≥ 2`: if `A_L z = 0` and `B_L y = 0` then
  `S_L(z) · ⟪y, g⟫ = 0`.

Firewalls:
* nothing here asserts that any contact exists or does not exist, and no branch
  is excluded;
* `T_L(λ) = 1` and `S_L(A_L⁻¹ D⁻¹ g) = -1` are *equivalent* to the
  corresponding contacts, never independent opposite-side inputs;
* the sign of `S_L(w_L)` (the plan's `c* > 0`, i.e. `⟪x_L, d⟫ > 0`) is not
  proved here: it needs determinant-derivative or first-crossing input;
* no `λ`-monotonicity of `T_L` and no aperture-derivative sign is claimed;
* `D` is never assumed unitary; `A_L` is not the scalar `𝓐_L`;
* no F04, no RH, no new axiom.
-/

/-! ## Abstract layer -/

section Abstract

variable {E O : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup O] [Module ℂ O]
  {A : E →ₗ[ℂ] E} {B : O →ₗ[ℂ] O} {D : E ≃ₗ[ℂ] O} {g : O} {H : E →ₗ[ℂ] ℂ}

/-- A common spectral shift preserves the rank-one intertwining. -/
theorem RankOneIntertwining.shift (hrank : RankOneIntertwining A B D g H) (μ : ℂ) :
    RankOneIntertwining (A - μ • LinearMap.id) (B - μ • LinearMap.id) D g H := by
  intro v
  rw [← hrank v]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
    map_smul]
  abel

/-- Exchanging the two sectors gives another rank-one intertwining:
`A D⁻¹ - D⁻¹ B = (-D⁻¹ g) ⊗ (H ∘ D⁻¹)`. -/
theorem RankOneIntertwining.swap (hrank : RankOneIntertwining A B D g H) :
    RankOneIntertwining B A D.symm (-D.symm g) (H ∘ₗ (D.symm : O →ₗ[ℂ] E)) := by
  intro y
  have h := hrank (D.symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  have h2 := congrArg D.symm h
  rw [map_sub, LinearEquiv.symm_apply_apply, map_smul] at h2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, smul_neg]
  rw [← h2]
  abel

end Abstract

section AbstractInner

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {Es : Submodule ℂ W} {Os : Submodule ℂ V}
  {A : Es →ₗ[ℂ] Es} {B : Os →ₗ[ℂ] Os} {D : Es ≃ₗ[ℂ] Os} {g : Os} {H : Es →ₗ[ℂ] ℂ}
  {Bi : Os ≃ₗ[ℂ] Os}

/-- **Tied contacts:** if `B` is symmetric, `A z = 0` and `B y = 0`, then
`H z · ⟪y, g⟫ = 0`. -/
theorem tied_contact_orthogonality
    (hB : ∀ y w : Os, inner ℂ (B y) w = inner ℂ y (B w))
    (hrank : RankOneIntertwining A B D g H) {z : Es} {y : Os}
    (hz : A z = 0) (hy : B y = 0) :
    H z * inner ℂ y g = 0 := by
  have h := hrank z
  rw [hz, map_zero, sub_zero] at h
  have h1 : inner ℂ y (B (D z)) = 0 := by rw [← hB, hy, inner_zero_left]
  rw [h, inner_smul_right] at h1
  exact h1

/-- `A w = D⁻¹ B⁻¹ g - H w • D⁻¹ g` for `w = D⁻¹ B⁻¹ B⁻¹ g`. -/
theorem apply_secularResolventRay_resolvent
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y) :
    A (secularResolventRay Bi D (Bi.symm g)) =
      secularResolventRay Bi D g -
        H (secularResolventRay Bi D (Bi.symm g)) • D.symm g := by
  apply D.injective
  have h := hrank (secularResolventRay Bi D (Bi.symm g))
  rw [D_secularResolventRay, apply_secularResolventVector hBi] at h
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, D_secularResolventRay, ← h]
  simp [secularResolventVector]

/-- **Step 60, exact overlap identity:** at contact (`H x = 1`) with `A`
symmetric, `⟪x, D⁻¹ g⟫ · H(D⁻¹ B⁻¹ B⁻¹ g) = ‖x‖²`. -/
theorem secular_overlap_identity
    (hA : ∀ u w : Es, inner ℂ (A u) w = inner ℂ u (A w))
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y)
    (hT : H (secularResolventRay Bi D g) = 1) :
    inner ℂ (secularResolventRay Bi D g) (D.symm g) *
        H (secularResolventRay Bi D (Bi.symm g)) =
      ((‖secularResolventRay Bi D g‖ ^ 2 : ℝ) : ℂ) := by
  set x := secularResolventRay Bi D g
  set w := secularResolventRay Bi D (Bi.symm g)
  have hAx : A x = 0 := by
    rw [apply_secularResolventRay hrank hBi, hT, sub_self, zero_smul]
  have hAw := apply_secularResolventRay_resolvent hrank hBi (A := A) (H := H)
  have h0 : inner ℂ x (A w) = 0 := by rw [← hA, hAx, inner_zero_left]
  rw [hAw, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    sub_eq_zero] at h0
  rw [mul_comm, ← h0]
  push_cast
  rfl

end AbstractInner

theorem finrank_span_singleton_le_one {M : Type*} [AddCommGroup M] [Module ℂ M] (x : M) :
    Module.finrank ℂ (ℂ ∙ x) ≤ 1 := by
  classical
  simpa using finrank_span_le_card (R := ℂ) ({x} : Set M)

/-! ## Canonical shifted secular equation -/

section CanonicalShifted

variable {L : ℝ} {K : ℕ}

/-- `B_L - λ`, the shifted odd compression. -/
def oddShiftedCanonical (L : ℝ) (K : ℕ) (lam : ℝ) :
    euclideanOddBoundaryFlatSubspace K →ₗ[ℂ] euclideanOddBoundaryFlatSubspace K :=
  oddCompressedCanonical L K - (lam : ℂ) • LinearMap.id

/-- `A_L - λ`, the shifted even compression. -/
def evenShiftedCanonical (L : ℝ) (K : ℕ) (lam : ℝ) :
    euclideanEvenBoundaryFlatSubspace K →ₗ[ℂ] euclideanEvenBoundaryFlatSubspace K :=
  evenCompressedCanonical L K - (lam : ℂ) • LinearMap.id

theorem re_inner_ofReal_smul_self {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (lam : ℝ) (y : V) :
    (inner ℂ ((lam : ℂ) • y) y).re = lam * ‖y‖ ^ 2 := by
  rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) y

theorem oddShiftedCanonical_coercive (L : ℝ) (K : ℕ) (lam : ℝ)
    (y : euclideanOddBoundaryFlatSubspace K) :
    (parityRayleighBottom .odd L K - lam) * ‖y‖ ^ 2 ≤
      (inner ℂ (oddShiftedCanonical L K lam y) y).re := by
  have h := oddCompressedCanonical_coercive L K y
  have hs := re_inner_ofReal_smul_self lam y
  simp only [oddShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, inner_sub_left, Complex.sub_re]
  linarith

theorem oddShiftedCanonical_injective {lam : ℝ}
    (hlam : lam < parityRayleighBottom .odd L K) :
    Function.Injective (oddShiftedCanonical L K lam) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have h := oddShiftedCanonical_coercive L K lam y
  rw [hy, inner_zero_left, Complex.zero_re] at h
  have hc : 0 < parityRayleighBottom .odd L K - lam := sub_pos.mpr hlam
  have hn : ‖y‖ ^ 2 ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have := mul_pos hc hneg
    linarith
  have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp this

/-- `B_L - λ` as a linear equivalence below the odd floor. -/
def oddShiftedCanonicalEquiv (L : ℝ) (K : ℕ) {lam : ℝ}
    (hlam : lam < parityRayleighBottom .odd L K) :
    euclideanOddBoundaryFlatSubspace K ≃ₗ[ℂ] euclideanOddBoundaryFlatSubspace K :=
  LinearEquiv.ofInjectiveEndo (oddShiftedCanonical L K lam)
    (oddShiftedCanonical_injective hlam)

theorem oddShiftedCanonicalEquiv_apply {lam : ℝ}
    (hlam : lam < parityRayleighBottom .odd L K) (y : euclideanOddBoundaryFlatSubspace K) :
    oddShiftedCanonicalEquiv L K hlam y = oddShiftedCanonical L K lam y := rfl

/-- Shifted resolvent ray `v_L(λ) = D⁻¹ (B_L - λ)⁻¹ g`. -/
def canonicalShiftedRay (L : ℝ) (K : ℕ) (hK : 2 ≤ K) {lam : ℝ}
    (hlam : lam < parityRayleighBottom .odd L K) :
    euclideanEvenBoundaryFlatSubspace K :=
  secularResolventRay (oddShiftedCanonicalEquiv L K hlam)
    (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)) (oddCubicCompressionVector K)

/-- Shifted rank-one intertwining `(B_L - λ) D - D (A_L - λ) = g ⊗ H_L`. -/
theorem canonical_shifted_rankOneIntertwining (hL : 0 < L) (hK : 2 ≤ K) (lam : ℝ) :
    RankOneIntertwining (evenShiftedCanonical L K lam) (oddShiftedCanonical L K lam)
      (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
      (oddCubicCompressionVector K) (cubicDefectFunctional L K) :=
  (canonical_rankOneIntertwining hL K hK).shift (lam : ℂ)

variable (hL : 0 < L) (hK : 2 ≤ K) {lam : ℝ} (hlam : lam < parityRayleighBottom .odd L K)
include hL hK hlam

/-- **Steps 58–59 (canonical):**
`(A_L - λ) v_L(λ) = (1 - T_L(λ)) • D⁻¹ g` with `T_L(λ) = S_L(v_L(λ))`. -/
theorem canonical_shifted_apply_ray :
    evenShiftedCanonical L K lam (canonicalShiftedRay L K hK hlam) =
      (1 - explicitCanonicalSourceMoment L K (canonicalShiftedRay L K hK hlam)) •
        (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact apply_secularResolventRay (canonical_shifted_rankOneIntertwining hL hK lam)
    (oddShiftedCanonicalEquiv_apply hlam)

/-- **Step 58 (canonical), shifted secular determinant:**
`det (A_L - λ) = det (B_L - λ) · (1 - T_L(λ))`. -/
theorem canonical_shifted_det_eq :
    LinearMap.det (evenShiftedCanonical L K lam) =
      LinearMap.det (oddShiftedCanonical L K lam) *
        (1 - explicitCanonicalSourceMoment L K (canonicalShiftedRay L K hK hlam)) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact det_eq_det_mul_one_sub_secularResolventScalar
    (canonical_shifted_rankOneIntertwining hL hK lam) (oddShiftedCanonicalEquiv_apply hlam)

/-- **Step 58 (canonical), shifted determinant ratio:**
`det (A_L - λ) / det (B_L - λ) = 1 - T_L(λ)`. -/
theorem canonical_shifted_det_div_eq :
    LinearMap.det (evenShiftedCanonical L K lam) /
        LinearMap.det (oddShiftedCanonical L K lam) =
      1 - explicitCanonicalSourceMoment L K (canonicalShiftedRay L K hK hlam) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact det_div_det_eq_one_sub_secularResolventScalar
    (canonical_shifted_rankOneIntertwining hL hK lam) (oddShiftedCanonicalEquiv_apply hlam)

omit hL hK hlam in
theorem mem_ker_evenShiftedCanonical_iff (z : euclideanEvenBoundaryFlatSubspace K) :
    evenShiftedCanonical L K lam z = 0 ↔ evenCompressedCanonical L K z = (lam : ℂ) • z := by
  simp only [evenShiftedCanonical, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- **Step 59 (canonical), shifted secular criterion:** below the odd floor,
`λ` is an eigenvalue of `A_L` iff `T_L(λ) = 1`.  This is the eigenvalue
condition itself, not an independent input. -/
theorem canonical_shifted_eigen_iff :
    explicitCanonicalSourceMoment L K (canonicalShiftedRay L K hK hlam) = 1 ↔
      ∃ z : euclideanEvenBoundaryFlatSubspace K, z ≠ 0 ∧
        evenCompressedCanonical L K z = (lam : ℂ) • z := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  refine (secularResolventScalar_eq_one_iff (canonical_shifted_rankOneIntertwining hL hK lam)
    (oddShiftedCanonicalEquiv_apply hlam) (oddCubicCompressionVector_ne_zero K hK)).trans ?_
  simp only [mem_ker_evenShiftedCanonical_iff]

/-- **Step 64 (canonical), eigenvector rigidity:** below the odd floor every
even eigenvector at `λ` is `S_L(z) • v_L(λ)`. -/
theorem canonical_shifted_eigenvector_eq_smul {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = (lam : ℂ) • z) :
    z = explicitCanonicalSourceMoment L K z • canonicalShiftedRay L K hK hlam := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact eq_smul_secularResolventRay_of_apply_eq_zero
    (canonical_shifted_rankOneIntertwining hL hK lam) (oddShiftedCanonicalEquiv_apply hlam)
    ((mem_ker_evenShiftedCanonical_iff z).mpr hz)

/-- **Step 64 (canonical):** below the odd floor the even eigenspace at `λ` lies
on the shifted resolvent line. -/
theorem canonical_eigenspace_le_span :
    Module.End.eigenspace (evenCompressedCanonical L K) (lam : ℂ) ≤
      ℂ ∙ canonicalShiftedRay L K hK hlam := by
  intro z hz
  rw [Module.End.mem_eigenspace_iff] at hz
  rw [Submodule.mem_span_singleton]
  exact ⟨_, (canonical_shifted_eigenvector_eq_smul hL hK hlam hz).symm⟩

/-- **Step 64 (canonical), simple even roots below the odd floor:** for real
`λ` below the odd Rayleigh bottom, the even eigenspace of `A_L` at `λ` has
dimension at most one. -/
theorem canonical_finrank_eigenspace_le_one :
    Module.finrank ℂ (Module.End.eigenspace (evenCompressedCanonical L K) (lam : ℂ)) ≤ 1 := by
  calc Module.finrank ℂ (Module.End.eigenspace (evenCompressedCanonical L K) (lam : ℂ))
      ≤ Module.finrank ℂ (ℂ ∙ canonicalShiftedRay L K hK hlam) :=
        Submodule.finrank_mono (canonical_eigenspace_le_span hL hK hlam)
    _ ≤ 1 := finrank_span_singleton_le_one _

end CanonicalShifted

/-! ## Canonical contact overlap (Step 60) -/

section CanonicalOverlap

variable {L : ℝ} {K : ℕ} (hL : 0 < L) (hK : 2 ≤ K)
  (hpos : 0 < parityRayleighBottom .odd L K)
include hL hK hpos

/-- **Step 60 (canonical), exact overlap identity at even contact:** with
`x_L = D⁻¹ B_L⁻¹ g`, `d = D⁻¹ g` and `w_L = D⁻¹ B_L⁻¹ B_L⁻¹ g`, contact
`S_L(x_L) = 1` gives `⟪x_L, d⟫ · S_L(w_L) = ‖x_L‖²`.  The sign of `S_L(w_L)`
is not asserted. -/
theorem canonical_contact_overlap
    (hT : explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1) :
    inner ℂ (canonicalResolventRay L K hK hpos)
        ((euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K)) *
      explicitCanonicalSourceMoment L K
        (secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
          (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
          ((oddCompressedCanonicalEquiv L K hpos).symm (oddCubicCompressionVector K))) =
      ((‖canonicalResolventRay L K hK hpos‖ ^ 2 : ℝ) : ℂ) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK] at hT ⊢
  exact secular_overlap_identity (parityCompressedCanonical_isSymmetric .even L K)
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos) hT

/-- **Step 60 (canonical):** at an even contact the overlap `⟪x_L, D⁻¹ g⟫` and
the resolvent slope `S_L(w_L)` are both nonzero. -/
theorem canonical_contact_overlap_ne_zero
    (hT : explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1) :
    inner ℂ (canonicalResolventRay L K hK hpos)
        ((euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K)) ≠ 0 ∧
      explicitCanonicalSourceMoment L K
        (secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
          (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
          ((oddCompressedCanonicalEquiv L K hpos).symm (oddCubicCompressionVector K))) ≠ 0 := by
  have h := canonical_contact_overlap hL hK hpos hT
  have hx : canonicalResolventRay L K hK hpos ≠ 0 :=
    secularResolventRay_ne_zero (oddCubicCompressionVector_ne_zero K hK)
  have hn : ((‖canonicalResolventRay L K hK hpos‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖canonicalResolventRay L K hK hpos‖ := norm_pos_iff.mpr hx
    exact_mod_cast (pow_pos this 2).ne'
  rw [← h] at hn
  exact ⟨left_ne_zero_of_mul hn, right_ne_zero_of_mul hn⟩

/-- **Step 60 (canonical), weak modulus bound:** at an even contact,
`‖x_L‖ ≤ ‖D⁻¹ g‖ · ‖S_L(w_L)‖` (the plan's `c* ≥ ‖v‖/‖d‖`, in modulus only). -/
theorem canonical_contact_overlap_norm_le
    (hT : explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1) :
    ‖canonicalResolventRay L K hK hpos‖ ≤
      ‖(euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K)‖ *
        ‖explicitCanonicalSourceMoment L K
          (secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
            (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
            ((oddCompressedCanonicalEquiv L K hpos).symm (oddCubicCompressionVector K)))‖ := by
  have h := congrArg norm (canonical_contact_overlap hL hK hpos hT)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
  have hx : canonicalResolventRay L K hK hpos ≠ 0 :=
    secularResolventRay_ne_zero (oddCubicCompressionVector_ne_zero K hK)
  have hxpos : 0 < ‖canonicalResolventRay L K hK hpos‖ := norm_pos_iff.mpr hx
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (canonicalResolventRay L K hK hpos)
    ((euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm (oddCubicCompressionVector K))
  set a := ‖canonicalResolventRay L K hK hpos‖
  set b := ‖(euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
    (oddCubicCompressionVector K)‖
  set c := ‖explicitCanonicalSourceMoment L K
    (secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
      (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
      ((oddCompressedCanonicalEquiv L K hpos).symm (oddCubicCompressionVector K)))‖
  have hc : 0 ≤ c := norm_nonneg _
  have h2 : a ^ 2 ≤ a * b * c := by
    rw [← h]
    exact mul_le_mul_of_nonneg_right hcs hc
  nlinarith

end CanonicalOverlap

/-! ## Odd-first branch (even bottom positive) -/

section OddFirst

variable {L : ℝ} {K : ℕ}

theorem evenCompressedCanonical_coercive (L : ℝ) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    parityRayleighBottom .even L K * ‖z‖ ^ 2 ≤
      (inner ℂ (evenCompressedCanonical L K z) z).re :=
  parityRayleighBottom_mul_norm_sq_le .even L K z

theorem evenCompressedCanonical_injective
    (hposE : 0 < parityRayleighBottom .even L K) :
    Function.Injective (evenCompressedCanonical L K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h := evenCompressedCanonical_coercive L K z
  rw [hz, inner_zero_left, Complex.zero_re] at h
  have hn : ‖z‖ ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hposE hc
    linarith
  have : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
  exact norm_eq_zero.mp this

/-- `A_L` as a linear equivalence when the even bottom is positive. -/
def evenCompressedCanonicalEquiv (L : ℝ) (K : ℕ)
    (hposE : 0 < parityRayleighBottom .even L K) :
    euclideanEvenBoundaryFlatSubspace K ≃ₗ[ℂ] euclideanEvenBoundaryFlatSubspace K :=
  LinearEquiv.ofInjectiveEndo (evenCompressedCanonical L K)
    (evenCompressedCanonical_injective hposE)

theorem evenCompressedCanonicalEquiv_apply
    (hposE : 0 < parityRayleighBottom .even L K) (z : euclideanEvenBoundaryFlatSubspace K) :
    evenCompressedCanonicalEquiv L K hposE z = evenCompressedCanonical L K z := rfl

/-- Dual even vector `u_L = A_L⁻¹ D⁻¹ g`. -/
def canonicalDualVector (L : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hposE : 0 < parityRayleighBottom .even L K) :
    euclideanEvenBoundaryFlatSubspace K :=
  (evenCompressedCanonicalEquiv L K hposE).symm
    ((euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
      (oddCubicCompressionVector K))

variable (hL : 0 < L) (hK : 2 ≤ K) (hposE : 0 < parityRayleighBottom .even L K)
include hL hK hposE

omit hL in
/-- The dual secular ray of the swapped instance is `-(D u_L)`. -/
theorem secularResolventRay_swap_eq :
    secularResolventRay (evenCompressedCanonicalEquiv L K hposE)
        (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
        (-(euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K)) =
      -(euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)
          (canonicalDualVector L K hK hposE)) := by
  simp [secularResolventRay, canonicalDualVector]

/-- **Odd-first branch, kernel rigidity:** when the even bottom is positive,
every odd zero mode lies on the line `ℂ ∙ D A_L⁻¹ D⁻¹ g`. -/
theorem canonical_odd_ker_le_span :
    LinearMap.ker (oddCompressedCanonical L K) ≤
      ℂ ∙ euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)
        (canonicalDualVector L K hK hposE) := by
  have h := ker_le_span_secularResolventRay
    (canonical_rankOneIntertwining hL K hK).swap (evenCompressedCanonicalEquiv_apply hposE)
  rw [secularResolventRay_swap_eq hK hposE, ← Set.neg_singleton, Submodule.span_neg] at h
  exact h

/-- **Odd-first branch, finrank:** the odd kernel has dimension at most one
when the even bottom is positive. -/
theorem canonical_finrank_odd_ker_le_one :
    Module.finrank ℂ (LinearMap.ker (oddCompressedCanonical L K)) ≤ 1 :=
  (Submodule.finrank_mono (canonical_odd_ker_le_span hL hK hposE)).trans
    (finrank_span_singleton_le_one _)

/-- **Odd-first branch, contact criterion:** when the even bottom is positive,
`B_L` has a nonzero zero mode iff `S_L(A_L⁻¹ D⁻¹ g) = -1`.  This is the odd
contact itself, never an independent input. -/
theorem canonical_odd_contact_iff :
    explicitCanonicalSourceMoment L K (canonicalDualVector L K hK hposE) = -1 ↔
      ∃ y : euclideanOddBoundaryFlatSubspace K, y ≠ 0 ∧ oddCompressedCanonical L K y = 0 := by
  have hg : -(euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
      (oddCubicCompressionVector K) ≠ 0 := by
    intro h0
    apply oddCubicCompressionVector_ne_zero K hK
    have := congrArg (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)) (neg_eq_zero.mp h0)
    simpa using this
  rw [← secularResolventScalar_eq_one_iff (canonical_rankOneIntertwining hL K hK).swap
    (evenCompressedCanonicalEquiv_apply hposE) hg, secularResolventRay_swap_eq hK hposE]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_neg,
    LinearEquiv.symm_apply_apply]
  rw [cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  constructor
  · intro h
    rw [h, neg_neg]
  · intro h
    rw [← neg_neg (explicitCanonicalSourceMoment L K _), h]

/-- **Odd-first branch, determinant:**
`det B_L = det A_L · (1 + S_L(A_L⁻¹ D⁻¹ g))`. -/
theorem canonical_odd_det_eq :
    LinearMap.det (oddCompressedCanonical L K) =
      LinearMap.det (evenCompressedCanonical L K) *
        (1 + explicitCanonicalSourceMoment L K (canonicalDualVector L K hK hposE)) := by
  have h := det_eq_det_mul_one_sub_secularResolventScalar
    (canonical_rankOneIntertwining hL K hK).swap (evenCompressedCanonicalEquiv_apply hposE)
  rw [secularResolventRay_swap_eq hK hposE] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_neg,
    LinearEquiv.symm_apply_apply] at h
  rw [h, cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK, sub_neg_eq_add]

end OddFirst

/-! ## Tied branch -/

/-- **Tied branch:** at any aperture, if `A_L z = 0` and `B_L y = 0` then
`S_L(z) · ⟪y, g⟫ = 0`: either the even zero mode has vanishing source moment
(and then `D z ∈ ker B_L`), or `g ⊥ ker B_L`. -/
theorem canonical_tied_contact_orthogonality {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
    {z : euclideanEvenBoundaryFlatSubspace K} {y : euclideanOddBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) (hy : oddCompressedCanonical L K y = 0) :
    explicitCanonicalSourceMoment L K z * inner ℂ y (oddCubicCompressionVector K) = 0 := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact tied_contact_orthogonality (oddCompressedCanonical_inner_symm L K)
    (canonical_rankOneIntertwining hL K hK) hz hy

end Zeta23.CCM

#print axioms Zeta23.CCM.RankOneIntertwining.shift
#print axioms Zeta23.CCM.RankOneIntertwining.swap
#print axioms Zeta23.CCM.tied_contact_orthogonality
#print axioms Zeta23.CCM.secular_overlap_identity
#print axioms Zeta23.CCM.canonical_shifted_apply_ray
#print axioms Zeta23.CCM.canonical_shifted_det_eq
#print axioms Zeta23.CCM.canonical_shifted_det_div_eq
#print axioms Zeta23.CCM.canonical_shifted_eigen_iff
#print axioms Zeta23.CCM.canonical_shifted_eigenvector_eq_smul
#print axioms Zeta23.CCM.canonical_eigenspace_le_span
#print axioms Zeta23.CCM.canonical_finrank_eigenspace_le_one
#print axioms Zeta23.CCM.canonical_contact_overlap
#print axioms Zeta23.CCM.canonical_contact_overlap_ne_zero
#print axioms Zeta23.CCM.canonical_contact_overlap_norm_le
#print axioms Zeta23.CCM.canonical_odd_ker_le_span
#print axioms Zeta23.CCM.canonical_finrank_odd_ker_le_one
#print axioms Zeta23.CCM.canonical_odd_contact_iff
#print axioms Zeta23.CCM.canonical_odd_det_eq
#print axioms Zeta23.CCM.canonical_tied_contact_orthogonality
