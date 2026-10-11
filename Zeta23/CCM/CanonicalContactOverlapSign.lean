import Zeta23.CCM.CanonicalShiftedSecular
import Mathlib.Analysis.InnerProductSpace.Spectrum

noncomputable section

namespace Zeta23.CCM

open scoped ComplexConjugate

/-!
# POST285 (Step 60; M28): sign of the contact resolvent overlap

`CanonicalShiftedSecular.lean` proves the sign-free overlap identity
`⟪x_L, D⁻¹ g⟫ · S_L(w_L) = ‖x_L‖²` at an even contact, with
`x_L = D⁻¹ B_L⁻¹ g` and `w_L = D⁻¹ B_L⁻¹ B_L⁻¹ g`.  This module proves the
sign at a contact where the even compression is positive semidefinite (the
first-crossing geometry: `0 ≤` even Rayleigh bottom) and the odd bottom is
positive:

* `S_L(w_L)` is real and strictly positive, and
* `⟪x_L, D⁻¹ g⟫` is real and strictly positive (the plan's
  `⟪v, d⟫ = ‖v‖² / c* > 0`).

Route, entirely algebraic plus one elementary limit:
1. a coercive symmetric map has a real positive determinant
   (`LinearMap.IsSymmetric.det_eq_prod_eigenvalues`);
2. for real `λ < 0`, both `A_L - λ` and `B_L - λ` are coercive, so the shifted
   secular determinant gives `1 - T_L(λ) = det(A_L - λ)/det(B_L - λ) > 0`;
3. the resolvent identity `(B - λ)⁻¹ g - B⁻¹ g = λ (B - λ)⁻¹ B⁻¹ g` and contact
   `T_L(0) = 1` give `1 - T_L(λ) = -λ c_λ`, so each `c_λ` is real positive;
4. `|c_λ - S_L(w_L)| ≤ |λ| M` with an explicit `M`, so `S_L(w_L)` is a limit of
   real positive numbers, hence real and `≥ 0`; it is nonzero by the overlap
   identity.

Hypotheses are the contact itself (`S_L(x_L) = 1`) and the first-crossing
geometry (`A_L ≽ 0`, `B_L > 0`).  Firewalls:
* nothing asserts that a contact exists or does not exist;
* `T ≤ 1` is never used to infer `A_L ≽ 0`: positivity of `A_L` is a
  hypothesis, and the conclusion is about the overlap, not about `A_L`;
* `D` is not assumed unitary; `A_L` is not the scalar `𝓐_L`;
* no F04, no RH, no new axiom.
-/

/-! ## Determinant of a coercive symmetric map -/

section DetPos

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Es : Submodule ℂ W}
  [FiniteDimensional ℂ Es]

/-- A coercive symmetric map on a finite-dimensional complex inner-product space
has a real, strictly positive determinant. -/
theorem exists_det_eq_ofReal_pos_of_coercive {T : Es →ₗ[ℂ] Es} (hT : T.IsSymmetric)
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ (inner ℂ (T x) x).re) :
    ∃ p : ℝ, 0 < p ∧ LinearMap.det T = (p : ℂ) := by
  refine ⟨∏ i, hT.eigenvalues rfl i, Finset.prod_pos fun i _ => ?_, ?_⟩
  · have hb : ‖hT.eigenvectorBasis rfl i‖ = 1 := (hT.eigenvectorBasis rfl).orthonormal.1 i
    have h := hcoer (hT.eigenvectorBasis rfl i)
    rw [hT.apply_eigenvectorBasis, inner_smul_left, inner_self_eq_norm_sq_to_K, hb] at h
    simp only [RCLike.conj_ofReal, one_pow, mul_one, RCLike.ofReal_one] at h
    have h' : c ≤ hT.eigenvalues rfl i := by simpa using h
    linarith
  · rw [hT.det_eq_prod_eigenvalues rfl]
    push_cast
    rfl

end DetPos

/-! ## An elementary limit -/

/-- If `c` is within `ε M` of a real positive number for every `ε > 0`, then
`c` is real and `0 ≤ re c`. -/
theorem re_nonneg_and_im_eq_zero_of_approx {c : ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ ε : ℝ, 0 < ε → ∃ c' : ℂ, c'.im = 0 ∧ 0 < c'.re ∧ ‖c - c'‖ ≤ ε * M) :
    0 ≤ c.re ∧ c.im = 0 := by
  have hM1 : 0 < M + 1 := by linarith
  constructor
  · by_contra hneg
    push Not at hneg
    obtain ⟨c', -, hc're, hc'⟩ := h (-c.re / (2 * (M + 1))) (by
      apply div_pos (by linarith) (by positivity))
    have hre : |(c - c').re| ≤ ‖c - c'‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at hre
    have hεM : -c.re / (2 * (M + 1)) * M < -c.re := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have := (abs_le.mp (hre.trans hc')).1
    linarith
  · by_contra hne
    have hpos : 0 < |c.im| := abs_pos.mpr hne
    obtain ⟨c', hc'im, -, hc'⟩ := h (|c.im| / (2 * (M + 1))) (by positivity)
    have him : |(c - c').im| ≤ ‖c - c'‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hc'im, sub_zero] at him
    have hεM : |c.im| / (2 * (M + 1)) * M < |c.im| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith [him.trans hc']

/-! ## Abstract overlap sign -/

section OverlapSign

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {Es : Submodule ℂ W} {Os : Submodule ℂ V} [FiniteDimensional ℂ Es] [FiniteDimensional ℂ Os]

/-- Shifted map `T - λ` for real `λ`. -/
abbrev realShift {M : Type*} [AddCommGroup M] [Module ℂ M] (T : M →ₗ[ℂ] M) (lam : ℝ) :
    M →ₗ[ℂ] M :=
  T - (lam : ℂ) • LinearMap.id

theorem realShift_isSymmetric {S : Submodule ℂ W} {T : S →ₗ[ℂ] S} (hT : T.IsSymmetric)
    (lam : ℝ) : (realShift T lam).IsSymmetric := by
  intro x y
  simp only [realShift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    hT x y]

theorem realShift_coercive {S : Submodule ℂ W} {T : S →ₗ[ℂ] S} {c : ℝ}
    (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ (inner ℂ (T x) x).re) (lam : ℝ) (x : S) :
    (c - lam) * ‖x‖ ^ 2 ≤ (inner ℂ (realShift T lam x) x).re := by
  have h := hcoer x
  have hs := re_inner_ofReal_smul_self lam x
  simp only [realShift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, Complex.sub_re]
  linarith

theorem injective_of_coercive {S : Submodule ℂ W} {T : S →ₗ[ℂ] S} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ (inner ℂ (T x) x).re) : Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := hcoer x
  rw [hx, inner_zero_left, Complex.zero_re] at h
  have hn : ‖x‖ ^ 2 ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have := mul_pos hc hneg
    linarith
  have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp this

/-- Resolvent bound `c ‖T⁻¹ s‖ ≤ ‖s‖` for a coercive `T`. -/
theorem mul_norm_symm_le_of_coercive {S : Submodule ℂ W} {T : S →ₗ[ℂ] S} {Ti : S ≃ₗ[ℂ] S}
    (hTi : ∀ y, Ti y = T y) {c : ℝ}
    (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ (inner ℂ (T x) x).re) (s : S) :
    c * ‖Ti.symm s‖ ≤ ‖s‖ := by
  set y := Ti.symm s
  have hTy : T y = s := by rw [← hTi, LinearEquiv.apply_symm_apply]
  have h := hcoer y
  rw [hTy] at h
  have hcs : (inner ℂ s y).re ≤ ‖s‖ * ‖y‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm s y)
  rcases eq_or_lt_of_le (norm_nonneg y) with hy | hy
  · rw [← hy, mul_zero]
    exact norm_nonneg s
  · have : c * ‖y‖ * ‖y‖ ≤ ‖s‖ * ‖y‖ := by nlinarith
    exact le_of_mul_le_mul_right this hy

/-- Resolvent identity `(T - λ)⁻¹ s - T⁻¹ s = λ (T - λ)⁻¹ T⁻¹ s`. -/
theorem shift_symm_sub_symm {M : Type*} [AddCommGroup M] [Module ℂ M] {T : M →ₗ[ℂ] M}
    {Ti Tl : M ≃ₗ[ℂ] M} {lam : ℝ} (hTi : ∀ y, Ti y = T y) (hTl : ∀ y, Tl y = realShift T lam y)
    (s : M) :
    Tl.symm s - Ti.symm s = (lam : ℂ) • Tl.symm (Ti.symm s) := by
  apply Tl.injective
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hTl]
  simp only [realShift, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [← hTi, LinearEquiv.apply_symm_apply]
  abel

variable {A : Es →ₗ[ℂ] Es} {B : Os →ₗ[ℂ] Os} {D : Es ≃ₗ[ℂ] Os} {g : Os} {H : Es →ₗ[ℂ] ℂ}
  {Bi : Os ≃ₗ[ℂ] Os}

/-- **Step 60, sign (abstract):** at a contact `H x = 1` with `A ≽ 0`
symmetric and `B` symmetric and `δ`-coercive (`δ > 0`), the resolvent slope
`H(D⁻¹ B⁻¹ B⁻¹ g)` is real and strictly positive. -/
theorem secular_resolvent_slope_pos
    (hA : A.IsSymmetric) (hA0 : ∀ x, 0 ≤ (inner ℂ (A x) x).re)
    (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ) (hBc : ∀ y, δ * ‖y‖ ^ 2 ≤ (inner ℂ (B y) y).re)
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y)
    (hT : H (secularResolventRay Bi D g) = 1) :
    (H (secularResolventRay Bi D (Bi.symm g))).im = 0 ∧
      0 < (H (secularResolventRay Bi D (Bi.symm g))).re := by
  set c0 := H (secularResolventRay Bi D (Bi.symm g)) with hc0
  set r := Bi.symm g
  set s := Bi.symm r
  -- a uniform bound for `H ∘ D⁻¹`
  set F : Os →ₗ[ℂ] ℂ := H ∘ₗ (D.symm : Os →ₗ[ℂ] Es)
  set C := ‖LinearMap.toContinuousLinearMap F‖
  have hF : ∀ y, ‖F y‖ ≤ C * ‖y‖ := fun y => by
    have := (LinearMap.toContinuousLinearMap F).le_opNorm y
    simpa using this
  have hC : 0 ≤ C := norm_nonneg (LinearMap.toContinuousLinearMap F)
  set M := C * ‖s‖ / δ
  have hM : 0 ≤ M := by positivity
  -- nonzero by the overlap identity
  have hc0ne : c0 ≠ 0 := by
    have hov := secular_overlap_identity hA hrank hBi hT
    have hx : secularResolventRay Bi D g ≠ 0 := by
      intro h0
      have : H (secularResolventRay Bi D g) = 0 := by rw [h0, map_zero]
      rw [hT] at this
      exact one_ne_zero this
    have hn : ((‖secularResolventRay Bi D g‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ‖secularResolventRay Bi D g‖ := norm_pos_iff.mpr hx
      exact_mod_cast (pow_pos this 2).ne'
    rw [← hov] at hn
    exact right_ne_zero_of_mul hn
  -- approximation by real positive numbers
  have happrox : ∀ ε : ℝ, 0 < ε →
      ∃ c' : ℂ, c'.im = 0 ∧ 0 < c'.re ∧ ‖c0 - c'‖ ≤ ε * M := by
    intro ε hε
    set lam : ℝ := -ε
    have hlam : lam < 0 := by simp [lam, hε]
    -- shifted maps are coercive
    have hBl : ∀ y, (δ - lam) * ‖y‖ ^ 2 ≤ (inner ℂ (realShift B lam y) y).re :=
      realShift_coercive hBc lam
    have hAl : ∀ x, (0 - lam) * ‖x‖ ^ 2 ≤ (inner ℂ (realShift A lam x) x).re :=
      realShift_coercive (c := 0) (fun x => by simpa using hA0 x) lam
    have hδl : 0 < δ - lam := by linarith
    have h0l : 0 < 0 - lam := by linarith
    set Bl : Os ≃ₗ[ℂ] Os := LinearEquiv.ofInjectiveEndo (realShift B lam)
      (injective_of_coercive hδl hBl)
    have hBl_apply : ∀ y, Bl y = realShift B lam y := fun _ => rfl
    -- determinants
    obtain ⟨pA, hpA, hdetA⟩ :=
      exists_det_eq_ofReal_pos_of_coercive (realShift_isSymmetric hA lam) h0l hAl
    obtain ⟨pB, hpB, hdetB⟩ :=
      exists_det_eq_ofReal_pos_of_coercive (realShift_isSymmetric hB lam) hδl hBl
    have hdet := det_eq_det_mul_one_sub_secularResolventScalar
      (hrank.shift (lam : ℂ)) hBl_apply
    rw [hdetA, hdetB] at hdet
    -- resolvent identity for the ray
    set cl := F (Bl.symm r)
    have hres : H (secularResolventRay Bl D g) - H (secularResolventRay Bi D g) =
        (lam : ℂ) * cl := by
      simp only [secularResolventRay]
      rw [← map_sub, ← map_sub, shift_symm_sub_symm hBi hBl_apply, map_smul, map_smul,
        smul_eq_mul]
      rfl
    rw [hT] at hres
    -- `1 - T(λ) = -λ c_λ = pA / pB`
    have hcl : cl = ((pA / pB / (-lam) : ℝ) : ℂ) := by
      have hpBc : (pB : ℂ) ≠ 0 := by exact_mod_cast hpB.ne'
      have hlc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne
      have h1 : 1 - H (secularResolventRay Bl D g) = (pA : ℂ) / pB := by
        rw [hdet]
        field_simp
      have h2 : (lam : ℂ) * cl = -((pA : ℂ) / pB) := by
        rw [← hres]
        linear_combination (-1 : ℂ) * h1
      have h3 : cl = -((pA : ℂ) / pB) / lam := by
        rw [← h2]
        field_simp
      rw [h3]
      push_cast
      field_simp
    refine ⟨cl, ?_, ?_, ?_⟩
    · rw [hcl, Complex.ofReal_im]
    · rw [hcl, Complex.ofReal_re]
      apply div_pos (div_pos hpA hpB)
      linarith
    · -- `c0 - c_λ = -λ F((B - λ)⁻¹ s)`
      have hdiff : c0 - cl = -((lam : ℂ) * F (Bl.symm s)) := by
        have := shift_symm_sub_symm hBi hBl_apply r
        have h4 : F (Bl.symm r) - F (Bi.symm r) = (lam : ℂ) * F (Bl.symm s) := by
          rw [← map_sub, this, map_smul, smul_eq_mul]
        rw [hc0]
        change F (Bi.symm r) - F (Bl.symm r) = _
        rw [← h4]
        ring
      rw [hdiff, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hlam]
      have hbound : ‖F (Bl.symm s)‖ ≤ C * (‖s‖ / δ) := by
        refine (hF _).trans (mul_le_mul_of_nonneg_left ?_ hC)
        have h5 := mul_norm_symm_le_of_coercive hBl_apply hBl s
        rw [le_div_iff₀ hδ]
        have : δ * ‖Bl.symm s‖ ≤ (δ - lam) * ‖Bl.symm s‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        linarith
      have : -lam = ε := by simp [lam]
      rw [this]
      calc ε * ‖F (Bl.symm s)‖ ≤ ε * (C * (‖s‖ / δ)) :=
            mul_le_mul_of_nonneg_left hbound hε.le
        _ = ε * M := by simp only [M]; ring
  obtain ⟨hre, him⟩ := re_nonneg_and_im_eq_zero_of_approx hM happrox
  refine ⟨him, lt_of_le_of_ne hre ?_⟩
  intro h0
  apply hc0ne
  exact Complex.ext h0.symm him

/-- **Step 60, sign (abstract):** under the same hypotheses the overlap
`⟪x, D⁻¹ g⟫` is real and strictly positive. -/
theorem secular_overlap_pos
    (hA : A.IsSymmetric) (hA0 : ∀ x, 0 ≤ (inner ℂ (A x) x).re)
    (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ) (hBc : ∀ y, δ * ‖y‖ ^ 2 ≤ (inner ℂ (B y) y).re)
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y)
    (hT : H (secularResolventRay Bi D g) = 1) :
    (inner ℂ (secularResolventRay Bi D g) (D.symm g)).im = 0 ∧
      0 < (inner ℂ (secularResolventRay Bi D g) (D.symm g)).re := by
  obtain ⟨him, hre⟩ := secular_resolvent_slope_pos hA hA0 hB hδ hBc hrank hBi hT
  have hov := secular_overlap_identity hA hrank hBi hT
  set c0 := H (secularResolventRay Bi D (Bi.symm g))
  set o := inner ℂ (secularResolventRay Bi D g) (D.symm g)
  have hc0 : c0 = (c0.re : ℂ) := Complex.ext rfl (by simp [him])
  have hx : secularResolventRay Bi D g ≠ 0 := by
    intro h0
    have : H (secularResolventRay Bi D g) = 0 := by rw [h0, map_zero]
    rw [hT] at this
    exact one_ne_zero this
  have hxpos : 0 < ‖secularResolventRay Bi D g‖ ^ 2 := by
    have := norm_pos_iff.mpr hx
    positivity
  have ho : o = ((‖secularResolventRay Bi D g‖ ^ 2 / c0.re : ℝ) : ℂ) := by
    have hcne : (c0.re : ℂ) ≠ 0 := by exact_mod_cast hre.ne'
    rw [hc0] at hov
    rw [Complex.ofReal_div, eq_div_iff hcne]
    exact hov
  rw [ho, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_pos hxpos hre⟩

end OverlapSign

/-! ## Canonical instance -/

section Canonical

variable {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
  (hpos : 0 < parityRayleighBottom .odd L K) (hposE : 0 ≤ parityRayleighBottom .even L K)
include hL hK hpos hposE

/-- **Step 60 (canonical), sign of the overlap at a first-crossing contact:**
if the even Rayleigh bottom is `≥ 0` (`A_L ≽ 0`), the odd bottom is `> 0`, and
`S_L(x_L) = 1` (contact), then `S_L(D⁻¹ B_L⁻¹ B_L⁻¹ g)` and
`⟪x_L, D⁻¹ g⟫` are both real and strictly positive. -/
theorem canonical_contact_overlap_pos
    (hT : explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1) :
    (explicitCanonicalSourceMoment L K
        (secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
          (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
          ((oddCompressedCanonicalEquiv L K hpos).symm (oddCubicCompressionVector K)))).im = 0 ∧
      0 < (explicitCanonicalSourceMoment L K
        (secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
          (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
          ((oddCompressedCanonicalEquiv L K hpos).symm (oddCubicCompressionVector K)))).re ∧
      (inner ℂ (canonicalResolventRay L K hK hpos)
        ((euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K))).im = 0 ∧
      0 < (inner ℂ (canonicalResolventRay L K hK hpos)
        ((euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K))).re := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK] at hT ⊢
  have hA0 : ∀ x : euclideanEvenBoundaryFlatSubspace K,
      0 ≤ (inner ℂ (evenCompressedCanonical L K x) x).re := fun x =>
    (mul_nonneg hposE (sq_nonneg _)).trans (evenCompressedCanonical_coercive L K x)
  have h1 := secular_resolvent_slope_pos (parityCompressedCanonical_isSymmetric .even L K) hA0
    (parityCompressedCanonical_isSymmetric .odd L K) hpos (oddCompressedCanonical_coercive L K)
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos) hT
  have h2 := secular_overlap_pos (parityCompressedCanonical_isSymmetric .even L K) hA0
    (parityCompressedCanonical_isSymmetric .odd L K) hpos (oddCompressedCanonical_coercive L K)
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos) hT
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

end Canonical

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_det_eq_ofReal_pos_of_coercive
#print axioms Zeta23.CCM.re_nonneg_and_im_eq_zero_of_approx
#print axioms Zeta23.CCM.secular_resolvent_slope_pos
#print axioms Zeta23.CCM.secular_overlap_pos
#print axioms Zeta23.CCM.canonical_contact_overlap_pos
