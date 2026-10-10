import Zeta23.CCM.SecularDeterminantKernel
import Zeta23.CCM.GlobalParityBottomSourceMoment
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace Zeta23.CCM

open scoped ComplexConjugate

/-!
# POST285 M74 (Steps 111, 112, 116, 117, 118): canonical secular resolvent ray

`SecularDeterminantKernel.lean` proves the rank-one secular algebra for
abstract matrices.  This module restates it for linear maps between two
(different) complex inner-product spaces and then instantiates it on the actual
canonical parity compressions:

* `A_L = evenCompressedCanonical L K` (even constrained sector),
* `B_L = oddCompressedCanonical L K` (odd constrained sector),
* `D = euclideanEvenOddBoundaryFlatLinearEquiv K` (algebraic, **not** unitary),
* `g = oddCubicCompressionVector K` (projected cubic generator),
* `H_L = cubicDefectFunctional L K`, pointwise equal to the actual
  `explicitCanonicalSourceMoment L K` (pole / archimedean / von Mangoldt).

The rank-one relation `B_L D - D A_L = g ⊗ H_L` is the existing theorem
`evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul`; the fourth-moment
normalization `⟪g, D v⟫ = M4(v)` is the existing theorem
`inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour`.  Neither is
re-proved or assumed here.

When the odd bottom is positive (`0 < parityRayleighBottom .odd L K`, so
`B_L > 0`), put `r_L = B_L⁻¹ g`, `x_L = D⁻¹ r_L`, `γ_L = ⟪g, r_L⟫`.  Proved:

* (Step 111) `A_L x_L = (1 - H_L x_L) • D⁻¹ g`,
  `det A_L = det B_L · (1 - H_L x_L)`, every even zero mode is
  `H_L(z) • x_L`, `H_L x_L = 1 ↔ ker A_L ≠ 0`, and then `ker A_L = ℂ ∙ x_L`;
* (Step 116) the **off-contact** Ward identity, for every even `v`,
  `γ_L * H_L v = M4(v) - ⟪r_L, D (A_L v)⟫` (Mathlib inner product,
  conjugate-linear in the first slot);
* (Step 118) `γ_L` is real and `γ_L > 0`, and `M4(x_L) = γ_L`;
* (Step 112) at every even contact `A_L z = 0`: `γ_L * H_L z = M4 z` and
  `Re(conj(H_L z) * M4 z) = γ_L |H_L z|² > 0` for `z ≠ 0`;
* (Step 117) `‖H_L v - M4 v / γ_L‖ ≤ K ‖r_L‖ ‖A_L v‖ / γ_L`,
  `δ ‖r_L‖ ≤ ‖g‖` for `δ = parityRayleighBottom .odd L K`, and the
  approximate-contact phase lock `‖M4 v‖ > K ‖r_L‖ ‖A_L v‖ ⇒
  Re(conj(H_L v) * M4 v) > 0`.

Firewalls:
* nothing here asserts that a contact exists or does not exist;
* `H_L x_L = 1` is *equivalent* to contact, so it is never an independent
  opposite-side input;
* `T ≤ 1` is never used to infer `A_L ≽ 0`, and no monotonicity in the spectral
  parameter is claimed;
* `A_L` (the even compressed operator) is not the scalar physical functional
  `𝓐_L` of Step 113; no arithmetic sign of `𝓐_L` is claimed;
* no F04, no RH, no new axiom.
-/

/-! ## Linear-map secular algebra between two inner-product spaces -/

section LinearSecular

variable {E O : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup O] [Module ℂ O]

/-- Rank-one intertwining `B ∘ D - D ∘ A = g ⊗ H`, pointwise. -/
def RankOneIntertwining (A : E →ₗ[ℂ] E) (B : O →ₗ[ℂ] O) (D : E ≃ₗ[ℂ] O)
    (g : O) (H : E →ₗ[ℂ] ℂ) : Prop :=
  ∀ v : E, B (D v) - D (A v) = H v • g

/-- Resolvent image `r = B⁻¹ g`. -/
def secularResolventVector (Bi : O ≃ₗ[ℂ] O) (g : O) : O :=
  Bi.symm g

/-- Resolvent-selected even ray `x = D⁻¹ B⁻¹ g`. -/
def secularResolventRay (Bi : O ≃ₗ[ℂ] O) (D : E ≃ₗ[ℂ] O) (g : O) : E :=
  D.symm (Bi.symm g)

variable {A : E →ₗ[ℂ] E} {B : O →ₗ[ℂ] O} {D : E ≃ₗ[ℂ] O} {g : O}
  {H : E →ₗ[ℂ] ℂ} {Bi : O ≃ₗ[ℂ] O}

theorem apply_secularResolventVector (hBi : ∀ y, Bi y = B y) :
    B (secularResolventVector Bi g) = g := by
  rw [secularResolventVector, ← hBi, LinearEquiv.apply_symm_apply]

theorem D_secularResolventRay :
    D (secularResolventRay Bi D g) = secularResolventVector Bi g := by
  simp [secularResolventRay, secularResolventVector]

/-- `D (A x) = (1 - H x) • g` on the resolvent ray. -/
theorem D_apply_secularResolventRay (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) :
    D (A (secularResolventRay Bi D g)) =
      (1 - H (secularResolventRay Bi D g)) • g := by
  have h := hrank (secularResolventRay Bi D g)
  rw [D_secularResolventRay, apply_secularResolventVector hBi] at h
  rw [sub_smul, one_smul, ← h]
  abel

/-- **Step 111, constructive vector:** `A x = (1 - H x) • D⁻¹ g`. -/
theorem apply_secularResolventRay (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) :
    A (secularResolventRay Bi D g) =
      (1 - H (secularResolventRay Bi D g)) • D.symm g := by
  apply D.injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact D_apply_secularResolventRay hrank hBi

/-- **Step 111, kernel rigidity:** every zero mode of `A` is `H(z) • x`. -/
theorem eq_smul_secularResolventRay_of_apply_eq_zero
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y)
    {z : E} (hz : A z = 0) :
    z = H z • secularResolventRay Bi D g := by
  have h := hrank z
  rw [hz, map_zero, sub_zero] at h
  have h1 : Bi (D z) = H z • g := by rw [hBi]; exact h
  have h2 : D z = Bi.symm (H z • g) := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  rw [map_smul] at h2
  calc z = D.symm (D z) := (D.symm_apply_apply z).symm
    _ = H z • secularResolventRay Bi D g := by
      rw [h2, map_smul]
      rfl

theorem secularResolventRay_ne_zero (hg : g ≠ 0) :
    secularResolventRay Bi D g ≠ 0 := by
  intro h0
  apply hg
  have h1 : Bi.symm g = 0 := by
    have := congrArg D h0
    simpa [secularResolventRay] using this
  simpa using congrArg Bi h1

/-- **Step 111, contact criterion:** for `g ≠ 0`, `H x = 1` iff `A` has a
nonzero zero mode. -/
theorem secularResolventScalar_eq_one_iff
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y) (hg : g ≠ 0) :
    H (secularResolventRay Bi D g) = 1 ↔ ∃ z : E, z ≠ 0 ∧ A z = 0 := by
  have hd : D.symm g ≠ 0 := by
    intro h0
    apply hg
    simpa using congrArg D h0
  constructor
  · intro hT
    refine ⟨secularResolventRay Bi D g, secularResolventRay_ne_zero hg, ?_⟩
    rw [apply_secularResolventRay hrank hBi, hT, sub_self, zero_smul]
  · rintro ⟨z, hz0, hz⟩
    have hzeq := eq_smul_secularResolventRay_of_apply_eq_zero hrank hBi hz
    have hc : H z ≠ 0 := by
      intro hc
      apply hz0
      rw [hzeq, hc, zero_smul]
    have hAz : A z = H z • ((1 - H (secularResolventRay Bi D g)) • D.symm g) := by
      conv_lhs => rw [hzeq]
      rw [map_smul, apply_secularResolventRay hrank hBi]
    rw [hz, smul_smul] at hAz
    have hmul : H z * (1 - H (secularResolventRay Bi D g)) = 0 := by
      by_contra hne
      exact hd ((smul_eq_zero.mp hAz.symm).resolve_left hne)
    have := (mul_eq_zero.mp hmul).resolve_left hc
    exact (sub_eq_zero.mp this).symm

/-- The kernel of `A` always lies in the resolvent line. -/
theorem ker_le_span_secularResolventRay
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y) :
    LinearMap.ker A ≤ ℂ ∙ secularResolventRay Bi D g := by
  intro z hz
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_span_singleton]
  exact ⟨H z, (eq_smul_secularResolventRay_of_apply_eq_zero hrank hBi hz).symm⟩

/-- **Step 111, kernel span:** at contact (`H x = 1`) the kernel is exactly the
resolvent line. -/
theorem ker_eq_span_secularResolventRay_of_scalar_eq_one
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y)
    (hT : H (secularResolventRay Bi D g) = 1) :
    LinearMap.ker A = ℂ ∙ secularResolventRay Bi D g := by
  apply le_antisymm (ker_le_span_secularResolventRay hrank hBi)
  rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
    apply_secularResolventRay hrank hBi, hT, sub_self, zero_smul]

/-- `det (1 - k ⊗ w) = 1 - k w` for linear maps. -/
theorem det_id_sub_smulRight {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (k : M →ₗ[ℂ] ℂ) (w : M) :
    LinearMap.det (LinearMap.id - k.smulRight w) = 1 - k w := by
  classical
  let b := Module.finBasis ℂ M
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b (LinearMap.id - k.smulRight w) =
      1 - Matrix.vecMulVec (b.repr w) (fun j => k (b j)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      Finsupp.single_apply, eq_comm, mul_comm]
  rw [hmat, det_one_sub_vecMulVec]
  congr 1
  simp only [dotProduct]
  conv_rhs => rw [← b.sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- **Step 111, determinant identity:** `det A = det B · (1 - H x)`. -/
theorem det_eq_det_mul_one_sub_secularResolventScalar [FiniteDimensional ℂ O]
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y) :
    LinearMap.det A = LinearMap.det B * (1 - H (secularResolventRay Bi D g)) := by
  have hconj : (D : E →ₗ[ℂ] O) ∘ₗ A ∘ₗ (D.symm : O →ₗ[ℂ] E) =
      B ∘ₗ (LinearMap.id - (H ∘ₗ (D.symm : O →ₗ[ℂ] E)).smulRight
        (secularResolventVector Bi g)) := by
    apply LinearMap.ext
    intro y
    have h := hrank (D.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
      apply_secularResolventVector hBi]
    rw [← h]
    abel
  rw [← LinearMap.det_conj A D, hconj, LinearMap.det_comp, det_id_sub_smulRight]
  rfl

theorem det_ne_zero_of_equiv [FiniteDimensional ℂ O] (hBi : ∀ y, Bi y = B y) :
    LinearMap.det B ≠ 0 := by
  have hB : B = (Bi : O →ₗ[ℂ] O) := by
    apply LinearMap.ext
    intro y
    exact (hBi y).symm
  rw [hB]
  exact (LinearEquiv.isUnit_det' Bi).ne_zero

/-- **Step 111, determinant ratio:** `det A / det B = 1 - H x`. -/
theorem det_div_det_eq_one_sub_secularResolventScalar [FiniteDimensional ℂ O]
    (hrank : RankOneIntertwining A B D g H) (hBi : ∀ y, Bi y = B y) :
    LinearMap.det A / LinearMap.det B = 1 - H (secularResolventRay Bi D g) := by
  rw [det_eq_det_mul_one_sub_secularResolventScalar hrank hBi,
    mul_div_cancel_left₀ _ (det_ne_zero_of_equiv hBi)]

end LinearSecular

/-! ## Inner-product layer (odd carrier a submodule of an inner-product space) -/

section Symmetric

variable {E V : Type*} [AddCommGroup E] [Module ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] {Os : Submodule ℂ V}

/-- Resolvent scalar `γ = ⟪g, B⁻¹ g⟫`. -/
def secularResolventGamma (Bi : Os ≃ₗ[ℂ] Os) (g : Os) : ℂ :=
  inner ℂ g (Bi.symm g)

variable {A : E →ₗ[ℂ] E} {B : Os →ₗ[ℂ] Os} {D : E ≃ₗ[ℂ] Os} {g : Os}
  {H : E →ₗ[ℂ] ℂ} {Bi : Os ≃ₗ[ℂ] Os}

variable (hsym : ∀ y w : Os, inner ℂ (B y) w = inner ℂ y (B w))
include hsym

/-- `⟪r, g⟫ = γ`: the two orderings of the resolvent pairing agree. -/
theorem inner_secularResolventVector_left (hBi : ∀ y, Bi y = B y) :
    inner ℂ (secularResolventVector Bi g) g = secularResolventGamma Bi g := by
  have hBr := apply_secularResolventVector (g := g) hBi
  calc inner ℂ (secularResolventVector Bi g) g
      = inner ℂ (secularResolventVector Bi g) (B (secularResolventVector Bi g)) := by
        rw [hBr]
    _ = inner ℂ (B (secularResolventVector Bi g)) (secularResolventVector Bi g) :=
        (hsym _ _).symm
    _ = inner ℂ g (secularResolventVector Bi g) := by rw [hBr]
    _ = secularResolventGamma Bi g := rfl

/-- `γ` is real. -/
theorem conj_secularResolventGamma (hBi : ∀ y, Bi y = B y) :
    conj (secularResolventGamma Bi g) = secularResolventGamma Bi g := by
  have h1 := inner_secularResolventVector_left hsym hBi (g := g)
  calc conj (secularResolventGamma Bi g)
      = conj (inner ℂ (secularResolventVector Bi g) g) := by rw [h1]
    _ = inner ℂ g (secularResolventVector Bi g) := inner_conj_symm _ _
    _ = secularResolventGamma Bi g := rfl

theorem ofReal_re_secularResolventGamma (hBi : ∀ y, Bi y = B y) :
    ((secularResolventGamma Bi g).re : ℂ) = secularResolventGamma Bi g :=
  Complex.conj_eq_iff_re.mp (conj_secularResolventGamma hsym hBi)

/-- **Step 116, off-contact Ward identity:** for every `v`,
`γ * H v = ⟪g, D v⟫ - ⟪B⁻¹ g, D (A v)⟫`.  No contact hypothesis. -/
theorem secular_ward_identity (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) (v : E) :
    secularResolventGamma Bi g * H v =
      inner ℂ g (D v) - inner ℂ (secularResolventVector Bi g) (D (A v)) := by
  have h := congrArg (fun y => inner ℂ (secularResolventVector Bi g) y) (hrank v)
  simp only [inner_sub_right, inner_smul_right] at h
  have hB : inner ℂ (secularResolventVector Bi g) (B (D v)) = inner ℂ g (D v) := by
    rw [← hsym, apply_secularResolventVector hBi]
  rw [hB, inner_secularResolventVector_left hsym hBi] at h
  linear_combination -h

omit hsym in
/-- **Step 118, ray gauge:** `⟪g, D x⟫ = γ`. -/
theorem inner_D_secularResolventRay :
    inner ℂ g (D (secularResolventRay Bi D g)) = secularResolventGamma Bi g := by
  rw [D_secularResolventRay]
  rfl

/-- **Step 112, contact pairing:** at a zero mode `A z = 0`,
`γ * H z = ⟪g, D z⟫`. -/
theorem secular_contact_pairing (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) {z : E} (hz : A z = 0) :
    secularResolventGamma Bi g * H z = inner ℂ g (D z) := by
  rw [secular_ward_identity hsym hrank hBi z, hz, map_zero, inner_zero_right, sub_zero]

/-- **Step 112, contact phase:** `Re(conj(H z) ⟪g, D z⟫) = Re γ · |H z|²`. -/
theorem re_conj_mul_inner_contact (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) {z : E} (hz : A z = 0) :
    (conj (H z) * inner ℂ g (D z)).re =
      (secularResolventGamma Bi g).re * Complex.normSq (H z) := by
  rw [← secular_contact_pairing hsym hrank hBi hz,
    ← ofReal_re_secularResolventGamma hsym hBi]
  have : conj (H z) * (((secularResolventGamma Bi g).re : ℂ) * H z) =
      (((secularResolventGamma Bi g).re * Complex.normSq (H z) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [this, Complex.ofReal_re, Complex.ofReal_re]

omit hsym in
/-- Positivity of the resolvent scalar from a coercive odd block. -/
theorem re_secularResolventGamma_ge (hBi : ∀ y, Bi y = B y) {δ : ℝ}
    (hcoer : ∀ y : Os, δ * ‖y‖ ^ 2 ≤ (inner ℂ (B y) y).re) :
    δ * ‖secularResolventVector Bi g‖ ^ 2 ≤ (secularResolventGamma Bi g).re := by
  have h := hcoer (secularResolventVector Bi g)
  rw [apply_secularResolventVector hBi] at h
  exact h

omit hsym in
/-- **Step 117, resolvent norm:** `δ ‖B⁻¹ g‖ ≤ ‖g‖`. -/
theorem mul_norm_secularResolventVector_le (hBi : ∀ y, Bi y = B y) {δ : ℝ}
    (hcoer : ∀ y : Os, δ * ‖y‖ ^ 2 ≤ (inner ℂ (B y) y).re) :
    δ * ‖secularResolventVector Bi g‖ ≤ ‖g‖ := by
  set r := secularResolventVector Bi g
  have h1 := re_secularResolventGamma_ge hBi hcoer (g := g)
  have h2 : (secularResolventGamma Bi g).re ≤ ‖g‖ * ‖r‖ := by
    calc (secularResolventGamma Bi g).re ≤ ‖secularResolventGamma Bi g‖ :=
          Complex.re_le_norm _
      _ ≤ ‖g‖ * ‖r‖ := norm_inner_le_norm g r
  by_cases hr : ‖r‖ = 0
  · rw [hr, mul_zero]; exact norm_nonneg g
  · have hrpos : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    have : δ * ‖r‖ * ‖r‖ ≤ ‖g‖ * ‖r‖ := by nlinarith
    exact le_of_mul_le_mul_right this hrpos

omit hsym in
/-- **Step 118, positivity:** a positive-definite odd block and `g ≠ 0` give
`Re γ > 0`. -/
theorem re_secularResolventGamma_pos (hBi : ∀ y, Bi y = B y) (hg : g ≠ 0)
    (hpos : ∀ y : Os, y ≠ 0 → 0 < (inner ℂ (B y) y).re) :
    0 < (secularResolventGamma Bi g).re := by
  have hr : secularResolventVector Bi g ≠ 0 := by
    intro h0
    apply hg
    rw [← apply_secularResolventVector (g := g) hBi, h0, map_zero]
  have h := hpos _ hr
  rw [apply_secularResolventVector hBi] at h
  exact h

/-- **Step 117, approximate-contact error:**
`‖γ H v - ⟪g, D v⟫‖ ≤ ‖B⁻¹ g‖ ‖D (A v)‖`. -/
theorem norm_gamma_mul_sub_inner_le (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) (v : E) :
    ‖secularResolventGamma Bi g * H v - inner ℂ g (D v)‖ ≤
      ‖secularResolventVector Bi g‖ * ‖D (A v)‖ := by
  rw [secular_ward_identity hsym hrank hBi v, sub_sub_cancel_left, norm_neg]
  exact norm_inner_le_norm _ _

/-- **Step 117, approximate phase lock:** if
`‖B⁻¹ g‖ ‖D (A v)‖ < ‖⟪g, D v⟫‖` and `Re γ > 0`, then
`Re(conj(H v) ⟪g, D v⟫) > 0`.  This certifies a sign near contact; it does not
certify existence or nonexistence of a contact. -/
theorem re_conj_mul_inner_pos_of_approx (hrank : RankOneIntertwining A B D g H)
    (hBi : ∀ y, Bi y = B y) (hγ : 0 < (secularResolventGamma Bi g).re) (v : E)
    (hsmall : ‖secularResolventVector Bi g‖ * ‖D (A v)‖ < ‖inner ℂ g (D v)‖) :
    0 < (conj (H v) * inner ℂ g (D v)).re := by
  set γ := secularResolventGamma Bi g
  set m := inner ℂ g (D v)
  set e := m - γ * H v
  have hγreal : ((γ.re : ℝ) : ℂ) = γ := ofReal_re_secularResolventGamma hsym hBi
  have he : ‖e‖ < ‖m‖ := by
    have := norm_gamma_mul_sub_inner_le hsym hrank hBi v
    rw [← norm_neg, neg_sub] at this
    exact lt_of_le_of_lt this hsmall
  have hkey : γ.re * (conj (H v) * m).re = (conj (m - e) * m).re := by
    have hme : m - e = γ * H v := by simp [e]
    rw [hme, map_mul, ← hγreal, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul,
      Complex.ofReal_re]
  have hexp : (conj (m - e) * m).re = ‖m‖ ^ 2 - (conj e * m).re := by
    rw [map_sub, sub_mul, Complex.sub_re, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hcross : (conj e * m).re ≤ ‖e‖ * ‖m‖ := by
    calc (conj e * m).re ≤ ‖conj e * m‖ := Complex.re_le_norm _
      _ = ‖e‖ * ‖m‖ := by rw [norm_mul, Complex.norm_conj]
  have hm : 0 < ‖m‖ := lt_of_le_of_lt (norm_nonneg e) he
  have hprod : 0 < γ.re * (conj (H v) * m).re := by
    rw [hkey, hexp]
    nlinarith [norm_nonneg e]
  exact pos_of_mul_pos_right hprod hγ.le

end Symmetric

/-! ## Canonical instantiation -/

section Canonical

/-- `D v` for the algebraic D-equivalence is the centered-index image. -/
theorem euclideanEvenOddBoundaryFlatLinearEquiv_apply (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    euclideanEvenOddBoundaryFlatLinearEquiv K hK v =
      euclideanEvenToOddIndexLinearMap K v := rfl

/-- **Canonical rank-one intertwining** `B_L D - D A_L = g ⊗ H_L`, from the
existing parity-defect factorization. -/
theorem canonical_rankOneIntertwining {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K) :
    RankOneIntertwining (evenCompressedCanonical L K) (oddCompressedCanonical L K)
      (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega))
      (oddCubicCompressionVector K) (cubicDefectFunctional L K) := by
  intro v
  exact evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul hL K hK v

/-- The odd compressed canonical operator is symmetric. -/
theorem oddCompressedCanonical_inner_symm (L : ℝ) (K : ℕ)
    (y w : euclideanOddBoundaryFlatSubspace K) :
    inner ℂ (oddCompressedCanonical L K y) w = inner ℂ y (oddCompressedCanonical L K w) :=
  parityCompressedCanonical_isSymmetric .odd L K y w

/-- Odd coercivity at the odd Rayleigh bottom. -/
theorem oddCompressedCanonical_coercive (L : ℝ) (K : ℕ)
    (y : euclideanOddBoundaryFlatSubspace K) :
    parityRayleighBottom .odd L K * ‖y‖ ^ 2 ≤
      (inner ℂ (oddCompressedCanonical L K y) y).re :=
  parityRayleighBottom_mul_norm_sq_le .odd L K y

theorem oddCompressedCanonical_injective {L : ℝ} {K : ℕ}
    (hpos : 0 < parityRayleighBottom .odd L K) :
    Function.Injective (oddCompressedCanonical L K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have h := oddCompressedCanonical_coercive L K y
  rw [hy, inner_zero_left, Complex.zero_re] at h
  have hn : ‖y‖ ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hpos hc
    linarith
  have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp this

/-- `B_L` as a linear equivalence when the odd bottom is positive. -/
def oddCompressedCanonicalEquiv (L : ℝ) (K : ℕ)
    (hpos : 0 < parityRayleighBottom .odd L K) :
    euclideanOddBoundaryFlatSubspace K ≃ₗ[ℂ] euclideanOddBoundaryFlatSubspace K :=
  LinearEquiv.ofInjectiveEndo (oddCompressedCanonical L K)
    (oddCompressedCanonical_injective hpos)

theorem oddCompressedCanonicalEquiv_apply {L : ℝ} {K : ℕ}
    (hpos : 0 < parityRayleighBottom .odd L K) (y : euclideanOddBoundaryFlatSubspace K) :
    oddCompressedCanonicalEquiv L K hpos y = oddCompressedCanonical L K y := rfl

/-- Canonical resolvent vector `r_L = B_L⁻¹ g`. -/
def canonicalResolventVector (L : ℝ) (K : ℕ)
    (hpos : 0 < parityRayleighBottom .odd L K) :
    euclideanOddBoundaryFlatSubspace K :=
  secularResolventVector (oddCompressedCanonicalEquiv L K hpos) (oddCubicCompressionVector K)

/-- Canonical resolvent-selected even ray `x_L = D⁻¹ B_L⁻¹ g`. -/
def canonicalResolventRay (L : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hpos : 0 < parityRayleighBottom .odd L K) :
    euclideanEvenBoundaryFlatSubspace K :=
  secularResolventRay (oddCompressedCanonicalEquiv L K hpos)
    (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)) (oddCubicCompressionVector K)

/-- Canonical resolvent scalar `γ_L = Re ⟪g, B_L⁻¹ g⟫` (the pairing is real). -/
def canonicalResolventGamma (L : ℝ) (K : ℕ)
    (hpos : 0 < parityRayleighBottom .odd L K) : ℝ :=
  (secularResolventGamma (oddCompressedCanonicalEquiv L K hpos)
    (oddCubicCompressionVector K)).re

/-- `‖D w‖ ≤ K ‖w‖` for the centered-index map. -/
theorem norm_euclideanIndexLinearMap_le (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖euclideanIndexLinearMap K x‖ ≤ K * ‖x‖ := by
  have hcoord : ∀ i, (euclideanIndexLinearMap K x) i = (centeredIndex K i : ℂ) * x i := by
    intro i
    have h := congrFun (euclideanIndexLinearMap_coordinates K x) i
    simpa [indexMatrix, Matrix.mulVec_diagonal] using h
  have hidx : ∀ i : Fin (2 * K + 1), ‖((centeredIndex K i : ℤ) : ℂ)‖ ≤ K := by
    intro i
    rw [Complex.norm_intCast, abs_le]
    have hi : i.1 ≤ 2 * K := by have := i.isLt; omega
    have hi' : ((i.1 : ℕ) : ℝ) ≤ 2 * K := by exact_mod_cast hi
    have h0 : (0 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [centeredIndex]
    push_cast
    constructor <;> linarith
  have hsq : ‖euclideanIndexLinearMap K x‖ ^ 2 ≤ ((K : ℝ) * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hcoord i, norm_mul, mul_pow]
    gcongr
    exact hidx i
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

variable {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 2 ≤ K)
  (hpos : 0 < parityRayleighBottom .odd L K)
include hL hK

/-- Fourth centered moment of an even constrained vector. -/
abbrev evenMomentFour (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)

omit hL in
theorem canonical_inner_g_D_eq_momentFour (v : euclideanEvenBoundaryFlatSubspace K) :
    inner ℂ (oddCubicCompressionVector K)
        (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega) v) =
      evenMomentFour K v :=
  inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour K v

omit hL hK in
include hpos in
theorem canonicalResolventGamma_ofReal :
    ((canonicalResolventGamma L K hpos : ℝ) : ℂ) =
      inner ℂ (oddCubicCompressionVector K) (canonicalResolventVector L K hpos) :=
  ofReal_re_secularResolventGamma (Os := euclideanOddBoundaryFlatSubspace K) (B := oddCompressedCanonical L K)
    (Bi := oddCompressedCanonicalEquiv L K hpos)
    (oddCompressedCanonical_inner_symm L K)
    (oddCompressedCanonicalEquiv_apply hpos)

omit hL in
include hpos in
/-- **Step 118:** `γ_L > 0`. -/
theorem canonicalResolventGamma_pos : 0 < canonicalResolventGamma L K hpos := by
  apply re_secularResolventGamma_pos (Os := euclideanOddBoundaryFlatSubspace K) (B := oddCompressedCanonical L K)
    (Bi := oddCompressedCanonicalEquiv L K hpos)
     (oddCompressedCanonicalEquiv_apply hpos)
    (oddCubicCompressionVector_ne_zero K hK)
  intro y hy
  have h := oddCompressedCanonical_coercive L K y
  have hy2 : 0 < ‖y‖ ^ 2 := by positivity
  nlinarith

include hpos in
/-- **Step 111 (canonical), constructive vector:**
`A_L x_L = (1 - S_L(x_L)) • D⁻¹ g`, with `S_L` the actual canonical source moment. -/
theorem canonical_apply_resolventRay :
    evenCompressedCanonical L K (canonicalResolventRay L K hK hpos) =
      (1 - explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos)) •
        (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
          (oddCubicCompressionVector K) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact apply_secularResolventRay (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos)

include hpos in
/-- **Step 111 (canonical), determinant:** `det A_L = det B_L · (1 - S_L(x_L))`. -/
theorem canonical_det_eq :
    LinearMap.det (evenCompressedCanonical L K) =
      LinearMap.det (oddCompressedCanonical L K) *
        (1 - explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos)) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact det_eq_det_mul_one_sub_secularResolventScalar
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos)

include hpos in
/-- **Step 111 (canonical), determinant ratio:**
`det A_L / det B_L = 1 - S_L(x_L)`. -/
theorem canonical_det_div_eq :
    LinearMap.det (evenCompressedCanonical L K) /
        LinearMap.det (oddCompressedCanonical L K) =
      1 - explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact det_div_det_eq_one_sub_secularResolventScalar
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos)

include hpos in
/-- **Step 111/118 (canonical), contact criterion:** `A_L x_L = 0` iff
`S_L(x_L) = 1`; and `S_L(x_L) = 1` iff `A_L` has a nonzero zero mode.  The
condition `S_L(x_L) = 1` is contact itself, never an independent input. -/
theorem canonical_resolventRay_contact_iff :
    (evenCompressedCanonical L K (canonicalResolventRay L K hK hpos) = 0 ↔
        explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1) ∧
      (explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1 ↔
        ∃ z : euclideanEvenBoundaryFlatSubspace K, z ≠ 0 ∧
          evenCompressedCanonical L K z = 0) := by
  have hrank := canonical_rankOneIntertwining hL K hK
  have hg := oddCubicCompressionVector_ne_zero K hK
  have hd : (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)).symm
      (oddCubicCompressionVector K) ≠ 0 := by
    intro h0
    apply hg
    simpa using congrArg (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)) h0
  refine ⟨?_, ?_⟩
  · rw [canonical_apply_resolventRay hL hK hpos, smul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact h.symm
      · exact absurd h hd
    · intro h
      exact Or.inl h.symm
  · rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
    exact secularResolventScalar_eq_one_iff hrank (oddCompressedCanonicalEquiv_apply hpos) hg

include hpos in
/-- **Step 111 (canonical), kernel rigidity:** every even zero mode is
`S_L(z) • x_L`. -/
theorem canonical_eq_smul_resolventRay_of_contact
    {z : euclideanEvenBoundaryFlatSubspace K} (hz : evenCompressedCanonical L K z = 0) :
    z = explicitCanonicalSourceMoment L K z • canonicalResolventRay L K hK hpos := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK]
  exact eq_smul_secularResolventRay_of_apply_eq_zero
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos) hz

include hpos in
/-- **Step 111 (canonical), kernel span:** at contact the kernel of `A_L` is
exactly `ℂ ∙ x_L`. -/
theorem canonical_ker_eq_span_of_contact
    (hT : explicitCanonicalSourceMoment L K (canonicalResolventRay L K hK hpos) = 1) :
    LinearMap.ker (evenCompressedCanonical L K) = ℂ ∙ canonicalResolventRay L K hK hpos := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK] at hT
  exact ker_eq_span_secularResolventRay_of_scalar_eq_one
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos) hT

include hpos in
/-- **Step 116 (canonical), off-contact Ward identity:** for every even
constrained `v` (no contact hypothesis),
`γ_L S_L(v) = M4(v) - ⟪B_L⁻¹ g, D (A_L v)⟫`. -/
theorem canonical_ward_identity (v : euclideanEvenBoundaryFlatSubspace K) :
    (canonicalResolventGamma L K hpos : ℂ) * explicitCanonicalSourceMoment L K v =
      evenMomentFour K v -
        inner ℂ (canonicalResolventVector L K hpos)
          (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)
            (evenCompressedCanonical L K v)) := by
  rw [← cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK,
    ← canonical_inner_g_D_eq_momentFour hK v, canonicalResolventGamma_ofReal hpos]
  exact secular_ward_identity (Os := euclideanOddBoundaryFlatSubspace K) (B := oddCompressedCanonical L K)
    (Bi := oddCompressedCanonicalEquiv L K hpos)
    (oddCompressedCanonical_inner_symm L K)
    (canonical_rankOneIntertwining hL K hK) (oddCompressedCanonicalEquiv_apply hpos) v

omit hL in
include hpos in
/-- **Step 118 (canonical), fourth-moment gauge of the ray:** `M4(x_L) = γ_L`. -/
theorem canonical_momentFour_resolventRay :
    evenMomentFour K (canonicalResolventRay L K hK hpos) =
      (canonicalResolventGamma L K hpos : ℂ) := by
  rw [← canonical_inner_g_D_eq_momentFour hK, canonicalResolventGamma_ofReal hpos]
  exact inner_D_secularResolventRay

include hpos in
/-- **Step 112 (canonical), contact pairing:** at every even zero mode,
`γ_L S_L(z) = M4(z)`. -/
theorem canonical_contact_pairing {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) :
    (canonicalResolventGamma L K hpos : ℂ) * explicitCanonicalSourceMoment L K z =
      evenMomentFour K z := by
  rw [canonical_ward_identity hL hK hpos z, hz, map_zero, inner_zero_right, sub_zero]

include hpos in
/-- **Step 112 (canonical), contact phase lock:** at a nonzero even zero mode,
`Re(conj(S_L z) M4 z) = γ_L |S_L z|² > 0`, and
`Re(conj(M4 z) S_L z) = |M4 z|² / γ_L`. -/
theorem canonical_contact_phase {z : euclideanEvenBoundaryFlatSubspace K}
    (hz : evenCompressedCanonical L K z = 0) (hz0 : z ≠ 0) :
    (conj (explicitCanonicalSourceMoment L K z) * evenMomentFour K z).re =
        canonicalResolventGamma L K hpos * Complex.normSq (explicitCanonicalSourceMoment L K z) ∧
      0 < (conj (explicitCanonicalSourceMoment L K z) * evenMomentFour K z).re ∧
      (conj (evenMomentFour K z) * explicitCanonicalSourceMoment L K z).re =
        Complex.normSq (evenMomentFour K z) / canonicalResolventGamma L K hpos := by
  set S := explicitCanonicalSourceMoment L K z
  set γ := canonicalResolventGamma L K hpos
  have hγ : 0 < γ := canonicalResolventGamma_pos hK hpos
  have hpair : (γ : ℂ) * S = evenMomentFour K z := canonical_contact_pairing hL hK hpos hz
  have hS : S ≠ 0 := by
    intro h0
    apply hz0
    rw [canonical_eq_smul_resolventRay_of_contact hL hK hpos hz]
    change S • _ = 0
    rw [h0, zero_smul]
  have h1 : (conj S * evenMomentFour K z).re = γ * Complex.normSq S := by
    rw [← hpair]
    have : conj S * ((γ : ℂ) * S) = ((γ * Complex.normSq S : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
      ring
    rw [this, Complex.ofReal_re]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    exact mul_pos hγ (Complex.normSq_pos.mpr hS)
  · rw [← hpair]
    have : conj ((γ : ℂ) * S) * S = ((γ * Complex.normSq S : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
      ring
    rw [this, Complex.ofReal_re, Complex.normSq_mul, Complex.normSq_ofReal]
    field_simp

omit hL in
theorem norm_evenOddEquiv_le (v : euclideanEvenBoundaryFlatSubspace K) :
    ‖euclideanEvenOddBoundaryFlatLinearEquiv K (by omega) v‖ ≤ K * ‖v‖ :=
  norm_euclideanIndexLinearMap_le K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))

omit hL hK in
include hpos in
/-- **Step 117 (canonical), resolvent norm:** `δ_L ‖B_L⁻¹ g‖ ≤ ‖g‖` for
`δ_L = parityRayleighBottom .odd L K`. -/
theorem canonical_resolventVector_norm_le :
    parityRayleighBottom .odd L K * ‖canonicalResolventVector L K hpos‖ ≤
      ‖oddCubicCompressionVector K‖ :=
  mul_norm_secularResolventVector_le (Os := euclideanOddBoundaryFlatSubspace K) (B := oddCompressedCanonical L K)
    (Bi := oddCompressedCanonicalEquiv L K hpos)
    
    (oddCompressedCanonicalEquiv_apply hpos) (oddCompressedCanonical_coercive L K)

include hpos in
/-- **Step 117 (canonical), approximate-contact error:** for every even `v`,
`‖γ_L S_L(v) - M4(v)‖ ≤ K ‖B_L⁻¹ g‖ ‖A_L v‖`. -/
theorem canonical_approx_contact_error (v : euclideanEvenBoundaryFlatSubspace K) :
    ‖(canonicalResolventGamma L K hpos : ℂ) * explicitCanonicalSourceMoment L K v -
        evenMomentFour K v‖ ≤
      K * ‖canonicalResolventVector L K hpos‖ * ‖evenCompressedCanonical L K v‖ := by
  rw [canonical_ward_identity hL hK hpos v, sub_sub_cancel_left, norm_neg]
  calc _ ≤ ‖canonicalResolventVector L K hpos‖ *
        ‖euclideanEvenOddBoundaryFlatLinearEquiv K (by omega) (evenCompressedCanonical L K v)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖canonicalResolventVector L K hpos‖ * (K * ‖evenCompressedCanonical L K v‖) := by
        gcongr
        exact norm_evenOddEquiv_le hK _
    _ = _ := by ring

include hpos in
/-- **Step 117 (canonical), quotient form:**
`‖S_L(v) - M4(v)/γ_L‖ ≤ K ‖B_L⁻¹ g‖ ‖A_L v‖ / γ_L`. -/
theorem canonical_approx_contact_error_div (v : euclideanEvenBoundaryFlatSubspace K) :
    ‖explicitCanonicalSourceMoment L K v -
        evenMomentFour K v / (canonicalResolventGamma L K hpos : ℂ)‖ ≤
      K * ‖canonicalResolventVector L K hpos‖ * ‖evenCompressedCanonical L K v‖ /
        canonicalResolventGamma L K hpos := by
  have hγ := canonicalResolventGamma_pos hK hpos
  have hγc : (canonicalResolventGamma L K hpos : ℂ) ≠ 0 := by
    exact_mod_cast hγ.ne'
  have heq : explicitCanonicalSourceMoment L K v -
      evenMomentFour K v / (canonicalResolventGamma L K hpos : ℂ) =
      ((canonicalResolventGamma L K hpos : ℂ) * explicitCanonicalSourceMoment L K v -
        evenMomentFour K v) / (canonicalResolventGamma L K hpos : ℂ) := by
    field_simp
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
  exact div_le_div_of_nonneg_right (canonical_approx_contact_error hL hK hpos v) hγ.le

include hpos in
/-- **Step 117 (canonical), approximate phase lock:** whenever
`K ‖B_L⁻¹ g‖ ‖A_L v‖ < ‖M4(v)‖`, `Re(conj(S_L v) M4 v) > 0`.  A sign certificate
near contact only. -/
theorem canonical_re_conj_mul_momentFour_pos_of_approx
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hsmall : K * ‖canonicalResolventVector L K hpos‖ * ‖evenCompressedCanonical L K v‖ <
      ‖evenMomentFour K v‖) :
    0 < (conj (explicitCanonicalSourceMoment L K v) * evenMomentFour K v).re := by
  have hD : ‖euclideanEvenOddBoundaryFlatLinearEquiv K (by omega)
      (evenCompressedCanonical L K v)‖ ≤ K * ‖evenCompressedCanonical L K v‖ :=
    norm_evenOddEquiv_le hK _
  have hsmall' : ‖canonicalResolventVector L K hpos‖ *
      ‖euclideanEvenOddBoundaryFlatLinearEquiv K (by omega) (evenCompressedCanonical L K v)‖ <
      ‖inner ℂ (oddCubicCompressionVector K)
        (euclideanEvenOddBoundaryFlatLinearEquiv K (by omega) v)‖ := by
    rw [canonical_inner_g_D_eq_momentFour hK v]
    calc _ ≤ ‖canonicalResolventVector L K hpos‖ * (K * ‖evenCompressedCanonical L K v‖) :=
          mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ = K * ‖canonicalResolventVector L K hpos‖ * ‖evenCompressedCanonical L K v‖ := by ring
      _ < _ := hsmall
  have h := re_conj_mul_inner_pos_of_approx (Os := euclideanOddBoundaryFlatSubspace K)
    (B := oddCompressedCanonical L K) (Bi := oddCompressedCanonicalEquiv L K hpos)
    (oddCompressedCanonical_inner_symm L K) (canonical_rankOneIntertwining hL K hK)
    (oddCompressedCanonicalEquiv_apply hpos) (canonicalResolventGamma_pos hK hpos) v hsmall'
  rw [canonical_inner_g_D_eq_momentFour hK v,
    cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK] at h
  exact h

end Canonical

end Zeta23.CCM

#print axioms Zeta23.CCM.apply_secularResolventRay
#print axioms Zeta23.CCM.secularResolventScalar_eq_one_iff
#print axioms Zeta23.CCM.ker_eq_span_secularResolventRay_of_scalar_eq_one
#print axioms Zeta23.CCM.det_eq_det_mul_one_sub_secularResolventScalar
#print axioms Zeta23.CCM.secular_ward_identity
#print axioms Zeta23.CCM.re_conj_mul_inner_pos_of_approx
#print axioms Zeta23.CCM.canonical_rankOneIntertwining
#print axioms Zeta23.CCM.canonicalResolventGamma_pos
#print axioms Zeta23.CCM.canonical_apply_resolventRay
#print axioms Zeta23.CCM.canonical_det_eq
#print axioms Zeta23.CCM.canonical_det_div_eq
#print axioms Zeta23.CCM.canonical_resolventRay_contact_iff
#print axioms Zeta23.CCM.canonical_ker_eq_span_of_contact
#print axioms Zeta23.CCM.canonical_ward_identity
#print axioms Zeta23.CCM.canonical_momentFour_resolventRay
#print axioms Zeta23.CCM.canonical_contact_phase
#print axioms Zeta23.CCM.canonical_resolventVector_norm_le
#print axioms Zeta23.CCM.canonical_approx_contact_error_div
#print axioms Zeta23.CCM.canonical_re_conj_mul_momentFour_pos_of_approx
