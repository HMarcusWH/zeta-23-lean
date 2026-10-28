import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4
open scoped BigOperators

/-- Complex continuation of a finite signed real spectral response. -/
def complexSignedSpectralResponse {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ β, (residue β : ℂ) / ((eigenvalue β : ℂ) - z)

/-- The signed Pick kernel, with a distinct atom for each grouped eigenvalue. -/
def signedPickKernel {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (z w : ℂ) : ℂ :=
  ∑ β, (residue β : ℂ) /
    (((eigenvalue β : ℂ) - z) * ((eigenvalue β : ℂ) - star w))

theorem real_sub_upper_ne_zero (β : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (β : ℂ) - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
  linarith

theorem upper_sub_conj_ne_zero {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    z - star w ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hi
  linarith

/-- Exact finite signed Pick identity on the upper half plane. -/
theorem finite_signed_pick_identity {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    (complexSignedSpectralResponse eigenvalue residue z -
      star (complexSignedSpectralResponse eigenvalue residue w)) / (z - star w) =
      signedPickKernel eigenvalue residue z w := by
  classical
  simp only [complexSignedSpectralResponse, signedPickKernel, star_sum,
    star_div₀, star_sub, Complex.star_def, Complex.conj_ofReal, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro β _
  have hβz := real_sub_upper_ne_zero (eigenvalue β) hz
  have hβw : (eigenvalue β : ℂ) - star w ≠ 0 := by
    have h := real_sub_upper_ne_zero (eigenvalue β) hw
    simpa using star_ne_zero.mpr h
  change (((residue β : ℂ) / ((eigenvalue β : ℂ) - z) -
    (residue β : ℂ) / ((eigenvalue β : ℂ) - star w)) / (z - star w)) =
      (residue β : ℂ) / (((eigenvalue β : ℂ) - z) * ((eigenvalue β : ℂ) - star w))
  field_simp [hβz, hβw, upper_sub_conj_ne_zero hz hw]
  have hd : -star w + z ≠ 0 := by
    simpa only [sub_eq_add_neg, add_comm] using upper_sub_conj_ne_zero hz hw
  have hc := mul_inv_cancel₀ hd
  linear_combination (residue β : ℂ) * hc

/-- Cauchy evaluation of a finite coefficient vector. -/
def signedCauchyEvaluation {ι κ : Type*} [Fintype κ]
    (eigenvalue : ι → ℝ) (points : κ → ℂ) (a : κ → ℂ) (β : ι) : ℂ :=
  ∑ j, a j / ((eigenvalue β : ℂ) - points j)

/-- The kernel's finite quadratic form is a signed Gram form. Negative atoms
are retained; positivity and a one-negative-square bound are not asserted. -/
theorem finite_signed_pick_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eigenvalue residue : ι → ℝ) (points : κ → ℂ) (a : κ → ℂ) :
    (∑ j, ∑ k, a j * signedPickKernel eigenvalue residue (points j) (points k) * star (a k)) =
      ∑ β, (residue β : ℂ) *
        (Complex.normSq (signedCauchyEvaluation eigenvalue points a β) : ℂ) := by
  classical
  simp only [signedPickKernel, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    intro j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  rw [← Complex.mul_conj]
  simp only [signedCauchyEvaluation, map_sum, map_div₀, map_sub, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.star_def, div_eq_mul_inv, mul_inv_rev]
  ring

theorem finite_signed_pick_gram_re {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eigenvalue residue : ι → ℝ) (points : κ → ℂ) (a : κ → ℂ) :
    (∑ j, ∑ k, a j * signedPickKernel eigenvalue residue (points j) (points k) * star (a k)).re =
      ∑ β, residue β * Complex.normSq (signedCauchyEvaluation eigenvalue points a β) := by
  rw [finite_signed_pick_gram]
  simp

/-- The finite Cauchy map is a linear map, including its possible kernel. -/
def signedCauchyLinearMap {ι κ : Type*} [Fintype κ]
    (eigenvalue : ι → ℝ) (points : κ → ℂ) : (κ → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun a := signedCauchyEvaluation eigenvalue points a
  map_add' a b := by ext β; simp [signedCauchyEvaluation, add_div, Finset.sum_add_distrib]
  map_smul' c a := by
    ext β
    simp only [signedCauchyEvaluation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Every strictly negative subspace of a finite signed Pick matrix injects
into the coordinates of its negative atoms. This spectral bound is unrelated
to the physical Weil negative index. -/
theorem finite_signed_pick_negative_subspace_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] (eigenvalue residue : ι → ℝ) (points : κ → ℂ)
    (N : Submodule ℂ (κ → ℂ))
    (hN : ∀ a : N, a ≠ 0 →
      (∑ j, ∑ k, (a : κ → ℂ) j *
        signedPickKernel eigenvalue residue (points j) (points k) * star ((a : κ → ℂ) k)).re < 0) :
    Module.finrank ℂ N ≤ Fintype.card {β : ι // residue β < 0} := by
  classical
  let q : N →ₗ[ℂ] ({β : ι // residue β < 0} → ℂ) :=
    (LinearMap.pi fun β => (LinearMap.proj β.val).comp
      (signedCauchyLinearMap eigenvalue points)).comp N.subtype
  have hq : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    have hn := hN a hne
    rw [finite_signed_pick_gram_re] at hn
    have hp : 0 ≤ ∑ β, residue β *
        Complex.normSq (signedCauchyEvaluation eigenvalue points (a : κ → ℂ) β) := by
      apply Finset.sum_nonneg
      intro β _
      by_cases hb : residue β < 0
      · have hz := congrFun ha ⟨β, hb⟩
        change signedCauchyEvaluation eigenvalue points (a : κ → ℂ) β = 0 at hz
        simp [hz]
      · exact mul_nonneg (le_of_not_gt hb) (Complex.normSq_nonneg _)
    linarith
  simpa using q.finrank_le_finrank_of_injective hq

/-- Inclusion of the negative atom coordinates into all spectral coordinates. -/
def negativeAtomEmbedding {ι : Type*} (residue : ι → ℝ) :
    ({β : ι // residue β < 0} → ℂ) →ₗ[ℂ] (ι → ℂ) := by
  classical
  exact LinearMap.pi fun β => if h : residue β < 0 then LinearMap.proj ⟨β, h⟩ else 0

theorem negativeAtomEmbedding_injective {ι : Type*} (residue : ι → ℝ) :
    Function.Injective (negativeAtomEmbedding residue) := by
  classical
  intro v w h
  ext β
  have hh := congrFun h β.val
  simpa [negativeAtomEmbedding, β.property] using hh

/-- Equality of the spectral negative index when a square finite Cauchy map
is an equivalence. Full rank is explicit and is not inferred from rank one
intertwining or from the physical predecessor geometry. -/
theorem finite_signed_pick_negative_subspace_exact {ι κ : Type*}
    [Fintype ι] [Fintype κ] (eigenvalue residue : ι → ℝ) (points : κ → ℂ)
    (e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (he : ∀ a, e a = signedCauchyLinearMap eigenvalue points a) :
    (∀ N : Submodule ℂ (κ → ℂ),
      (∀ a : N, a ≠ 0 →
        (∑ j, ∑ k, (a : κ → ℂ) j * signedPickKernel eigenvalue residue
          (points j) (points k) * star ((a : κ → ℂ) k)).re < 0) →
        Module.finrank ℂ N ≤ Fintype.card {β : ι // residue β < 0}) ∧
    ∃ N : Submodule ℂ (κ → ℂ),
      Module.finrank ℂ N = Fintype.card {β : ι // residue β < 0} ∧
      ∀ a : N, a ≠ 0 →
        (∑ j, ∑ k, (a : κ → ℂ) j * signedPickKernel eigenvalue residue
          (points j) (points k) * star ((a : κ → ℂ) k)).re < 0 := by
  classical
  refine ⟨fun N hN => finite_signed_pick_negative_subspace_bound eigenvalue residue points N hN, ?_⟩
  let J := e.symm.toLinearMap.comp (negativeAtomEmbedding residue)
  have hJ : Function.Injective J := e.symm.injective.comp (negativeAtomEmbedding_injective residue)
  refine ⟨J.range, ?_, ?_⟩
  · simpa using J.finrank_range_of_inj hJ
  · intro a ha
    obtain ⟨v, hv⟩ := a.property
    have hv0 : v ≠ 0 := by
      intro hz
      apply ha
      apply Subtype.ext
      simpa [hz] using hv.symm
    obtain ⟨β, hβ⟩ : ∃ β, v β ≠ 0 := by
      by_contra! hh
      apply hv0
      ext β
      exact hh β
    have hcoord : signedCauchyEvaluation eigenvalue points (a : κ → ℂ) =
        negativeAtomEmbedding residue v := by
      change signedCauchyLinearMap eigenvalue points (a : κ → ℂ) = _
      rw [← he, ← hv]
      exact e.apply_symm_apply _
    rw [finite_signed_pick_gram_re, hcoord]
    have hn (γ : ι) : residue γ * Complex.normSq (negativeAtomEmbedding residue v γ) ≤ 0 := by
      by_cases hγ : residue γ < 0
      · exact mul_nonpos_of_nonpos_of_nonneg hγ.le (Complex.normSq_nonneg _)
      · simp [negativeAtomEmbedding, hγ]
    have hb : residue β.val * Complex.normSq (negativeAtomEmbedding residue v β.val) < 0 := by
      simp only [negativeAtomEmbedding, LinearMap.pi_apply, dif_pos β.property,
        LinearMap.proj_apply]
      exact mul_neg_of_neg_of_pos β.property (Complex.normSq_pos.mpr hβ)
    simpa using Finset.sum_lt_sum (fun γ _ => hn γ) ⟨β.val, Finset.mem_univ _, hb⟩

end Zeta23.OPICARound4

