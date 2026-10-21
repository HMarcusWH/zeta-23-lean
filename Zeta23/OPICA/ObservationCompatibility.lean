import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

namespace Zeta23.OPICA
open scoped ComplexOrder

/-- A finite family of square-integrable complex observations gives an actual PSD Gram integral.
The `Lp` carrier supplies measurability and every entry's integrability. -/
theorem gram_integral_posSemidef {A I 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace A] [Fintype I]
    (μ : MeasureTheory.Measure A) (ψ : I → MeasureTheory.Lp 𝕜 2 μ) :
    Matrix.PosSemidef (fun i j => ∫ t, inner 𝕜 (ψ i t) (ψ j t) ∂μ) := by
  have heq : (fun i j => ∫ t, inner 𝕜 (ψ i t) (ψ j t) ∂μ) = Matrix.gram 𝕜 ψ := by
    ext i j
    rw [Matrix.gram_apply, MeasureTheory.L2.inner_def]
  rw [heq]
  exact Matrix.posSemidef_gram 𝕜 ψ

section Recovery
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem observation_factors_iff_ker_le (P : V →ₗ[K] W) (l : V →ₗ[K] K) :
    (∃ recovered : P.range →ₗ[K] K, l = recovered.comp P.rangeRestrict) ↔
      P.ker ≤ l.ker := by
  constructor
  · rintro ⟨r, rfl⟩ x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have h : P.rangeRestrict x = 0 := Subtype.ext hx
    simp [h]
  · intro h
    refine ⟨(P.ker.liftQ l h).comp P.quotKerEquivRange.symm.toLinearMap, ?_⟩
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change l x = P.ker.liftQ l h (P.quotKerEquivRange.symm ⟨P x, _⟩)
    rw [P.quotKerEquivRange_symm_apply_image]
    rfl

theorem solutions_preserved_under_left_map {X : Type*} [AddCommGroup X] [Module K X]
    (B : V →ₗ[K] W) (S : W →ₗ[K] X) (b : W) :
    {v | B v = b} ⊆ {v | (S.comp B) v = S b} := by
  intro v hv
  simp only [Set.mem_ofPred_eq, LinearMap.comp_apply] at *
  rw [hv]

theorem compatibility_under_invertible_left_map {X : Type*} [AddCommGroup X] [Module K X]
    (B : V →ₗ[K] W) (S : W ≃ₗ[K] X) (b : W) :
    {v | B v = b} = {v | S (B v) = S b} := by
  ext v
  exact S.injective.eq_iff.symm
end Recovery

section FiniteCompatibility
open scoped InnerProductSpace
open ComplexConjugate
open Metric
noncomputable section

variable {d n : ℕ}
local notation "Input" => EuclideanSpace ℂ (Fin d)
local notation "Output" => EuclideanSpace ℂ (Fin n)

private theorem residual_pairing (B : Input →L[ℂ] Output) (b : Output) :
    let r := b - B.range.starProjection b
    B.adjoint r = 0 ∧ ⟪r, b⟫_ℂ = ⟪r, r⟫_ℂ := by
  dsimp
  have hr := B.range.sub_starProjection_mem_orthogonal b
  constructor
  · simpa [B.orthogonal_range] using hr
  · have hp := Submodule.inner_left_of_mem_orthogonal
      (B.range.starProjection_apply_mem b) hr
    calc ⟪b-B.range.starProjection b,b⟫_ℂ =
        ⟪b-B.range.starProjection b,(b-B.range.starProjection b)+B.range.starProjection b⟫_ℂ := by
          congr 1; abel
         _ = _ := by rw [inner_add_right, hp, add_zero]

theorem incompatible_iff_left_annihilator (B : Input →L[ℂ] Output) (b : Output) :
    b ∉ B.range ↔ ∃ y : Output, B.adjoint y = 0 ∧ ⟪y, b⟫_ℂ ≠ 0 := by
  constructor
  · intro hb
    let r := b - B.range.starProjection b
    have hr : r ≠ 0 := by
      intro h
      have heq : b = B.range.starProjection b := sub_eq_zero.mp h
      exact hb (heq ▸ B.range.starProjection_apply_mem b)
    have hp := residual_pairing B b
    exact ⟨r, hp.1, by rw [hp.2]; exact (inner_self_ne_zero.mpr hr)⟩
  · rintro ⟨y, hy, hb⟩ ⟨x,hx⟩
    apply hb
    rw [← hx]
    change ⟪y,B x⟫_ℂ = 0
    calc ⟪y,B x⟫_ℂ = ⟪B.adjoint y,x⟫_ℂ := (B.adjoint_inner_left x y).symm
         _ = 0 := by rw [hy, inner_zero_left]

private theorem residual_distance (B : Input →L[ℂ] Output) (b : Output) :
    infDist b (B.range : Set Output) = ‖b - B.range.starProjection b‖ := by
  apply le_antisymm
  · simpa only [dist_eq_norm] using
      infDist_le_dist_of_mem (B.range.starProjection_apply_mem b)
  · have hn : (B.range : Set Output).Nonempty := ⟨0,B.range.zero_mem⟩
    apply (le_infDist hn).mpr
    intro z hz
    rw [Submodule.starProjection_minimal, dist_eq_norm]
    exact ciInf_le ⟨0, by rintro q ⟨x,rfl⟩; exact norm_nonneg _⟩ (⟨z,hz⟩ : B.range)

theorem range_distance_eq_annihilator_sup (B : Input →L[ℂ] Output) (b : Output) :
    infDist b (B.range : Set Output) =
      sSup {q : ℝ | ∃ y : Output, B.adjoint y = 0 ∧ ‖y‖ ≤ 1 ∧ q = ‖⟪y,b⟫_ℂ‖} := by
  let r := b - B.range.starProjection b
  have hr := B.range.sub_starProjection_mem_orthogonal b
  have hp := residual_pairing B b
  rw [residual_distance]
  change ‖r‖ = _
  have upper : ∀ y : Output, B.adjoint y = 0 → ‖y‖ ≤ 1 → ‖⟪y,b⟫_ℂ‖ ≤ ‖r‖ := by
    intro y hy hn
    have hy' : y ∈ B.rangeᗮ := by simpa [B.orthogonal_range] using hy
    have hz := Submodule.inner_left_of_mem_orthogonal (B.range.starProjection_apply_mem b) hy'
    have hpair : ⟪y,b⟫_ℂ = ⟪y,r⟫_ℂ := by simp only [r, inner_sub_right, hz, sub_zero]
    rw [hpair]
    exact (norm_inner_le_norm y r).trans (by nlinarith [norm_nonneg r])
  have attain : ∃ y : Output, B.adjoint y = 0 ∧ ‖y‖ ≤ 1 ∧ ‖r‖ = ‖⟪y,b⟫_ℂ‖ := by
    by_cases hz : r = 0
    · exact ⟨0, by simp, by simp, by simp [hz]⟩
    · let y : Output := (‖r‖⁻¹ : ℝ) • r
      have hn : 0 < ‖r‖ := norm_pos_iff.mpr hz
      have hy : y ∈ B.rangeᗮ := ((B.rangeᗮ).restrictScalars ℝ).smul_mem (‖r‖⁻¹ : ℝ) hr
      refine ⟨y, by simpa [B.orthogonal_range] using hy, ?_, ?_⟩
      · simp [y, norm_smul, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
      · have hpair : ‖⟪r,b⟫_ℂ‖ = ‖r‖^2 := by
          rw [hp.2, ← inner_self_re_eq_norm, inner_self_eq_norm_sq]
        rw [show ⟪y,b⟫_ℂ = (‖r‖⁻¹ : ℝ) • ⟪r,b⟫_ℂ by
          dsimp [y]
          simpa only [Complex.real_smul, Complex.ofReal_inv] using
            (inner_smul_left_eq_smul (𝕜 := ℂ) r b (‖r‖⁻¹ : ℝ))]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, hpair]
        field_simp
  apply Eq.symm
  apply IsLUB.csSup_eq
  · constructor
    · rintro q ⟨y,hy,hn,rfl⟩
      exact upper y hy hn
    · intro q hq
      rcases attain with ⟨y,hy,hn,heq⟩
      exact hq ⟨y,hy,hn,heq⟩
  · exact ⟨‖r‖, attain⟩
end
end FiniteCompatibility

end Zeta23.OPICA
