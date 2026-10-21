import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Analytic.Basic
import Zeta23.OPICA.EnergyRate
import Mathlib.Tactic

namespace Zeta23.OPICA
open Filter Topology
open scoped BigOperators Matrix
noncomputable section

def linearGram : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∫ t in (0:ℝ)..1, (if i=0 then 1 else t)*(if j=0 then 1 else t)

theorem linearGram_eq : linearGram = !![(1:ℝ), 1/2; 1/2, 1/3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linearGram, ← pow_two, integral_pow, integral_id]

theorem gram_integral_not_rank_one :
    linearGram.det = (1:ℝ)/12 ∧ linearGram.rank = 2 ∧ linearGram.rank ≠ 1 := by
  have hd : linearGram.det = (1:ℝ)/12 := by
    rw [linearGram_eq]; norm_num [Matrix.det_fin_two]
  have hne : linearGram.det ≠ 0 := by rw [hd]; norm_num
  have hr : linearGram.rank = 2 := by simpa using Matrix.rank_of_det_ne_zero hne
  exact ⟨hd,hr,by omega⟩

theorem linearGram_posSemidef : linearGram.PosSemidef := by
  rw [linearGram_eq]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · intro x
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1 / 2), sq_nonneg (x 1)]

theorem single_vector_bound_not_operator_bound (C : ℝ) :
    ∃ L : Matrix (Fin 2) (Fin 2) ℝ,
      (![1,0] : Fin 2 → ℝ) ⬝ᵥ (L *ᵥ ![1,0]) = 0 ∧
      C < (![0,1] : Fin 2 → ℝ) ⬝ᵥ (L *ᵥ ![0,1]) := by
  refine ⟨!![0,0; 0,C+1], ?_⟩
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem offDiagonal_mask_not_posSemidef :
    ¬ Matrix.PosSemidef (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hn

def contrast (d : ℕ) (v : Fin d → ℝ) (i : Fin d) : ℝ :=
  v i - (∑ j, v j)/(d:ℝ)

theorem contrast_cannot_recover_sum (d : ℕ) (hd : 0 < d) :
    contrast d (fun _ => 1) = 0 ∧
      ¬ ∃ recovered : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        ∀ v, recovered (contrast d v) = ∑ j, v j := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc : contrast d (fun _ => 1) = 0 := by
    ext i; simp [contrast, hd']
  refine ⟨hc, ?_⟩
  rintro ⟨R,hR⟩
  have h := hR (fun _ => 1)
  rw [hc, map_zero] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact hd' h.symm

/-- The six coefficients themselves witness compatibility at any seven sample points. -/
theorem seven_samples_six_coefficients_consistent (sample : Fin 7 → ℂ)
    (coeff : Fin 6 → ℂ) :
    ∃ a : Fin 6 → ℂ, ∀ i : Fin 7,
      (∑ j : Fin 6, a j * sample i ^ (j:ℕ)) =
        ∑ j : Fin 6, coeff j * sample i ^ (j:ℕ) := by
  exact ⟨coeff, fun _ => rfl⟩

/-- An analytic constant can cancel a completed simple pole's leading value. -/
theorem analytic_addition_can_cancel_completed_jet :
    AnalyticAt ℂ (fun _ : ℂ => (-1:ℂ)) 0 ∧
      AnalyticAt ℂ (fun z : ℂ => z) 0 ∧
      (∀ z : ℂ, z ≠ 0 → z * (1/z) = 1) ∧
      (1:ℂ) ≠ 0 ∧ (1:ℂ) + (-1:ℂ) = 0 := by
  exact ⟨analyticAt_const, analyticAt_id, fun z hz => by field_simp, one_ne_zero, by ring⟩

theorem shifted_exponential_rate (T : HorizonSchedule) (n : ℕ) :
    magnitudeRate T (fun n =>Real.exp (2*T.time n)-1) n=1 := by
  have hp : 0<2*T.time n := by nlinarith [T.positive n]
  have he : 0<Real.exp (2*T.time n)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hp)
  have heq : 1+(Real.exp (2*T.time n)-1)=Real.exp (2*T.time n) := by ring
  simp only [magnitudeRate,Real.norm_eq_abs,abs_of_pos he,heq,Real.log_exp,div_self hp.ne']

theorem unshifted_exponential_rate_limit (T : HorizonSchedule) :
    Tendsto (magnitudeRate T (fun n =>Real.exp (2*T.time n))) atTop (𝓝 1) := by
  let u : ℕ→ℝ := fun n =>Real.exp (2*T.time n)
  let v : ℕ→ℝ := fun n =>Real.exp (2*T.time n)-1
  have hv : Tendsto (magnitudeRate T v) atTop (𝓝 1) := by
    have heq : magnitudeRate T v = fun _ =>1 := by funext n; exact shifted_exponential_rate T n
    rw [heq]
    exact tendsto_const_nhds
  have herr : u-v=fun _=>1 := by funext n; dsimp [u,v]; ring
  exact rate_limit_congr_of_subexp_error T u v (by rw [herr];exact subexpAlong_const T (1:ℝ)) hv

/-- Every scale is a positive unit bounded above by one, but its inverse cost destroys the rate. -/
theorem inverse_scale_can_erase_rate (T : HorizonSchedule) :
    (∀ n,0<Real.exp (-(2*T.time n)) ∧ Real.exp (-(2*T.time n))≤1) ∧
      Tendsto (magnitudeRate T (fun n =>Real.exp (2*T.time n))) atTop (𝓝 1) ∧
      SubexpAlong T (fun n =>Real.exp (-(2*T.time n))*Real.exp (2*T.time n)) := by
  refine ⟨fun n =>⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (by nlinarith [T.positive n])⟩,
    unshifted_exponential_rate_limit T,?_⟩
  have heq : (fun n =>Real.exp (-(2*T.time n))*Real.exp (2*T.time n))=fun _=>1 := by
    funext n
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [heq]
  exact subexpAlong_const T (1:ℝ)

/-- Negative units preserve magnitude but erase the positive-part observation. -/
theorem negative_scale_can_erase_positive_rate (T : HorizonSchedule) :
    Tendsto (positiveRate T (fun n =>Real.exp (2*T.time n))) atTop (𝓝 1) ∧
      Tendsto (positiveRate T (fun n =>-Real.exp (2*T.time n))) atTop (𝓝 0) := by
  have hpos : positiveRate T (fun n =>Real.exp (2*T.time n)) =
      magnitudeRate T (fun n =>Real.exp (2*T.time n)) := by
    funext n
    simp [positiveRate,magnitudeRate,Real.norm_eq_abs,(Real.exp_pos _).le]
  have hneg : positiveRate T (fun n =>-Real.exp (2*T.time n))=fun _=>0 := by
    funext n
    simp [positiveRate,max_eq_right (neg_nonpos.mpr (Real.exp_pos _).le)]
  rw [hpos,hneg]
  exact ⟨unshifted_exponential_rate_limit T,tendsto_const_nhds⟩

theorem high_primitive_does_not_mean_both_high :
    7<max (1:ℕ) 11 ∧ ¬(7<(1:ℕ) ∧ 7<(11:ℕ)) := by decide

theorem common_gcd_need_not_be_coprime_to_primitives :
    Nat.gcd 121 1331=121 ∧ 121/121=1 ∧ 1331/121=11 ∧ Nat.gcd 121 11≠1 := by decide

def integerHorizonSchedule : HorizonSchedule where
  time n := ((n+1:ℕ):ℝ)
  positive n := by exact_mod_cast Nat.succ_pos n
  cofinal := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ =>(n:ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)

/-- Each fixed factor has vanishing cost, while their growing product has positive total cost. -/
theorem accumulated_cost_counterexample :
    Tendsto (fun n =>Real.log 2/(2*integerHorizonSchedule.time n)) atTop (𝓝 0) ∧
      (∀ n : ℕ, Real.log (∏ _i∈Finset.range (n+1),(2:ℝ))/(2*integerHorizonSchedule.time n)=Real.log 2/2) ∧
      0<Real.log 2/2 := by
  refine ⟨tendsto_const_nhds.div_atTop
    (integerHorizonSchedule.cofinal.const_mul_atTop (by norm_num)),?_,
    div_pos (Real.log_pos (by norm_num)) (by norm_num)⟩
  intro n
  simp only [Finset.prod_const,Finset.card_range,Real.log_pow,integerHorizonSchedule]
  field_simp [show ((n+1:ℕ):ℝ)≠0 by exact_mod_cast Nat.succ_ne_zero n]
  <;> ring

end
end Zeta23.OPICA
