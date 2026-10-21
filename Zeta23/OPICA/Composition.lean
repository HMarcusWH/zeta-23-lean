import Zeta23.OPICA.EnergyRate
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace Zeta23.OPICA
open Filter Topology Finset
open scoped BigOperators

def affineChain {R : Type*} [Semiring R] (a b : ℕ → R) (z : R) : ℕ → R
  | 0 => z
  | n+1 => a n * affineChain a b z n + b n

def affineProduct {R : Type*} [CommSemiring R] (a : ℕ → R) (N : ℕ) : R :=
  ∏ i ∈ range N, a i

def affineCorrection {R : Type*} [CommSemiring R] (a b : ℕ → R) (N : ℕ) : R :=
  ∑ j ∈ range N, b j * ∏ i ∈ Ico (j+1) N, a i

theorem affineCorrection_succ {R : Type*} [CommSemiring R] (a b : ℕ → R) (N : ℕ) :
    affineCorrection a b (N+1) = a N * affineCorrection a b N + b N := by
  simp only [affineCorrection, sum_range_succ, Ico_self, prod_empty, mul_one]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [prod_Ico_succ_top (Nat.succ_le_of_lt (mem_range.mp hj))]
  ring

theorem affine_chain_expansion {R : Type*} [CommSemiring R] (a b : ℕ → R) (z : R)
    (N : ℕ) : affineChain a b z N = affineProduct a N * z + affineCorrection a b N := by
  induction N with
  | zero => simp [affineChain, affineProduct, affineCorrection]
  | succ N ih =>
    rw [affineChain, ih, affineCorrection_succ]
    simp only [affineProduct, prod_range_succ]
    ring

theorem affine_chain_budget (a b Z : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, Z (n+1) ≤ a n * Z n + b n) (N : ℕ) :
    Z N ≤ affineProduct a N * Z 0 + affineCorrection a b N := by
  rw [← affine_chain_expansion]
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    exact (hstep N).trans (by simpa [affineChain] using add_le_add_right (mul_le_mul_of_nonneg_left ih (ha N)) (b N))

theorem rate_congr_of_accumulated_budget {𝕜 : Type*} [NormedField 𝕜]
    (T : HorizonSchedule) (a b : ℕ → ℕ → 𝕜) (u : ℕ → 𝕜) (depth : ℕ → ℕ)
    (hA : TemperedAlong T (fun n => affineProduct (fun i => a i n) (depth n)))
    (hB : SubexpAlong T (fun n => affineCorrection (fun i => a i n) (fun i => b i n) (depth n))) :
    Tendsto (fun n => magnitudeRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) (depth n)) n - magnitudeRate T u n) atTop (𝓝 0) := by
  let A : ℕ → 𝕜 := fun n => affineProduct (fun i => a i n) (depth n)
  let B : ℕ → 𝕜 := fun n => affineCorrection (fun i => a i n) (fun i => b i n) (depth n)
  let Z : ℕ → 𝕜 := fun n => affineChain (fun i => a i n) (fun i => b i n) (u n) (depth n)
  have hz : Z - A*u = B := by funext n; dsimp [Z,A,B]; rw [affine_chain_expansion]; ring
  have hadd := rate_congr_of_subexp_error T Z (A*u) (by rwa [hz])
  have hscale := rate_congr_of_tempered_scale T A u hA
  have := hadd.add hscale
  simpa [Z] using this

theorem posRate_congr_of_accumulated_budget
    (T : HorizonSchedule) (a b : ℕ → ℕ → ℝ) (u : ℕ → ℝ) (depth : ℕ → ℕ)
    (hA : TemperedAlong T (fun n => affineProduct (fun i => a i n) (depth n)))
    (hpos : ∀ n, 0 < affineProduct (fun i => a i n) (depth n))
    (hB : SubexpAlong T (fun n => affineCorrection (fun i => a i n) (fun i => b i n) (depth n))) :
    Tendsto (fun n => positiveRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) (depth n)) n - positiveRate T u n) atTop (𝓝 0) := by
  let A : ℕ → ℝ := fun n => affineProduct (fun i => a i n) (depth n)
  let B : ℕ → ℝ := fun n => affineCorrection (fun i => a i n) (fun i => b i n) (depth n)
  let Z : ℕ → ℝ := fun n => affineChain (fun i => a i n) (fun i => b i n) (u n) (depth n)
  have hz : Z - A*u = B := by funext n; dsimp [Z,A,B]; rw [affine_chain_expansion]; ring
  have hadd := posRate_congr_of_subexp_error T Z (A*u) (by rwa [hz])
  have hscale := posRate_congr_of_positive_tempered_scale T A u hA hpos
  have := hadd.add hscale
  simpa [Z] using this

theorem finite_affine_chain_rate {𝕜 : Type*} [NormedField 𝕜]
    (T : HorizonSchedule) (a b : ℕ → ℕ → 𝕜) (u : ℕ → 𝕜)
    (ha : ∀ i, TemperedAlong T (a i)) (hb : ∀ i, SubexpAlong T (b i)) (N : ℕ) :
    Tendsto (fun n => magnitudeRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) N) n - magnitudeRate T u n) atTop (𝓝 0) := by
  induction N with
  | zero => simpa [affineChain] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  | succ N ih =>
    let Z : ℕ → 𝕜 := fun n => affineChain (fun i => a i n) (fun i => b i n) (u n) N
    have hz : (a N*Z+b N) - (a N*Z) = b N := by funext n; simp
    have hadd := rate_congr_of_subexp_error T (a N*Z+b N) (a N*Z) (by rw [hz]; exact hb N)
    have hscale := rate_congr_of_tempered_scale T (a N) Z (ha N)
    have hlim := (hadd.add hscale).add ih
    simpa [Z,affineChain,magnitudeRate] using hlim

/-- At a fixed finite depth, each positive tempered scale and each
subexponential affine error preserve the positive-part rate. -/
theorem finite_affine_chain_posRate
    (T : HorizonSchedule) (a b : ℕ → ℕ → ℝ) (u : ℕ → ℝ)
    (ha : ∀ i, TemperedAlong T (a i)) (hpos : ∀ i n, 0 < a i n)
    (hb : ∀ i, SubexpAlong T (b i)) (N : ℕ) :
    Tendsto (fun n => positiveRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) N) n - positiveRate T u n) atTop (𝓝 0) := by
  induction N with
  | zero => simpa [affineChain] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  | succ N ih =>
    let Z : ℕ → ℝ := fun n => affineChain (fun i => a i n) (fun i => b i n) (u n) N
    have hz : (a N*Z+b N) - (a N*Z) = b N := by funext n; simp
    have hadd := posRate_congr_of_subexp_error T (a N*Z+b N) (a N*Z)
      (by rw [hz]; exact hb N)
    have hscale := posRate_congr_of_positive_tempered_scale T (a N) Z (ha N) (hpos N)
    have hlim := (hadd.add hscale).add ih
    simpa [Z,affineChain,positiveRate] using hlim

theorem quiet_cofinal_rate_zero (T : HorizonSchedule) (E : ℝ → ℝ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hE : ∀ t, 0 ≤ E t)
    (hfull : Tendsto (fun t => Real.log (1+E t)/(2*t)) atTop (𝓝 θ))
    (C b : ℕ → ℝ) (hC : ∀ n, 0 < C n)
    (hb : Tendsto b atTop (𝓝 0))
    (hcost : Tendsto (fun n => Real.log (C n)/(2*T.time n)) atTop (𝓝 0))
    (hquiet : ∀ n, 1+E (T.time n) ≤ C n * Real.exp (2*b n*T.time n)) : θ = 0 := by
  have hlim := hfull.comp T.cofinal
  have hbound : ∀ n, Real.log (1+E (T.time n))/(2*T.time n) ≤
      Real.log (C n)/(2*T.time n) + b n := by
    intro n
    have hEn := hE (T.time n)
    have hl := Real.log_le_log (by positivity : 0 < 1+E (T.time n)) (hquiet n)
    rw [Real.log_mul (hC n).ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hp : 0 < 2*T.time n := by nlinarith [T.positive n]
    calc Real.log (1+E (T.time n))/(2*T.time n) ≤
        (Real.log (C n)+2*b n*T.time n)/(2*T.time n) :=
          div_le_div_of_nonneg_right hl hp.le
         _ = Real.log (C n)/(2*T.time n)+b n := by
           field_simp [(T.positive n).ne']
           <;> ring
  have hzero : Tendsto (fun n => Real.log (C n)/(2*T.time n)+b n) atTop (𝓝 0) := by
    simpa using hcost.add hb
  exact le_antisymm (le_of_tendsto_of_tendsto' hlim hzero hbound) hθ

section Quotient
variable {K V W X : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X]

theorem quotient_map_injective_iff (N : Submodule K V) (N' : Submodule K W)
    (f : V →ₗ[K] W) (hf : N ≤ N'.comap f) :
    Function.Injective (N.mapQ N' f hf) ↔ N'.comap f = N := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
  constructor
  · intro h
    have hc := congrArg (Submodule.comap N.mkQ) h
    simpa [sup_eq_right.mpr hf] using hc
  · intro h
    rw [h, Submodule.mkQ_map_self]

theorem faithful_transfer_comp (N : Submodule K V) (N' : Submodule K W)
    (N'' : Submodule K X) (f : V →ₗ[K] W) (g : W →ₗ[K] X)
    (hf : N ≤ N'.comap f) (hg : N' ≤ N''.comap g)
    (hfi : Function.Injective (N.mapQ N' f hf))
    (hgi : Function.Injective (N'.mapQ N'' g hg)) :
    Function.Injective (N.mapQ N'' (g.comp f) (hf.trans (Submodule.comap_mono hg))) := by
  rw [Submodule.mapQ_comp N N' N'' f g hf hg]
  exact hgi.comp hfi
end Quotient

theorem obstruction_path_nonzero
    (S Ω : ℕ → Type*) (zero : ∀ i, Ω i)
    (admissible : ∀ i, S i → Prop) (obs : ∀ i, S i → Ω i)
    (transition : ∀ i, S i → S (i+1)) (carrier : ∀ i, Ω i → Ω (i+1))
    (preserve : ∀ i s, admissible i s → admissible (i+1) (transition i s))
    (commute : ∀ i s, admissible i s → obs (i+1) (transition i s) = carrier i (obs i s))
    (reflect : ∀ i w, carrier i w = zero (i+1) → w = zero i)
    (states : ∀ i, S i) (hstates : ∀ i, states (i+1) = transition i (states i))
    (ha : admissible 0 (states 0)) (h0 : obs 0 (states 0) ≠ zero 0) (N : ℕ) :
    admissible N (states N) ∧ obs N (states N) ≠ zero N := by
  induction N with
  | zero => exact ⟨ha, h0⟩
  | succ N ih =>
    rw [hstates N]
    refine ⟨preserve N _ ih.1, ?_⟩
    rw [commute N _ ih.1]
    exact fun h => ih.2 (reflect N _ h)

theorem implication_path_nonzero (S Ω : ℕ → Type*) (zero : ∀ i, Ω i)
    (obs : ∀ i, S i → Ω i) (transition : ∀ i, S i → S (i+1))
    (edge : ∀ i s, obs i s ≠ zero i → obs (i+1) (transition i s) ≠ zero (i+1))
    (states : ∀ i, S i) (hstates : ∀ i, states (i+1) = transition i (states i))
    (h0 : obs 0 (states 0) ≠ zero 0) (N : ℕ) : obs N (states N) ≠ zero N := by
  induction N with
  | zero => exact h0
  | succ N ih => rw [hstates N]; exact edge N _ ih

end Zeta23.OPICA
