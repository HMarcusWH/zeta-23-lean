import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Finset.Max

noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

namespace Zeta23.OPICARound4.RegularCells

def imaginaryReciprocal (x : ℝ) : ℂ := Complex.I / (x : ℂ)

theorem imaginaryReciprocal_tendsto :
    Tendsto imaginaryReciprocal atTop (𝓝 (0 : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  unfold imaginaryReciprocal
  simpa only [div_eq_mul_inv, Function.comp_apply, Complex.ofReal_inv,
    Complex.ofReal_zero, mul_zero]
    using h.const_mul Complex.I

theorem imaginaryReciprocal_tendsto_punctured :
    Tendsto imaginaryReciprocal atTop (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨imaginaryReciprocal_tendsto, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact div_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')

/-- A finite pole becomes at most polynomial growth on the exact imaginary ray. -/
theorem meromorphic_imaginaryReciprocal_isBigO_pow {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) :
    ∃ n : ℕ, (fun x : ℝ => f (imaginaryReciprocal x)) =O[atTop] (fun x => x^n) := by
  obtain ⟨n, hn⟩ := hf
  have hb := (hn.continuousAt.tendsto.comp imaginaryReciprocal_tendsto).isBigO_one ℝ
  obtain ⟨C, hC⟩ := hb.bound
  refine ⟨n, IsBigO.of_bound C ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with x hx hp
  have hx0 : x ≠ 0 := hp.ne'
  have hp0 : 0 < x^n := pow_pos hp n
  simp only [Function.comp_apply, sub_zero, smul_eq_mul, norm_mul, norm_pow,
    norm_one, mul_one] at hx
  have hnrm : ‖imaginaryReciprocal x‖ = x⁻¹ := by
    simp [imaginaryReciprocal, Real.norm_of_nonneg hp.le]
  rw [hnrm, inv_pow] at hx
  have hx' : ‖f (imaginaryReciprocal x)‖ / x^n ≤ C := by
    simpa [div_eq_mul_inv, mul_comm] using hx
  simpa [Real.norm_of_nonneg hp0.le] using (div_le_iff₀ hp0).mp hx'

/-- A meromorphic coefficient is dominated by every fixed positive exponential. -/
theorem meromorphic_imaginaryReciprocal_div_exp_tendsto_zero {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => f (imaginaryReciprocal x) / (Real.exp (b*x) : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨n,hn⟩ := meromorphic_imaginaryReciprocal_isBigO_pow hf
  have ho := hn.trans_isLittleO (isLittleO_pow_exp_pos_mul_atTop n hb)
  have hoc : (fun x : ℝ => f (imaginaryReciprocal x)) =o[atTop]
      (fun x => (Real.exp (b*x) : ℂ)) := by
    apply IsLittleO.of_norm_right
    have hnrm : (fun x : ℝ => ‖(Real.exp (b*x) : ℂ)‖) =
        (fun x => Real.exp (b*x)) := by
      funext x
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hnrm]
    exact ho
  exact hoc.tendsto_div_nhds_zero

def frequencyRayTerm (a : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  a (imaginaryReciprocal x) * (Real.exp (c*x) : ℂ)

theorem frequencyRayTerm_div (a b : ℂ → ℂ) (c d x : ℝ) :
    frequencyRayTerm a c x / frequencyRayTerm b d x =
      (a (imaginaryReciprocal x) / b (imaginaryReciprocal x)) /
        (Real.exp ((d-c)*x) : ℂ) := by
  unfold frequencyRayTerm
  rw [mul_div_mul_comm, ← Complex.ofReal_div, ← Real.exp_sub]
  rw [show c*x-d*x = -((d-c)*x) by ring, Real.exp_neg, Complex.ofReal_inv]
  rfl

/-- The maximal nonzero coefficient controls the finite exponential sum. -/
theorem meromorphic_frequency_ray_max_nonzero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ → ℂ) (c : ι → ℝ) (j : ι)
    (hj : j ∈ s) (ha : ∀ i ∈ s, MeromorphicAt (a i) 0)
    (hnz : ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), a j z = 0)
    (hmax : ∀ i ∈ s, i ≠ j →
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), a i z = 0) ∨ c i < c j) :
    ¬ ∀ᶠ x : ℝ in atTop, ∑ i ∈ s, frequencyRayTerm (a i) (c i) x = 0 := by
  have hnj := (ha j hj).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnz
  have hnjx := imaginaryReciprocal_tendsto_punctured.eventually hnj
  have hterm : ∀ i ∈ s, Tendsto
      (fun x : ℝ => frequencyRayTerm (a i) (c i) x /
        frequencyRayTerm (a j) (c j) x) atTop (𝓝 (if i = j then 1 else 0)) := by
    intro i hi
    by_cases hij : i = j
    · subst i
      apply tendsto_const_nhds.congr'
      filter_upwards [hnjx] with x hx
      simp [frequencyRayTerm, hx]
    · simp only [if_neg hij]
      rcases hmax i hi hij with hz | hlt
      · apply tendsto_const_nhds.congr'
        filter_upwards [imaginaryReciprocal_tendsto_punctured.eventually hz] with x hx
        simp [frequencyRayTerm, hx]
      · have ht := meromorphic_imaginaryReciprocal_div_exp_tendsto_zero
          ((ha i hi).div (ha j hj)) (sub_pos.mpr hlt)
        simpa only [frequencyRayTerm_div, Pi.div_apply] using ht
  have hs := tendsto_finsetSum s hterm
  have hs1 : Tendsto (fun x : ℝ =>
      (∑ i ∈ s, frequencyRayTerm (a i) (c i) x) /
        frequencyRayTerm (a j) (c j) x) atTop (𝓝 (1 : ℂ)) := by
    simpa only [div_eq_mul_inv, Finset.sum_mul, Finset.sum_ite_eq', if_pos hj] using hs
  intro hz
  have hz0 : Tendsto (fun x : ℝ =>
      (∑ i ∈ s, frequencyRayTerm (a i) (c i) x) /
        frequencyRayTerm (a j) (c j) x) atTop (𝓝 (0 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with x hx
    simp [hx]
  exact one_ne_zero (tendsto_nhds_unique hs1 hz0)

/-- Distinct real rates and at least one nonzero meromorphic germ cannot cancel. -/
theorem meromorphic_frequency_ray_nonzero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ → ℂ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, MeromorphicAt (a i) 0)
    (hc : Set.InjOn c (s : Set ι))
    (hne : ∃ i ∈ s, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), a i z = 0) :
    ¬ ∀ᶠ x : ℝ in atTop, ∑ i ∈ s, frequencyRayTerm (a i) (c i) x = 0 := by
  classical
  let t := s.filter fun i => ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), a i z = 0
  have ht : t.Nonempty := by
    obtain ⟨i,hi,hn⟩ := hne
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hn⟩⟩
  obtain ⟨j,hj,hmax⟩ := t.exists_max_image c ht
  obtain ⟨hjs,hjn⟩ := Finset.mem_filter.mp hj
  apply meromorphic_frequency_ray_max_nonzero s a c j hjs ha hjn
  intro i hi hij
  by_cases hz : ∀ᶠ z in 𝓝[≠] (0 : ℂ), a i z = 0
  · exact Or.inl hz
  · right
    apply lt_of_le_of_ne (hmax i (Finset.mem_filter.mpr ⟨hi,hz⟩))
    exact fun he => hij (hc hi hjs he)

theorem exp_frequency_imaginaryReciprocal (c x : ℝ) (hx : x ≠ 0) :
    Complex.exp ((c : ℂ) * Complex.I / imaginaryReciprocal x) =
      (Real.exp (c*x) : ℂ) := by
  have hi : (c : ℂ) * Complex.I / imaginaryReciprocal x = ((c*x : ℝ) : ℂ) := by
    unfold imaginaryReciprocal
    push_cast
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hx]
  rw [hi, Complex.ofReal_exp]

/-- Finite exponential independence over the actual field of meromorphic germs. -/
theorem meromorphic_frequency_germ_nonzero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ → ℂ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, MeromorphicAt (a i) 0)
    (hc : Set.InjOn c (s : Set ι))
    (hne : ∃ i ∈ s, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), a i z = 0) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ∑ i ∈ s, a i z * Complex.exp ((c i : ℂ) * Complex.I / z) = 0 := by
  intro hz
  apply meromorphic_frequency_ray_nonzero s a c ha hc hne
  filter_upwards [imaginaryReciprocal_tendsto_punctured.eventually hz,
    eventually_gt_atTop (0 : ℝ)] with x hx hp
  simpa only [frequencyRayTerm, exp_frequency_imaginaryReciprocal _ _ hp.ne'] using hx

end Zeta23.OPICARound4.RegularCells
