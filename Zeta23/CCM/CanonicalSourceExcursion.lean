import Zeta23.CCM.CanonicalSourceWeightedIntegral

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate Interval

/-!
# POST285 M70 (Step 108): quantitative positive and negative source excursions

For a zero-sum coefficient vector `z` (`∑ z = 0`) put `u = D z` (`u_n = n z_n`)
and `e(ω) = Re e_u(ω) = Re ⟪u, S_K(ω) u⟫`.  The integrated identities of
`CanonicalSourceWeightedIntegral.lean` give

* `∫₀¹ e = 0` (the centre coordinate of `u` vanishes),
* `∫₀¹ (1-ω) e = -‖z‖² / (2π²)`,
* hence `∫₀¹ ω e = +‖z‖² / (2π²)`.

Since `∫₀¹ ω = ∫₀¹ (1-ω) = 1/2` and `e(0) = 0`, for `z ≠ 0` there are interior
source coordinates with

* `e(ω₊) > ‖z‖² / π²`  and  `e(ω₋) < -‖z‖² / π²`.

The magnitude is independent of the dimension `K`.  This is a statement about
the elementary source form only; it is not a sign of the canonical operator or
of the full pole/archimedean/prime functional, and it proves nothing about
contacts or RH.
-/

theorem quadraticForm_sourceMatrix_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    quadraticForm (sourceMatrix 0 N) u = 0 := by
  rw [sourceMatrix_zero]
  simp [quadraticForm]

/-- Real elementary source energy along the source coordinate. -/
def sourceEnergyRe (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (ω : ℝ) : ℝ :=
  (quadraticForm (sourceMatrix ω N) u).re

theorem continuous_sourceEnergyRe (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Continuous (sourceEnergyRe N u) :=
  Complex.continuous_re.comp (continuous_quadraticForm_sourceMatrix N u)

theorem sourceEnergyRe_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    sourceEnergyRe N u 0 = 0 := by
  unfold sourceEnergyRe
  rw [quadraticForm_sourceMatrix_zero, Complex.zero_re]

/-- `∫₀¹ Re e_u = |u₀|²` in real form. -/
theorem integral_sourceEnergyRe (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    ∫ ω in (0 : ℝ)..1, sourceEnergyRe N u ω =
      ∑ i, if centeredIndex N i = 0 then Complex.normSq (u i) else 0 := by
  have hre := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume)
    (a := 0) (b := 1) ((continuous_quadraticForm_sourceMatrix N u).intervalIntegrable 0 1)
  simp only [RCLike.re_to_complex] at hre
  unfold sourceEnergyRe
  rw [hre, integral_quadraticForm_sourceMatrix, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  · rfl

/-- Centre coordinate of `D z` vanishes, so `∫₀¹ Re e_{Dz} = 0`. -/
theorem integral_sourceEnergyRe_indexAction (N : ℕ) (z : Fin (2 * N + 1) → ℂ) :
    ∫ ω in (0 : ℝ)..1, sourceEnergyRe N (indexMatrix N *ᵥ z) ω = 0 := by
  rw [integral_sourceEnergyRe]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · simp [indexMatrix, Matrix.mulVec_diagonal, hi]
  · rfl

/-- Weighted negative identity in `sourceEnergyRe` notation. -/
theorem integral_one_sub_mul_sourceEnergyRe_indexAction (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hsum : ∑ i, z i = 0) :
    ∫ ω in (0 : ℝ)..1, (1 - ω) * sourceEnergyRe N (indexMatrix N *ᵥ z) ω =
      -(1 / (2 * Real.pi ^ 2)) * ∑ i, Complex.normSq (z i) :=
  integral_one_sub_mul_re_energy_indexAction N z hsum

/-- **Weighted positive identity:** `∫₀¹ ω Re e_{Dz} = +‖z‖² / (2π²)`. -/
theorem integral_mul_sourceEnergyRe_indexAction (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hsum : ∑ i, z i = 0) :
    ∫ ω in (0 : ℝ)..1, ω * sourceEnergyRe N (indexMatrix N *ᵥ z) ω =
      (1 / (2 * Real.pi ^ 2)) * ∑ i, Complex.normSq (z i) := by
  set f := sourceEnergyRe N (indexMatrix N *ᵥ z)
  have hf : Continuous f := continuous_sourceEnergyRe N _
  have hsplit : (fun ω : ℝ => ω * f ω) = fun ω => f ω - (1 - ω) * f ω := by
    funext ω; ring
  rw [hsplit, intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun ω : ℝ => (1 - ω) * f ω).intervalIntegrable 0 1),
    integral_sourceEnergyRe_indexAction, integral_one_sub_mul_sourceEnergyRe_indexAction N z hsum]
  ring

/-- A continuous function, nonnegative on `[η, 1]` and positive on `(0, η)`, has
positive integral over `[0, 1]`. -/
theorem integral_pos_of_pos_near_zero (φ : ℝ → ℝ) (hφ : Continuous φ) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) η, 0 < φ x)
    (hnn : ∀ x ∈ Set.Icc η 1, 0 ≤ φ x) :
    0 < ∫ x in (0 : ℝ)..1, φ x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hφ.intervalIntegrable 0 η)
    (hφ.intervalIntegrable η 1)]
  have h1 : 0 < ∫ x in (0 : ℝ)..η, φ x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hφ.intervalIntegrable 0 η) hpos hη
  have h2 : 0 ≤ ∫ x in η..1, φ x := intervalIntegral.integral_nonneg hη1 hnn
  linarith

/-- A neighbourhood of `0` on which a continuous function vanishing at `0`
stays above `-ε`. -/
theorem exists_Ioo_gt_of_continuous_zero (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η, 0 < η ∧ η ≤ 1 ∧ ∀ x ∈ Set.Ioo (0 : ℝ) η, -ε < f x ∧ f x < ε := by
  have hopen : IsOpen {x : ℝ | -ε < f x ∧ f x < ε} :=
    (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have h0 : (0 : ℝ) ∈ {x : ℝ | -ε < f x ∧ f x < ε} := by
    simp only [Set.mem_ofPred_eq, hf0]
    exact ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  refine ⟨min (δ / 2) 1, by positivity, min_le_right _ _, ?_⟩
  intro x hx
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
  have : x < δ / 2 := lt_of_lt_of_le hx.2 (min_le_left _ _)
  linarith

/-- Extension of a lower bound from `(0, 1)` to `[0, 1]` by continuity. -/
private theorem le_on_Icc_of_le_on_Ioo (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ)
    (h : ∀ ω ∈ Set.Ioo (0 : ℝ) 1, c ≤ f ω) : ∀ ω ∈ Set.Icc (0 : ℝ) 1, c ≤ f ω := by
  have hclosed : IsClosed {ω : ℝ | c ≤ f ω} := isClosed_le continuous_const hf
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {ω | c ≤ f ω} := fun ω hω => h ω hω
  have := closure_mono hsub
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hclosed.closure_eq] at this
  exact fun ω hω => this hω

private theorem ge_on_Icc_of_ge_on_Ioo (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ)
    (h : ∀ ω ∈ Set.Ioo (0 : ℝ) 1, f ω ≤ c) : ∀ ω ∈ Set.Icc (0 : ℝ) 1, f ω ≤ c := by
  have hclosed : IsClosed {ω : ℝ | f ω ≤ c} := isClosed_le hf continuous_const
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {ω | f ω ≤ c} := fun ω hω => h ω hω
  have := closure_mono hsub
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hclosed.closure_eq] at this
  exact fun ω hω => this hω

/-- Positive mass of a nonzero coefficient vector. -/
theorem sum_normSq_pos_of_ne_zero {N : ℕ} {z : Fin (2 * N + 1) → ℂ} (hz : z ≠ 0) :
    0 < ∑ i, Complex.normSq (z i) := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

/-- **M70 negative excursion (Step 108):** every nonzero zero-sum `z` has an
interior source coordinate with `Re e_{Dz}(ω) < -‖z‖² / π²`. -/
theorem exists_sourceEnergyRe_lt_neg_of_zeroSum (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hz : z ≠ 0) (hsum : ∑ i, z i = 0) :
    ∃ ω ∈ Set.Ioo (0 : ℝ) 1,
      sourceEnergyRe N (indexMatrix N *ᵥ z) ω < -(∑ i, Complex.normSq (z i)) / Real.pi ^ 2 := by
  set f := sourceEnergyRe N (indexMatrix N *ᵥ z)
  set c := ∑ i, Complex.normSq (z i)
  have hc : 0 < c := sum_normSq_pos_of_ne_zero hz
  have hf : Continuous f := continuous_sourceEnergyRe N _
  have hpi : 0 < Real.pi ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  have hlow := le_on_Icc_of_le_on_Ioo f hf _ hcon
  set φ : ℝ → ℝ := fun ω => (1 - ω) * (f ω + c / Real.pi ^ 2)
  have hφc : Continuous φ := by fun_prop
  have hint : ∫ ω in (0 : ℝ)..1, φ ω = 0 := by
    have hsplit : φ = fun ω => (1 - ω) * f ω + (c / Real.pi ^ 2) * (1 - ω) := by
      funext ω; simp only [φ]; ring
    rw [hsplit, intervalIntegral.integral_add
        ((by fun_prop : Continuous fun ω : ℝ => (1 - ω) * f ω).intervalIntegrable 0 1)
        ((by fun_prop : Continuous fun ω : ℝ => (c / Real.pi ^ 2) * (1 - ω)).intervalIntegrable
          0 1),
      integral_one_sub_mul_sourceEnergyRe_indexAction N z hsum,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        intervalIntegrable_const intervalIntegral.intervalIntegrable_id, integral_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  obtain ⟨η, hη, hη1, hnear⟩ :=
    exists_Ioo_gt_of_continuous_zero f hf (sourceEnergyRe_zero N _)
      (ε := c / Real.pi ^ 2) (by positivity)
  have hpos : 0 < ∫ ω in (0 : ℝ)..1, φ ω := by
    apply integral_pos_of_pos_near_zero φ hφc hη hη1
    · intro x hx
      have h1 : 0 < 1 - x := by linarith [hx.2, hη1]
      have h2 := (hnear x hx).1
      exact mul_pos h1 (by linarith)
    · intro x hx
      have h1 : 0 ≤ 1 - x := by linarith [hx.2]
      have h2 := hlow x ⟨by linarith [hx.1], hx.2⟩
      exact mul_nonneg h1 (by
        have : -(c / Real.pi ^ 2) ≤ f x := by
          have heq : -c / Real.pi ^ 2 = -(c / Real.pi ^ 2) := by ring
          linarith [heq ▸ h2]
        linarith)
  linarith

/-- **M70 positive excursion (Step 108):** every nonzero zero-sum `z` has an
interior source coordinate with `Re e_{Dz}(ω) > ‖z‖² / π²`. -/
theorem exists_sourceEnergyRe_gt_of_zeroSum (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hz : z ≠ 0) (hsum : ∑ i, z i = 0) :
    ∃ ω ∈ Set.Ioo (0 : ℝ) 1,
      (∑ i, Complex.normSq (z i)) / Real.pi ^ 2 < sourceEnergyRe N (indexMatrix N *ᵥ z) ω := by
  set f := sourceEnergyRe N (indexMatrix N *ᵥ z)
  set c := ∑ i, Complex.normSq (z i)
  have hc : 0 < c := sum_normSq_pos_of_ne_zero hz
  have hf : Continuous f := continuous_sourceEnergyRe N _
  have hpi : 0 < Real.pi ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  have hup := ge_on_Icc_of_ge_on_Ioo f hf _ hcon
  set φ : ℝ → ℝ := fun ω => ω * (c / Real.pi ^ 2 - f ω)
  have hφc : Continuous φ := by fun_prop
  have hint : ∫ ω in (0 : ℝ)..1, φ ω = 0 := by
    have hsplit : φ = fun ω => (c / Real.pi ^ 2) * ω - ω * f ω := by
      funext ω; simp only [φ]; ring
    rw [hsplit, intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun ω : ℝ => (c / Real.pi ^ 2) * ω).intervalIntegrable 0 1)
        ((by fun_prop : Continuous fun ω : ℝ => ω * f ω).intervalIntegrable 0 1),
      integral_mul_sourceEnergyRe_indexAction N z hsum,
      intervalIntegral.integral_const_mul, integral_id]
    field_simp
    ring
  obtain ⟨η, hη, hη1, hnear⟩ :=
    exists_Ioo_gt_of_continuous_zero f hf (sourceEnergyRe_zero N _)
      (ε := c / Real.pi ^ 2) (by positivity)
  have hpos : 0 < ∫ ω in (0 : ℝ)..1, φ ω := by
    apply integral_pos_of_pos_near_zero φ hφc hη hη1
    · intro x hx
      have h2 := (hnear x hx).2
      exact mul_pos hx.1 (by linarith)
    · intro x hx
      have h1 : 0 ≤ x := by linarith [hx.1]
      have h2 := hup x ⟨h1, hx.2⟩
      exact mul_nonneg h1 (by linarith)
  linarith

/-- **M70 (Step 108) combined:** both strict excursions. -/
theorem sourceEnergyRe_excursions_of_zeroSum (N : ℕ) (z : Fin (2 * N + 1) → ℂ)
    (hz : z ≠ 0) (hsum : ∑ i, z i = 0) :
    (∃ ω ∈ Set.Ioo (0 : ℝ) 1,
      (∑ i, Complex.normSq (z i)) / Real.pi ^ 2 < sourceEnergyRe N (indexMatrix N *ᵥ z) ω) ∧
    ∃ ω ∈ Set.Ioo (0 : ℝ) 1,
      sourceEnergyRe N (indexMatrix N *ᵥ z) ω < -(∑ i, Complex.normSq (z i)) / Real.pi ^ 2 :=
  ⟨exists_sourceEnergyRe_gt_of_zeroSum N z hz hsum,
    exists_sourceEnergyRe_lt_neg_of_zeroSum N z hz hsum⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.integral_sourceEnergyRe_indexAction
#print axioms Zeta23.CCM.integral_mul_sourceEnergyRe_indexAction
#print axioms Zeta23.CCM.exists_sourceEnergyRe_lt_neg_of_zeroSum
#print axioms Zeta23.CCM.exists_sourceEnergyRe_gt_of_zeroSum
#print axioms Zeta23.CCM.sourceEnergyRe_excursions_of_zeroSum
