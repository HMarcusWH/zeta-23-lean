import Zeta23.OPICAFollowup.ZeroProfiles
import Zeta23.OPICAFollowup.LogFourierSobolev

/-!
The forced Euler equation of the actual zero profiles (R2-S1b). For an actual zero ζ(ρ) = 0 with
0 < Re ρ < 1 and h = `zeroProfile` ρ, on (0, ∞) in distributions,

  -(x² h')' = κ (h - 1 + Σ_{n ≥ 1} δ_n),  κ = ρ(1 - ρ).

- Distributions are tested on smooth compactly supported functions on (0, ∞)
  (`PositiveAxisTest`). The Euler image `eulerImage` uses the distributional derivative of h:
  ⟨-(x² h')', φ⟩ = ⟨x² h', φ'⟩ = -∫ h (x² φ')'. The explicit a.e. derivative
  `zeroProfileDeriv` (the cell derivative of the exact finite sums) gives the same value.
- Each cell branch x^(-ρ) A_n - x^(ρ-1) B_n solves (x² g')' + κ g = 0. Integration by parts on
  the cells telescopes: h is continuous, so no derivative of a delta appears, and the jump
  n² (h'(n+) - h'(n-)) = -κ of x² h' produces the atom κ δ_n.
- The atoms are nonzero, so the Euler image is not a function, in particular not in L²: h is not
  in the operator domain of the L² self-adjoint realization of -∂(x² ∂) and satisfies no
  homogeneous eigenvalue equation. The positive form identity (S1.5) of `LogFourierSobolev`
  holds for h with its explicit derivative.
-/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ContDiff

namespace Zeta23.OPICAFollowup

section CellEuler

/-- x² S'_cell = -ρ x^(1-ρ) A_n - (ρ-1) x^ρ B_n on (0, ∞). -/
lemma sq_mul_srhoCellDeriv (ρ : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 2 * srhoCellDeriv ρ n x =
      -ρ * (x : ℂ) ^ (1 - ρ) * cellSumA ρ n - (ρ - 1) * (x : ℂ) ^ ρ * cellSumB ρ n := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have e1 : (x : ℂ) ^ 2 * (x : ℂ) ^ (-ρ - 1) = (x : ℂ) ^ (1 - ρ) := by
    rw [show (1 - ρ) = (2 : ℂ) + (-ρ - 1) by ring, Complex.cpow_add _ _ hxne]; norm_cast
  have e2 : (x : ℂ) ^ 2 * (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ := by
    rw [show ρ = (2 : ℂ) + (ρ - 1 - 1) by ring, Complex.cpow_add _ _ hxne]
    · norm_cast; ring_nf
  unfold srhoCellDeriv
  linear_combination (-ρ * cellSumA ρ n) * e1 - ((ρ - 1) * cellSumB ρ n) * e2

/-- The Euler equation of every cell branch: (x² S'_cell)' = -κ S_cell on (0, ∞). -/
lemma hasDerivAt_sq_mul_srhoCellDeriv (ρ : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * srhoCellDeriv ρ n y)
      (-spectralKappa ρ * srhoCell ρ n x) x := by
  have h1 := (hasDerivAt_cpow_neg (ρ - 1) hx).const_mul (-ρ * cellSumA ρ n)
  have h2 := (hasDerivAt_cpow_neg (-ρ) hx).const_mul (-(ρ - 1) * cellSumB ρ n)
  have hsum := h1.add h2
  refine (hsum.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold srhoCell spectralKappa
    have e1 : -(ρ - 1) - 1 = -ρ := by ring
    have e2 : -(-ρ) - 1 = ρ - 1 := by ring
    rw [e1, e2]; ring
  · filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [sq_mul_srhoCellDeriv ρ n hy]
    simp only [neg_sub, neg_neg, Pi.add_apply]
    ring

end CellEuler

section CellParts

/-- On the closed cell [n, n+1] the profile is the smooth branch (S_ρ is continuous at n+1). -/
lemma zeroProfile_eq_cell_closed (ρ : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Icc (n : ℝ) (n + 1)) :
    zeroProfile ρ x = 1 - srhoCell ρ n x / normalizationBrho ρ := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg n) hx.1
  rw [zeroProfile, abs_of_nonneg hx0]
  rcases lt_or_eq_of_le hx.2 with h | h
  · rw [finiteSumSrho_eq_cell ρ ⟨hx.1, h⟩]
  · have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h, ← hc, finiteSumSrho_eq_cell ρ (n := n + 1) ⟨le_rfl, by push_cast; linarith⟩, srhoCell_succ_eq]

lemma srhoCell_zero (ρ : ℂ) (y : ℝ) : srhoCell ρ 0 y = 0 := by
  simp [srhoCell, cellSumA, cellSumB]

/-- Integration by parts on one cell [n, n+1] (n ≥ 1) against a C¹ test function. -/
lemma cell_parts (ρ : ℂ) {n : ℕ} (hn : 1 ≤ n) {φ φ' : ℝ → ℂ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ') :
    ∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * srhoCellDeriv ρ n x * φ' x =
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ 2 * srhoCellDeriv ρ n ((n : ℝ) + 1) * φ ((n : ℝ) + 1) -
        ((n : ℝ) : ℂ) ^ 2 * srhoCellDeriv ρ n n * φ n) +
      spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), srhoCell ρ n x * φ x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx; rw [uIcc_of_le (by linarith)] at hx; linarith [hx.1]
  have hu : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * srhoCellDeriv ρ n y)
      (-spectralKappa ρ * srhoCell ρ n x) x := fun x hx => hasDerivAt_sq_mul_srhoCellDeriv ρ n (hpos x hx)
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt φ (φ' x) x := fun x _ => hφ x
  have hcellc : ContinuousOn (fun x => -spectralKappa ρ * srhoCell ρ n x) (uIcc (n : ℝ) (n + 1)) :=
    fun x hx => ((hasDerivAt_srhoCell ρ n (hpos x hx)).continuousAt.const_mul _).continuousWithinAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcellc.intervalIntegrable) (hφ'.intervalIntegrable _ _)
  have e1 : (∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * srhoCellDeriv ρ n x * φ' x) =
      ∫ x in (n : ℝ)..(n + 1), ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x) * φ' x := rfl
  rw [e1, hparts]
  have e2 : (∫ x in (n : ℝ)..(n + 1), -spectralKappa ρ * srhoCell ρ n x * φ x) =
      -spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), srhoCell ρ n x * φ x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [e2]; push_cast; ring

end CellParts

section Derivative

/-- The explicit derivative of the zero profile on (0, ∞): the cell derivative of the cell
containing x (the right derivative at integers). -/
def zeroProfileDeriv (ρ : ℂ) (x : ℝ) : ℂ := -(srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ)

lemma measurable_zeroProfileDeriv (ρ : ℂ) : Measurable (zeroProfileDeriv ρ) := by
  have hA : Measurable (fun x : ℝ => cellSumA ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumA ρ)).comp Nat.measurable_floor
  have hB : Measurable (fun x : ℝ => cellSumB ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumB ρ)).comp Nat.measurable_floor
  unfold zeroProfileDeriv srhoCellDeriv
  have h1 : Measurable (fun x : ℝ => (x : ℂ) ^ (-ρ - 1)) := Complex.measurable_ofReal.pow_const _
  have h2 : Measurable (fun x : ℝ => (x : ℂ) ^ (ρ - 1 - 1)) := Complex.measurable_ofReal.pow_const _
  exact (((measurable_const.mul h1).mul hA).sub ((measurable_const.mul h2).mul hB)).div_const _ |>.neg

lemma zeroProfileDeriv_eq_cell (ρ : ℂ) {n : ℕ} {x : ℝ} (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    zeroProfileDeriv ρ x = -(srhoCellDeriv ρ n x / normalizationBrho ρ) := by
  rw [zeroProfileDeriv, natFloor_eq_of_mem_cell hx]

lemma deriv_zeroProfile_eq {ρ : ℂ} {x : ℝ} (hx : 0 < x) (hn : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    deriv (zeroProfile ρ) x = zeroProfileDeriv ρ x := by
  have hcell := mem_cell_of_not_nat hx hn
  rw [(hasDerivAt_zeroProfile_cell ρ hcell).deriv, zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hcell)]

lemma hasDerivWithinAt_zeroProfile_Ioi (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (zeroProfile ρ) (zeroProfileDeriv ρ x) (Ioi x) x := by
  by_cases hn : x ∈ Set.range (fun n : ℕ => (n : ℝ))
  · obtain ⟨m, rfl⟩ := hn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hx
      · exact h
    have h := hasDerivWithinAt_zeroProfile_right ρ hm
    rw [zeroProfileDeriv, Nat.floor_natCast]
    exact h.mono Ioi_subset_Ici_self
  · have hcell := mem_cell_of_not_nat hx hn
    rw [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hcell)]
    exact (hasDerivAt_zeroProfile_cell ρ hcell).hasDerivWithinAt

/-- The ordinary part of the forced Euler equation: (x² h')' = κ (1 - h) between integers. -/
lemma hasDerivAt_sq_mul_deriv_zeroProfile (ρ : ℂ) {x : ℝ} (hx : 0 < x)
    (hn : x ∉ Set.range (fun n : ℕ => (n : ℝ))) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * deriv (zeroProfile ρ) y)
      (spectralKappa ρ * (1 - zeroProfile ρ x)) x := by
  have hcell := mem_cell_of_not_nat hx hn
  set n := ⌊x⌋₊
  have h := (hasDerivAt_sq_mul_srhoCellDeriv ρ n hx).div_const (normalizationBrho ρ) |>.neg
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [zeroProfile_eq_cell_closed ρ (Ioo_subset_Icc_self hcell)]; ring
  · filter_upwards [Ioo_mem_nhds hcell.1 hcell.2] with y hy
    rw [(hasDerivAt_zeroProfile_cell ρ hy).deriv]; simp only [Pi.neg_apply]; ring

end Derivative

section Telescoping

lemma intervalIntegral_congr_Ioo {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

lemma intervalIntegrable_congr_Ioo {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b))
    (hg : IntervalIntegrable g volume a b) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hg ⊢
  exact hg.congr_fun h.symm measurableSet_Ioo

/-- The smooth branch of h on the closed cell [n, n+1] and its derivative. -/
lemma hasDerivAt_zeroProfile_branch (ρ : ℂ) (n : ℕ) {y : ℝ} (hy : (n : ℝ) ≤ y) :
    HasDerivAt (fun z : ℝ => 1 - srhoCell ρ n z / normalizationBrho ρ)
      (-(srhoCellDeriv ρ n y / normalizationBrho ρ)) y := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [srhoCell_zero, srhoCellDeriv_zero, zero_div, sub_zero, neg_zero]
    exact hasDerivAt_const _ _
  · have hy0 : 0 < y := lt_of_lt_of_le (by exact_mod_cast hn) hy
    exact ((hasDerivAt_srhoCell ρ n hy0).div_const _).const_sub 1

/-- Integration by parts of h against ψ' on one cell [n, n+1]. -/
lemma cell_parts_profile (ρ : ℂ) (n : ℕ) {ψ ψ' : ℝ → ℂ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ' : Continuous ψ') :
    IntervalIntegrable (fun x => zeroProfileDeriv ρ x * ψ x) volume n (n + 1) ∧
    ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x * ψ' x =
      zeroProfile ρ ((n : ℝ) + 1) * ψ ((n : ℝ) + 1) - zeroProfile ρ n * ψ n -
        ∫ x in (n : ℝ)..(n + 1), zeroProfileDeriv ρ x * ψ x := by
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hmem : ∀ x ∈ uIcc (n : ℝ) (n + 1), x ∈ Icc (n : ℝ) (n + 1) := fun x hx => by
    rwa [uIcc_of_le hle] at hx
  have hu : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (fun z : ℝ => 1 - srhoCell ρ n z / normalizationBrho ρ)
      (-(srhoCellDeriv ρ n x / normalizationBrho ρ)) x :=
    fun x hx => hasDerivAt_zeroProfile_branch ρ n (hmem x hx).1
  have hcont : ContinuousOn (fun x => -(srhoCellDeriv ρ n x / normalizationBrho ρ)) (uIcc (n : ℝ) (n + 1)) := by
    intro x hx
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [srhoCellDeriv_zero, zero_div, neg_zero]; exact continuousWithinAt_const
    · have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hn) (hmem x hx).1
      have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-ρ - 1)) x :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
      have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (ρ - 1 - 1)) x :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
      unfold srhoCellDeriv
      exact ((((continuousAt_const.mul h1).mul continuousAt_const).sub
        ((continuousAt_const.mul h2).mul continuousAt_const)).div_const _).neg.continuousWithinAt
  have hII : IntervalIntegrable (fun x => -(srhoCellDeriv ρ n x / normalizationBrho ρ)) volume n (n + 1) :=
    hcont.intervalIntegrable
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun x _ => hψ x) hII
    (hψ'.intervalIntegrable _ _)
  have heqIoo : EqOn (fun x => zeroProfileDeriv ρ x * ψ x)
      (fun x => -(srhoCellDeriv ρ n x / normalizationBrho ρ) * ψ x) (Ioo (n : ℝ) (n + 1)) :=
    fun x hx => by simp only [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hx)]
  have hcontψ : ContinuousOn ψ (uIcc (n : ℝ) (n + 1)) :=
    fun x _ => (hψ x).continuousAt.continuousWithinAt
  refine ⟨intervalIntegrable_congr_Ioo hle heqIoo ((hcont.mul hcontψ).intervalIntegrable), ?_⟩
  have e1 : (∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x * ψ' x) =
      ∫ x in (n : ℝ)..(n + 1), (1 - srhoCell ρ n x / normalizationBrho ρ) * ψ' x :=
    intervalIntegral.integral_congr fun x hx => by
      simp only [zeroProfile_eq_cell_closed ρ (hmem x hx)]
  rw [e1, hparts, intervalIntegral_congr_Ioo hle heqIoo,
    zeroProfile_eq_cell_closed ρ (n := n) ⟨le_refl _, hle⟩,
    zeroProfile_eq_cell_closed ρ (n := n) ⟨hle, le_refl _⟩]

/-- Telescoped distributional integration by parts of h on [0, N+1]. -/
lemma profile_parts (ρ : ℂ) {ψ ψ' : ℝ → ℂ} (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ' : Continuous ψ') (N : ℕ) :
    IntervalIntegrable (fun x => zeroProfileDeriv ρ x * ψ x) volume 0 ((N : ℝ) + 1) ∧
    ∫ x in (0 : ℝ)..((N : ℝ) + 1), zeroProfile ρ x * ψ' x =
      zeroProfile ρ ((N : ℝ) + 1) * ψ ((N : ℝ) + 1) - zeroProfile ρ 0 * ψ 0 -
        ∫ x in (0 : ℝ)..((N : ℝ) + 1), zeroProfileDeriv ρ x * ψ x := by
  induction N with
  | zero => simpa using cell_parts_profile ρ 0 hψ hψ'
  | succ N ih =>
    obtain ⟨hI, hE⟩ := ih
    obtain ⟨hI1, hE1⟩ := cell_parts_profile ρ (N + 1) hψ hψ'
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hc] at hI1 hE1
    have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + 1 := by push_cast; ring
    rw [hc2]
    have hcontψ' : ∀ a b : ℝ, IntervalIntegrable ψ' volume a b := fun a b => hψ'.intervalIntegrable a b
    have hhψ : ∀ a b : ℝ, IntervalIntegrable (fun x => zeroProfile ρ x * ψ' x) volume a b :=
      fun a b => ((continuous_zeroProfile ρ).mul hψ').intervalIntegrable a b
    refine ⟨hI.trans hI1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hhψ _ _) (hhψ _ _),
      ← intervalIntegral.integral_add_adjacent_intervals hI hI1, hE, hE1]
    ring

end Telescoping

section EulerTelescoping

lemma continuousOn_srhoCellDeriv (ρ : ℂ) (n : ℕ) : ContinuousOn (srhoCellDeriv ρ n) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-ρ - 1)) x :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
  have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (ρ - 1 - 1)) x :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne')
  unfold srhoCellDeriv
  exact (((continuousAt_const.mul h1).mul continuousAt_const).sub
    ((continuousAt_const.mul h2).mul continuousAt_const)).continuousWithinAt

/-- One cell [n, n+1], n ≥ 1, of ∫ x² h' v'. -/
lemma euler_cell (ρ : ℂ) {n : ℕ} (hn : 1 ≤ n) {v v' : ℝ → ℂ} (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : Continuous v') :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x) volume n (n + 1) ∧
    ∫ x in (n : ℝ)..(n + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x =
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ n ((n : ℝ) + 1) / normalizationBrho ρ) *
          v ((n : ℝ) + 1) -
        ((n : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ n n / normalizationBrho ρ) * v n) +
      spectralKappa ρ * ∫ x in (n : ℝ)..(n + 1), (zeroProfile ρ x - 1) * v x := by
  have hle : (n : ℝ) ≤ n + 1 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ x ∈ uIcc (n : ℝ) (n + 1), x ∈ Icc (n : ℝ) (n + 1) := fun x hx => by
    rwa [uIcc_of_le hle] at hx
  have heqIoo : EqOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x)
      (fun x : ℝ => -(1 / normalizationBrho ρ) * ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x * v' x))
      (Ioo (n : ℝ) (n + 1)) := fun x hx => by
    simp only [zeroProfileDeriv_eq_cell ρ (Ioo_subset_Ico_self hx)]; ring
  have hcont : ContinuousOn (fun x : ℝ => -(1 / normalizationBrho ρ) * ((x : ℂ) ^ 2 * srhoCellDeriv ρ n x * v' x))
      (uIcc (n : ℝ) (n + 1)) := by
    refine continuousOn_const.mul ((((Complex.continuous_ofReal.pow 2).continuousOn).mul ?_).mul
      hv'.continuousOn)
    exact (continuousOn_srhoCellDeriv ρ n).mono fun x hx => lt_of_lt_of_le hn0 (hmem x hx).1
  refine ⟨intervalIntegrable_congr_Ioo hle heqIoo hcont.intervalIntegrable, ?_⟩
  have hparts := cell_parts ρ hn hv hv'
  have e2 : (∫ x in (n : ℝ)..(n + 1), (zeroProfile ρ x - 1) * v x) =
      ∫ x in (n : ℝ)..(n + 1), -(1 / normalizationBrho ρ) * (srhoCell ρ n x * v x) :=
    intervalIntegral.integral_congr fun x hx => by
      simp only [zeroProfile_eq_cell_closed ρ (hmem x hx)]; ring
  rw [intervalIntegral_congr_Ioo hle heqIoo, intervalIntegral.integral_const_mul, hparts, e2,
    intervalIntegral.integral_const_mul]
  ring

/-- Telescoped ∫_0^(N+1) x² h' v' with the integer atoms and the boundary term at N+1. -/
lemma euler_parts {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) {v v' : ℝ → ℂ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x) volume 0 ((N : ℝ) + 1) ∧
    ∫ x in (0 : ℝ)..((N : ℝ) + 1), (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x =
      spectralKappa ρ * ((∫ x in (0 : ℝ)..((N : ℝ) + 1), (zeroProfile ρ x - 1) * v x) +
        ∑ m ∈ Finset.range N, v (m + 1)) +
      (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv ρ N ((N : ℝ) + 1) / normalizationBrho ρ) *
        v ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    have hz : EqOn (fun x : ℝ => (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * v' x) (fun _ => (0 : ℂ))
        (Ioo (0 : ℝ) 1) := fun x hx => by
      have hx' : x ∈ Ico ((0 : ℕ) : ℝ) ((0 : ℕ) + 1) := by simpa using Ioo_subset_Ico_self hx
      simp only [zeroProfileDeriv_eq_cell ρ hx', srhoCellDeriv_zero, zero_div, neg_zero, mul_zero,
        zero_mul]
    have hone : (∫ x in (0 : ℝ)..1, (zeroProfile ρ x - 1) * v x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun x hx => ?_]
      · simp
      · rw [uIcc_of_le zero_le_one] at hx
        simp only [zeroProfile_eq_one ρ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩), sub_self, zero_mul]
    simp only [CharP.cast_eq_zero, zero_add, Finset.range_zero, Finset.sum_empty, add_zero,
      srhoCellDeriv_zero, zero_div, neg_zero, mul_zero, zero_mul]
    refine ⟨intervalIntegrable_congr_Ioo zero_le_one hz intervalIntegrable_const, ?_⟩
    rw [intervalIntegral_congr_Ioo zero_le_one hz, hone]; simp
  | succ N ih =>
    obtain ⟨hI, hE⟩ := ih
    obtain ⟨hI1, hE1⟩ := euler_cell ρ (n := N + 1) (by omega) hv hv'
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hc] at hI1 hE1
    have hc2 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + 1 := by push_cast; ring
    rw [hc2]
    have hhv : ∀ a b : ℝ, IntervalIntegrable (fun x => (zeroProfile ρ x - 1) * v x) volume a b :=
      fun a b => (((continuous_zeroProfile ρ).sub continuous_const).mul
        (continuous_iff_continuousAt.mpr fun x => (hv x).continuousAt)).intervalIntegrable a b
    refine ⟨hI.trans hI1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hI hI1, hE, hE1,
      ← intervalIntegral.integral_add_adjacent_intervals (hhv 0 ((N : ℝ) + 1)) (hhv ((N : ℝ) + 1) ((N : ℝ) + 1 + 1)),
      Finset.sum_range_succ]
    have hj := zeroProfile_deriv_jump h0 h1 hh N
    have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have hj' : ((N + 1 : ℕ) : ℂ) ^ 2 * (-(srhoCellDeriv ρ (N + 1) (N + 1 : ℕ) / normalizationBrho ρ) -
        -(srhoCellDeriv ρ N (N + 1 : ℕ) / normalizationBrho ρ)) = -spectralKappa ρ := by
      rw [hj]; field_simp
    have hcast : (((N : ℝ) + 1 : ℝ) : ℂ) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    have hcastR : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, hcastR] at *
    simp only [Nat.cast_add, Nat.cast_one] at hj'
    push_cast at *
    linear_combination (-(v ((N : ℝ) + 1))) * hj'

end EulerTelescoping

section Distribution

/-- Smooth compactly supported test functions on the positive axis. -/
def PositiveAxisTest (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0

/-- The distribution -(x² h')' on (0, ∞), with h' the distributional derivative of h:
φ ↦ ⟨x² h', φ'⟩ = -∫ h (x² φ')'. -/
def eulerImage (ρ : ℂ) (φ : ℝ → ℂ) : ℂ :=
  -∫ x in Ioi 0, zeroProfile ρ x * deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv φ y) x

lemma PositiveAxisTest.eventually_zero {φ : ℝ → ℂ} (hφ : PositiveAxisTest φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, M < x → φ =ᶠ[𝓝 x] 0 := by
  obtain ⟨M, hM⟩ := hφ.2.1.isCompact.bddAbove
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport fun h =>
    absurd (hM h) (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hy))

lemma setIntegral_Ioi_eq_intervalIntegral {F : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ x, c < x → F x = 0) : ∫ x in Ioi 0, F x = ∫ x in (0 : ℝ)..c, F x := by
  rw [intervalIntegral.integral_of_le hc]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun x hx => hF x (not_le.mp fun h => hx.2 ⟨hx.1, h⟩)

/-- The forced Euler identity against every positive-axis test function, for b_ρ ≠ 0. -/
theorem forced_euler_identity {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2)
    {φ : ℝ → ℂ} (hφ : PositiveAxisTest φ) :
    eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
        ∑' n : ℕ, φ (n + 1)) ∧
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * deriv φ x) = eulerImage ρ φ := by
  obtain ⟨M, hM0, hMz⟩ := hφ.eventually_zero
  have h1le : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.1.differentiable (by simp)).differentiableAt).hasDerivAt
  have hdc : ContDiff ℝ ∞ (deriv φ) := by simpa using hφ.1.iterate_deriv 1
  set ψ : ℝ → ℂ := fun y => (y : ℂ) ^ 2 * deriv φ y with hψdef
  have hψc : ContDiff ℝ ∞ ψ := by
    have : ContDiff ℝ ∞ (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
    exact (this.pow 2).mul hdc
  have hψd : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψc.differentiable (by simp)).differentiableAt).hasDerivAt
  have hψ' : Continuous (deriv ψ) := hψc.continuous_deriv (by simp)
  have hφ' : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  have hφ0 : ∀ x, M < x → φ x = 0 := fun x hx => (hMz x hx).self_of_nhds
  have hdφ0 : ∀ x, M < x → deriv φ x = 0 := fun x hx => by
    rw [(hMz x hx).deriv_eq]; simp
  have hψ0 : ∀ x, M < x → ψ =ᶠ[𝓝 x] 0 := fun x hx => by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [hψdef, hdφ0 y hy]
  have hdψ0 : ∀ x, M < x → deriv ψ x = 0 := fun x hx => by
    rw [(hψ0 x hx).deriv_eq]; simp
  set N := ⌈M⌉₊
  set c : ℝ := (N : ℝ) + 1 with hcdef
  have hc : M < c := lt_of_le_of_lt (Nat.le_ceil M) (lt_add_one _)
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨-, hP⟩ := profile_parts ρ hψd hψ' N
  obtain ⟨-, hE⟩ := euler_parts h0 h1 hh hd hφ' N
  have hA : eulerImage ρ φ = ∫ x in (0 : ℝ)..c, (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * deriv φ x := by
    rw [eulerImage, ← hψdef, setIntegral_Ioi_eq_intervalIntegral hc0
      (fun x hx => by simp only [hdψ0 x (lt_trans hc hx), mul_zero]), hP,
      (hψ0 c hc).self_of_nhds]
    simp only [Pi.zero_apply, mul_zero, hψdef, Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, sub_zero, zero_sub, neg_neg]
    exact intervalIntegral.integral_congr fun x _ => by ring
  refine ⟨?_, ?_⟩
  · rw [hA, hE, hφ0 c hc, mul_zero, add_zero,
      setIntegral_Ioi_eq_intervalIntegral hc0 (fun x hx => by simp only [hφ0 x (lt_trans hc hx),
        mul_zero])]
    congr 2
    refine (tsum_eq_sum (s := Finset.range N) fun n hn => hφ0 _ ?_).symm
    have : (N : ℝ) ≤ n := by exact_mod_cast not_lt.mp (Finset.mem_range.not.mp hn)
    linarith
  · rw [hA, ← setIntegral_Ioi_eq_intervalIntegral hc0 (fun x hx => by
      simp only [hdφ0 x (lt_trans hc hx), mul_zero])]
    have hnull : (volume : Measure ℝ) (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
      (Set.countable_range _).measure_zero _
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hx0
    rw [deriv_zeroProfile_eq hx0 hx]

end Distribution

section Atoms

/-- Shrinking bumps at 1: radius 1/(2(k+1)). -/
def atomBump (k : ℕ) : ContDiffBump (1 : ℝ) where
  rIn := 1 / (4 * (k + 1))
  rOut := 1 / (2 * (k + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt (by positivity); nlinarith

lemma atomBump_rOut_le (k : ℕ) : (atomBump k).rOut ≤ 1 / 2 := by
  change 1 / (2 * ((k : ℝ) + 1)) ≤ 1 / 2
  apply one_div_le_one_div_of_le (by norm_num); nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma tsupport_atomBump_subset (k : ℕ) :
    tsupport (fun x => ((atomBump k x : ℝ) : ℂ)) ⊆ Icc (1 / 2) (3 / 2) := by
  refine (tsupport_comp_subset Complex.ofReal_zero (atomBump k)).trans ?_
  rw [(atomBump k).tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have := atomBump_rOut_le k
  constructor <;> linarith [hx.1, hx.2]

lemma positiveAxisTest_atomBump (k : ℕ) : PositiveAxisTest (fun x => ((atomBump k x : ℝ) : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp (atomBump k).contDiff,
    (atomBump k).hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  exact (tsupport_atomBump_subset k).trans fun x hx => lt_of_lt_of_le (by norm_num) hx.1

lemma atomBump_eq_zero_of_notMem {k : ℕ} {x : ℝ} (hx : x ∉ Icc (1 / 2 : ℝ) (3 / 2)) :
    ((atomBump k x : ℝ) : ℂ) = 0 :=
  image_eq_zero_of_notMem_tsupport (f := fun x => ((atomBump k x : ℝ) : ℂ))
    fun h => hx (tsupport_atomBump_subset k h)

lemma tsum_atomBump (k : ℕ) : ∑' n : ℕ, ((atomBump k ((n : ℝ) + 1) : ℝ) : ℂ) = 1 := by
  rw [tsum_eq_single 0 fun n hn => ?_]
  · simp [(atomBump k).one_of_mem_closedBall (Metric.mem_closedBall_self (atomBump k).rIn_pos.le)]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    refine atomBump_eq_zero_of_notMem fun h => ?_
    linarith [h.2]

/-- An atom at 1 has no integrable density near 1: if κ = ∫ f φ_k for all the shrinking bumps
φ_k (with φ_k(1) = 1), then κ = 0. -/
lemma atom_not_integrable {f : ℝ → ℂ} {κ : ℂ} (hf : IntegrableOn f (Icc (1 / 2) (3 / 2)))
    (h : ∀ k : ℕ, κ = ∫ x in Icc (1 / 2 : ℝ) (3 / 2), f x * ((atomBump k x : ℝ) : ℂ)) : κ = 0 := by
  have hlim : Tendsto (fun k : ℕ => ∫ x in Icc (1 / 2 : ℝ) (3 / 2), f x * ((atomBump k x : ℝ) : ℂ))
      atTop (𝓝 (∫ x in Icc (1 / 2 : ℝ) (3 / 2), (0 : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖) (fun k => ?_) hf.norm
      (fun k => ?_) ?_
    · exact hf.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (atomBump k).continuous).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atomBump k).nonneg]
      exact mul_le_of_le_one_right (norm_nonneg _) (atomBump k).le_one
    · have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
        rw [ae_iff]; simp
      filter_upwards [ae_restrict_of_ae hne] with x hx
      have hd : 0 < dist x 1 := dist_pos.mpr hx
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hd
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with k hk
      have hr : (atomBump k).rOut ≤ dist x 1 := by
        change 1 / (2 * ((k : ℝ) + 1)) ≤ dist x 1
        refine le_trans ?_ hm.le
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      rw [(atomBump k).zero_of_le_dist hr, Complex.ofReal_zero, mul_zero]
  simp only [integral_zero] at hlim
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun k => h k) hlim

/-- The Euler image is not given by any function integrable on [1/2, 3/2], for κ ≠ 0. -/
theorem eulerImage_not_function {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2)
    (hk : spectralKappa ρ ≠ 0) {g : ℝ → ℂ} (hg : IntegrableOn g (Icc (1 / 2) (3 / 2)))
    (hrep : ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) : False := by
  have hsub : Icc (1 / 2 : ℝ) (3 / 2) ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hred : ∀ (F : ℝ → ℂ) (k : ℕ), (∫ x in Ioi 0, F x * ((atomBump k x : ℝ) : ℂ)) =
      ∫ x in Icc (1 / 2 : ℝ) (3 / 2), F x * ((atomBump k x : ℝ) : ℂ) := fun F k =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub fun x hx => by
      rw [atomBump_eq_zero_of_notMem hx.2, mul_zero]
  refine hk (atom_not_integrable (f := fun x => g x - spectralKappa ρ * (zeroProfile ρ x - 1))
    ?_ fun k => ?_)
  · exact hg.sub ((continuous_const.mul ((continuous_zeroProfile ρ).sub continuous_const)).integrableOn_Icc)
  · have hT := positiveAxisTest_atomBump k
    have hE := (forced_euler_identity h0 h1 hh hT).1
    rw [hrep _ hT, tsum_atomBump, hred, hred] at hE
    have hc : ContinuousOn (fun x => ((atomBump k x : ℝ) : ℂ)) (Icc (1 / 2 : ℝ) (3 / 2)) :=
      (Complex.continuous_ofReal.comp (atomBump k).continuous).continuousOn
    have hI1 : IntegrableOn (fun x => g x * ((atomBump k x : ℝ) : ℂ)) (Icc (1 / 2 : ℝ) (3 / 2)) :=
      hg.mul_continuousOn hc isCompact_Icc
    have hI2 : IntegrableOn (fun x => spectralKappa ρ * ((zeroProfile ρ x - 1) * ((atomBump k x : ℝ) : ℂ)))
        (Icc (1 / 2 : ℝ) (3 / 2)) :=
      (continuous_const.mul (((continuous_zeroProfile ρ).sub continuous_const).mul
        (Complex.continuous_ofReal.comp (atomBump k).continuous))).integrableOn_Icc
    have hsplit : (∫ x in Icc (1 / 2 : ℝ) (3 / 2),
        (g x - spectralKappa ρ * (zeroProfile ρ x - 1)) * ((atomBump k x : ℝ) : ℂ)) =
        (∫ x in Icc (1 / 2 : ℝ) (3 / 2), g x * ((atomBump k x : ℝ) : ℂ)) -
          spectralKappa ρ * ∫ x in Icc (1 / 2 : ℝ) (3 / 2), (zeroProfile ρ x - 1) * ((atomBump k x : ℝ) : ℂ) := by
      rw [← integral_const_mul, ← integral_sub hI1 hI2]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hsplit, hE]; ring

end Atoms

section FormDomain

lemma zeroProfileDeriv_bound {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖zeroProfileDeriv ρ x‖ ≤ C * min 1 (x ^ (-2 : ℝ)) := by
  set C := (‖2 * ρ - 1‖ + srhoDerivRemainderConst ρ) / ‖normalizationBrho ρ‖
  have hC0 : 0 ≤ C := by
    have : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
    positivity
  refine ⟨C, hC0, fun x hx => ?_⟩
  rw [zeroProfileDeriv, norm_neg]
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [Nat.floor_eq_zero.mpr hx1, srhoCellDeriv_zero, zero_div, norm_zero]
    exact mul_nonneg hC0 (le_min zero_le_one (Real.rpow_nonneg hx.le _))
  · have hcell : x ∈ Ico (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1) := ⟨Nat.floor_le hx.le, Nat.lt_floor_add_one x⟩
    have hb := zeroProfile_deriv_bound hz h0 h1 hcell hx1
    have hmin : min 1 (x ^ (-2 : ℝ)) = x ^ (-2 : ℝ) :=
      min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
    rw [hmin]; exact hb

/-- At an actual zero the zero profile, with its explicit derivative, lies in the actual log form
domain. -/
theorem zeroProfile_mem_logFormDomain {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : LogFormDomain (zeroProfile ρ) (zeroProfileDeriv ρ) := by
  obtain ⟨C, hC0, hC⟩ := zeroProfileDeriv_bound hz h0 h1
  have hm := measurable_zeroProfileDeriv ρ
  have hII : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (zeroProfileDeriv ρ) volume a b := by
    intro a b ha hb
    refine (intervalIntegrable_const (c := C)).mono_fun hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : 0 < x := by
      rcases le_total a b with hab | hab
      · rw [uIoc_of_le hab] at hx; linarith [hx.1]
      · rw [uIoc_of_ge hab] at hx; linarith [hx.1]
    refine (hC x hx0).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hC0]
    exact mul_le_of_le_one_right hC0 (min_le_left _ _)
  have hFTC : ∀ a b : ℝ, 0 < a → a ≤ b →
      zeroProfile ρ b - zeroProfile ρ a = ∫ x in a..b, zeroProfileDeriv ρ x := by
    intro a b ha hab
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
      ((continuous_zeroProfile ρ).continuousOn)
      (fun x hx => hasDerivWithinAt_zeroProfile_Ioi ρ (lt_trans ha hx.1))
      (hII a b ha (lt_of_lt_of_le ha hab))]
  refine ⟨fun a b ha hb => ?_, hII, hm, (memLp_two_zeroProfile hz h0 h1).restrict _, ?_⟩
  · rcases le_total a b with hab | hab
    · exact hFTC a b ha hab
    · rw [intervalIntegral.integral_symm, ← hFTC b a hb hab]; ring
  · set g : ℝ → ℝ := fun x => C * min x (x ^ (-1 : ℝ)) with hg
    have hgL : MemLp g 2 (volume.restrict (Ioi 0)) := by
      have hgm : Measurable g := by fun_prop
      refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
      have hdom : Integrable (fun x : ℝ => C ^ 2 * (Ioc 0 1).indicator (fun _ => (1 : ℝ)) x +
          C ^ 2 * (Ioi 1).indicator (fun x => x ^ (-2 : ℝ)) x) (volume.restrict (Ioi 0)) := by
        refine Integrable.add ?_ ?_
        · refine Integrable.const_mul ?_ _
          refine ((integrable_indicator_iff measurableSet_Ioc).mpr ?_).mono_measure
            Measure.restrict_le_self
          exact integrableOn_const (by simp) (by simp)
        · refine Integrable.const_mul ?_ _
          exact ((integrable_indicator_iff measurableSet_Ioi).mpr
            (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).mono_measure Measure.restrict_le_self
      refine hdom.mono' (hgm.pow_const 2).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg, mul_pow]
      rcases le_or_gt x 1 with hx1 | hx1
      · have hmin : min x (x ^ (-1 : ℝ)) = x := by
          refine min_eq_left ?_
          rw [Real.rpow_neg_one]; exact le_trans hx1 (one_le_inv₀ hx0 |>.mpr hx1)
        rw [hmin, indicator_of_mem (show x ∈ Ioc 0 1 from ⟨hx0, hx1⟩),
          indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx1), mul_zero, add_zero, mul_one]
        exact mul_le_of_le_one_right (sq_nonneg C) (by nlinarith)
      · have hmin : min x (x ^ (-1 : ℝ)) = x ^ (-1 : ℝ) := by
          refine min_eq_right ?_
          rw [Real.rpow_neg_one]; exact le_trans (inv_le_one_of_one_le₀ hx1.le) hx1.le
        rw [hmin, indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => absurd h.2 (not_le.mpr hx1)),
          indicator_of_mem (show x ∈ Ioi 1 from hx1), mul_zero, zero_add,
          ← Real.rpow_natCast (x ^ (-1 : ℝ)) 2, ← Real.rpow_mul hx0.le]
        norm_num
    refine hgL.of_le ((Complex.measurable_ofReal.mul hm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC0 (le_min hx0.le (Real.rpow_nonneg hx0.le _)))]
    calc x * ‖zeroProfileDeriv ρ x‖ ≤ x * (C * min 1 (x ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hC x hx0) hx0.le
      _ = C * min x (x ^ (-1 : ℝ)) := by
          rw [show x * (C * min 1 (x ^ (-2 : ℝ))) = C * (min 1 (x ^ (-2 : ℝ)) * x) by ring,
            min_mul_of_nonneg _ _ hx0.le, one_mul,
            show x ^ (-2 : ℝ) * x = x ^ (-1 : ℝ) by
              rw [← Real.rpow_add_one hx0.ne']; norm_num]

end FormDomain

section Roots

/-- R2-S1b: at an actual zero 0 < Re ρ < 1, on (0, ∞) in distributions,
-(x² h')' = κ (h - 1 + Σ_{n ≥ 1} δ_n): the distributional derivative of h (tested as
-∫ h (x² φ')') and the a.e. derivative give the same Euler image; between integers
(x² h')' = κ (1 - h); at every integer n ≥ 1, h is continuous (no derivative of a delta) and the
actual jump of x² h' is n² (h'(n+) - h'(n-)) = -κ, which produces the atom κ δ_n. -/
theorem zero_profile_forced_euler (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
        ∑' n : ℕ, φ (n + 1))) ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * deriv φ x) = eulerImage ρ φ) ∧
    (∀ x : ℝ, 0 < x → x ∉ Set.range (fun n : ℕ => (n : ℝ)) →
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * deriv (zeroProfile ρ) y)
        (spectralKappa ρ * (1 - zeroProfile ρ x)) x) ∧
    (∀ n : ℕ, 1 ≤ n → ContinuousAt (zeroProfile ρ) n ∧
      ∃ dR dL : ℂ, HasDerivWithinAt (zeroProfile ρ) dR (Ici (n : ℝ)) n ∧
        HasDerivWithinAt (zeroProfile ρ) dL (Iic (n : ℝ)) n ∧
        (n : ℂ) ^ 2 * (dR - dL) = -spectralKappa ρ) := by
  have hh := zero_ne_half hz
  refine ⟨fun φ hφ => (forced_euler_identity h0 h1 hh hφ).1,
    fun φ hφ => (forced_euler_identity h0 h1 hh hφ).2,
    fun x hx hn => hasDerivAt_sq_mul_deriv_zeroProfile ρ hx hn, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨(continuous_zeroProfile ρ).continuousAt, _, _, hasDerivWithinAt_zeroProfile_right ρ hn,
    hasDerivWithinAt_zeroProfile_left ρ k, ?_⟩
  rw [zeroProfile_deriv_jump h0 h1 hh k]
  have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

/-- R2-S1b: at an actual zero the atoms κ δ_n are nonzero, so the distributional Euler image
-(x² h')' is not a function: not locally integrable on (0, ∞), in particular not in L²(0, ∞),
so h is not in the operator domain of the L² self-adjoint realization of -∂(x² ∂), and no
homogeneous eigenvalue equation -(x² h')' = c h holds. The positive form identity (S1.5) is
retained. -/
theorem zero_profile_not_homogeneous_operator_vector (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    spectralKappa ρ ≠ 0 ∧
    (¬ ∃ g : ℝ → ℂ, LocallyIntegrableOn g (Ioi 0) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) ∧
    (¬ ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioi 0)) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) ∧
    LogFormDomain (zeroProfile ρ) (zeroProfileDeriv ρ) ∧
    logForm (zeroProfileDeriv ρ) =
      (∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ x in Ioi 0, ‖zeroProfile ρ x‖ ^ 2 := by
  have hh := zero_ne_half hz
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hk : spectralKappa ρ ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  have hsub : Icc (1 / 2 : ℝ) (3 / 2) ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hD := zeroProfile_mem_logFormDomain hz h0 h1
  refine ⟨hk, fun ⟨g, hg, hrep⟩ => eulerImage_not_function h0 h1 hh hk
      (hg.integrableOn_compact_subset hsub isCompact_Icc) hrep,
    fun ⟨g, hg, hrep⟩ => eulerImage_not_function h0 h1 hh hk ?_ hrep, fun c hc => ?_, hD,
    (log_unitary_form_identity _ _ hD).2.2.2.2.1⟩
  · have hm : (volume.restrict (Ioi (0 : ℝ))).restrict (Icc (1 / 2 : ℝ) (3 / 2)) =
        volume.restrict (Icc (1 / 2 : ℝ) (3 / 2)) := by
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub]
    have h2 := hg.restrict (Icc (1 / 2 : ℝ) (3 / 2))
    rw [hm] at h2
    exact h2.integrable one_le_two
  · refine eulerImage_not_function h0 h1 hh hk (g := fun x => c * zeroProfile ρ x)
      ((continuous_const.mul (continuous_zeroProfile ρ)).integrableOn_Icc) fun φ hφ => ?_
    rw [hc φ hφ, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

end Roots

end Zeta23.OPICAFollowup
