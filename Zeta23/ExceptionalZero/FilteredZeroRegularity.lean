import Zeta23.ExceptionalZero.FilteredZeroFamily
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set Filter Topology

/-- On every compact nonnegative aperture interval, the filtered zero series is uniformly dominated
by the absolutely summable coefficient family times one fixed exponential factor. -/
theorem continuousOn_filteredZeroFamily_Icc
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) {A : ℝ} (hA : 0 ≤ A) :
    ContinuousOn (filteredZeroFamily φ c) (Set.Icc 0 A) := by
  have hcoeff : Summable (fun ρ : zetaZeroConfig.carrier => ‖zeroFilterCoeff φ ρ‖) := by
    simpa [AbsolutelySummableZeroFilter] using hφ
  have hu : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zeroFilterCoeff φ ρ‖ * Real.exp A) :=
    hcoeff.mul_right (Real.exp A)
  have hterm_cont : ∀ ρ : zetaZeroConfig.carrier,
      ContinuousOn (filteredZeroTerm φ c ρ) (Set.Icc 0 A) := by
    intro ρ
    apply Continuous.continuousOn
    unfold filteredZeroTerm
    fun_prop
  have hterm_bound : ∀ (ρ : zetaZeroConfig.carrier) (a : ℝ),
      a ∈ Set.Icc 0 A →
      ‖filteredZeroTerm φ c ρ a‖ ≤
        ‖zeroFilterCoeff φ ρ‖ * Real.exp A := by
    intro ρ a ha
    unfold filteredZeroTerm
    rw [norm_mul]
    calc
      ‖zeroFilterCoeff φ ρ‖ *
          ‖Complex.exp ((2 * ((ρ : ℂ) - c)) * (a : ℂ))‖ ≤
          ‖zeroFilterCoeff φ ρ‖ * Real.exp a :=
        mul_le_mul_of_nonneg_left
          (norm_filteredZeroExp_le hc ρ ha.1) (norm_nonneg _)
      _ ≤ ‖zeroFilterCoeff φ ρ‖ * Real.exp A :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha.2) (norm_nonneg _)
  simpa [filteredZeroFamily] using
    (continuousOn_tsum hterm_cont hu hterm_bound)

/-- The absolutely summable filtered zero family is continuous at every positive aperture.  The
proof localizes to `[0,a+1]`, where the zero series is uniformly summable. -/
theorem continuousAt_filteredZeroFamily_of_pos
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) {a : ℝ} (ha : 0 < a) :
    ContinuousAt (filteredZeroFamily φ c) a := by
  let A : ℝ := a + 1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    linarith
  have haA : a < A := by
    dsimp [A]
    linarith
  have hcont := continuousOn_filteredZeroFamily_Icc hφ hc hA0
  have hwithin : ContinuousWithinAt (filteredZeroFamily φ c) (Set.Icc 0 A) a :=
    hcont a ⟨ha.le, haA.le⟩
  have hnhds : Set.Icc 0 A ∈ 𝓝 a := by
    exact Icc_mem_nhds_iff.mpr ⟨ha, haA⟩
  exact hwithin.continuousAt hnhds

/-- The filtered zero family is continuous on the complete nonnegative aperture half-line.  At the
endpoint `a=0` we use uniform convergence on `[0,1]` and transfer the resulting within-continuity
through a neighborhood of `0` inside `[0,∞)`. -/
theorem continuousOn_filteredZeroFamily_Ici
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) :
    ContinuousOn (filteredZeroFamily φ c) (Set.Ici 0) := by
  intro a ha
  by_cases hzero : a = 0
  · subst a
    have hcompact := continuousOn_filteredZeroFamily_Icc
      (φ := φ) hφ hc (A := 1) zero_le_one
    have hwithin : ContinuousWithinAt
        (filteredZeroFamily φ c) (Set.Icc 0 1) 0 :=
      hcompact 0 ⟨le_rfl, zero_le_one⟩
    have hIio : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds (by norm_num)
    have hIioWithin : Set.Iio (1 : ℝ) ∈ 𝓝[Set.Ici 0] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds hIio
    have hIco : Set.Ico (0 : ℝ) 1 ∈ 𝓝[Set.Ici 0] (0 : ℝ) := by
      rw [← Set.Ici_inter_Iio]
      exact inter_mem self_mem_nhdsWithin hIioWithin
    have hIcc : Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici 0] (0 : ℝ) :=
      Filter.mem_of_superset hIco Set.Ico_subset_Icc_self
    exact hwithin.mono_of_mem_nhdsWithin hIcc
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    exact (continuousAt_filteredZeroFamily_of_pos hφ hc hpos).continuousWithinAt

/-- Restricting the preceding theorem gives continuity on the positive half-line. -/
theorem continuousOn_filteredZeroFamily_Ioi
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) :
    ContinuousOn (filteredZeroFamily φ c) (Set.Ioi 0) :=
  (continuousOn_filteredZeroFamily_Ici hφ hc).mono Set.Ioi_subset_Ici_self

end Zeta23.ExceptionalZero
