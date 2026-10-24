import Zeta23.OPICAFollowup.NearGapLimits

/- Independent consumers for the original R1-HT2 root
`Zeta23.OPICAFollowup.near_gap_controlled_limit_zero`.

Every predicate of the source statement (common linear variation bound, near
gap, off-lattice nonnegativity, canonical Fourier self-duality) is written out
explicitly below. The actual-domain consumer instantiates the root on the
genuine CT1 Jordan pairs at L_n = log 2/(n+2), discharging every premise from
the CT1 constructors, and checks that each term is a nonzero distribution, so
the limit is not vacuous. The unit-gap boundary consumer recovers the parent
sharp-gap separator on Schwartz tests. The CT1 normalized nonmeasure limit,
aggregate export and full release remain OPEN. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICANearGapLimitIndependent

/-- Complete expanded type of the controlled-limit root. -/
theorem expected_near_gap_controlled_limit_zero
    (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ) (hC0 : 0 ≤ C)
    (hlinear : ∀ n, ∀ R : ℝ, 0 ≤ R →
      ((nu n).positive + (nu n).negative).real (Icc (-R) R) ≤ C * (1 + R))
    (hnu : ∀ n, (nu n).HasLinearGrowth)
    (hself : ∀ n, 𝓕 ((nu n).distributionOfLinearGrowth (hnu n)) =
      (nu n).distributionOfLinearGrowth (hnu n))
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgapPos : ∀ n, (nu n).positive (Ioo (-a n) (a n)) = 0)
    (hgapNeg : ∀ n, (nu n).negative (Ioo (-a n) (a n)) = 0)
    (hoff : ∀ n, (nu n).negative (Set.range (fun k : ℤ => (k : ℝ)))ᶜ = 0)
    (hlim : Tendsto a atTop (𝓝 1)) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (nu n).distributionOfLinearGrowth (hnu n) φ) atTop (𝓝 0) :=
  near_gap_controlled_limit_zero nu C (fun n => ⟨hC0, hlinear n⟩) hself a ha ha1
    (fun n => ⟨hgapPos n, hgapNeg n⟩) hoff hlim φ

/-- The explicit single-measure estimate behind the limit, restated. -/
theorem expected_near_gap_schwartz_pairing_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth)
    (hself : 𝓕 (nu.distributionOfLinearGrowth hnu) = nu.distributionOfLinearGrowth hnu)
    (a C : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hgapPos : nu.positive (Ioo (-a) a) = 0) (hgapNeg : nu.negative (Ioo (-a) a) = 0)
    (hoff : nu.negative (Set.range (fun k : ℤ => (k : ℝ)))ᶜ = 0) (hC0 : 0 ≤ C)
    (hlinear : ∀ R : ℝ, 0 ≤ R → (nu.positive + nu.negative).real (Icc (-R) R) ≤ C * (1 + R))
    (φ : SchwartzMap ℝ ℂ) (N : ℕ) (hN : 1 ≤ N) (d : ℝ) (hd : 0 < d) (hd2 : d ≤ 1 / 2) :
    ‖nu.distributionOfLinearGrowth hnu φ‖ ≤
      (1 - a) * (2 * C * ((2 * N + 3) * SchwartzMap.seminorm ℝ 0 0 φ)) +
      2 * SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ φ) * d * (C * (1 + N)) +
      2 * SchwartzMap.seminorm ℝ 0 0 φ *
        ((Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (1 - a) * (2 * C)) +
      4 * C * (9 * SchwartzMap.seminorm ℝ 3 0 φ + 8 * SchwartzMap.seminorm ℝ 0 0 φ) /
        (N : ℝ) ^ 2 :=
  nearGap_schwartz_pairing_bound nu hnu hself ha ha1 ⟨hgapPos, hgapNeg⟩ hoff
    ⟨hC0, hlinear⟩ φ hN hd hd2

/-- Actual-domain consumer: the genuine CT1 family at L_n = log 2/(n+2).
Every premise of the root is discharged by the CT1 constructors. -/
theorem expected_CT1_controlled_limit (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n : ℕ => nearGapCombDistribution (Real.log 2 / ((n : ℝ) + 2)) φ)
      atTop (𝓝 0) := by
  set L : ℕ → ℝ := fun n => Real.log 2 / ((n : ℝ) + 2) with hLdef
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL (n : ℕ) : 0 < L n := by simp only [hLdef]; positivity
  have hu (n : ℕ) : L n < Real.log 2 := by
    simp only [hLdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : Tendsto L atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    have hshift : Tendsto (fun n : ℕ => Real.log 2 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 2)
    refine hshift.congr (fun n => ?_)
    simp only [hLdef]
    push_cast
    ring
  have hfam (n : ℕ) := dilation_near_gap_family (L n) (hL n) (hu n)
  have ha : Tendsto (fun n => Real.exp (-L n)) atTop (𝓝 1) := by
    have hneg : Tendsto (fun n => -L n) atTop (𝓝 0) := by simpa using hlim.neg
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hneg
  exact near_gap_controlled_limit_zero (fun n => nearGapCombFamily (L n)) 18
    (fun n => (hfam n).2.2.1) (fun n => (hfam n).2.2.2.1)
    (fun n => Real.exp (-L n)) (fun n => Real.exp_pos _)
    (fun n => ((hfam n).2.2.2.2.2.2.1).2.le) (fun n => (hfam n).2.2.2.2.2.1)
    (fun n => (hfam n).2.2.2.2.2.2.2.1) ha φ

/-- The family-level domain theorem, restated with explicit parameter domain. -/
theorem expected_CT1_family_controlled_limit (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hu : ∀ n, L n < Real.log 2) (hlim : Tendsto L atTop (𝓝 0))
    (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n =>
        (nearGapCombFamily (L n)).distributionOfLinearGrowth (nearGapCombFamily_growth (L n)) φ)
      atTop (𝓝 0) :=
  nearGapCombFamily_controlled_limit L hL hu hlim φ

/-- Non-vacuity: every term of the actual sequence is a nonzero distribution
(faithfulness of the parent Jordan-pair distribution map), so the controlled
limit is a genuine cancellation statement, not a statement about zero terms. -/
theorem expected_CT1_terms_nonzero (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    nearGapCombDistribution L ≠ 0 := by
  intro hzero
  have h := LocallyFiniteSignedMeasure.parts_eq_zero_of_distribution_eq_zero
    (nearGapCombFamily L) (nearGapCombFamily_growth L) hzero
  exact (dilation_near_gap_family L hL hu).2.2.2.2.2.2.2.2.2.1 h.1

/-- Boundary consumer a_n = 1: the constant sequence recovers the parent
unit-gap separator on every Schwartz test. -/
theorem expected_unit_gap_zero_pairing (nu : LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : CommonLinearMassBound C nu.totalVariation)
    (hself : nu.FourierSelfdual hC.linearGrowth) (hgap : nu.HasUnitGap)
    (hoff : nu.OffLatticeNonnegative) (φ : SchwartzMap ℝ ℂ) :
    nu.distributionOfLinearGrowth hC.linearGrowth φ = 0 := by
  have h := near_gap_controlled_limit_zero (fun _ => nu) C (fun _ => hC) (fun _ => hself)
    (fun _ => 1) (fun _ => one_pos) (fun _ => le_rfl) (fun _ => hgap) (fun _ => hoff)
    tendsto_const_nhds φ
  exact tendsto_const_nhds_iff.mp h

/-- Cross-check of the boundary consumer against the parent theorem. -/
theorem expected_unit_gap_matches_parent (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu) (hgap : nu.HasUnitGap)
    (hoff : nu.OffLatticeNonnegative) :
    nu.positive = 0 ∧ nu.negative = 0 :=
  signed_sharp_gap_separator nu hnu hself hgap hoff

end OPICANearGapLimitIndependent
#print axioms Zeta23.OPICAFollowup.near_gap_controlled_limit_zero
#print axioms Zeta23.OPICAFollowup.nearGap_schwartz_pairing_bound
#print axioms Zeta23.OPICAFollowup.nearGapCombFamily_controlled_limit
#print axioms OPICANearGapLimitIndependent.expected_near_gap_controlled_limit_zero
#print axioms OPICANearGapLimitIndependent.expected_near_gap_schwartz_pairing_bound
#print axioms OPICANearGapLimitIndependent.expected_CT1_controlled_limit
#print axioms OPICANearGapLimitIndependent.expected_CT1_family_controlled_limit
#print axioms OPICANearGapLimitIndependent.expected_CT1_terms_nonzero
#print axioms OPICANearGapLimitIndependent.expected_unit_gap_zero_pairing
#print axioms OPICANearGapLimitIndependent.expected_unit_gap_matches_parent
