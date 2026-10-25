import Zeta23.OPICAFollowup.RenormalizedCoPoisson

/- Independent consumers for the original R1-CP1 root
`Zeta23.OPICAFollowup.renormalized_copoisson_order_zero`.

Definition audits pin the cutoff density (CP1.5), the cutoff origin atom, the limit density
(CP1.4) and both measures to their explicit constructions. The root is restated in full.
Domain consumers check, on the open strip 0 < Re ρ < 1:
- the cutoff and limit origin atoms (1 - e^(-ρT))/ρ and 1/ρ on every compact window containing 0;
- that the limit density near the origin is ζ(ρ)|x|^(ρ-1) + 1/(1-ρ) (S_ρ vanishes on |x| < 1);
- convergence of the actual cutoff pairings to V_(ρ-1/2)(φ) for every Schwartz test;
- convergence of bounded measurable compact-window integrals under the parent
  `LocalVariationConvergence`;
- non-vacuity at ρ = 1/2. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
namespace OPICACoPoissonOrderZeroIndependent

/-! ### Definition audits -/

theorem audit_cutoff_density (ρ : ℂ) (T x : ℝ) : coPoissonCutoffDensity ρ T x =
    ((|x| : ℝ) : ℂ) ^ (-ρ) *
        ∑ n ∈ Finset.Icc (max 1 ⌈|x| * Real.exp (-T)⌉₊) ⌊|x|⌋₊, (n : ℂ) ^ (ρ - 1) +
      ((|x| : ℝ) : ℂ) ^ (ρ - 1) * ∑ n ∈ Finset.Ioc ⌊|x|⌋₊ ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) -
      (cexp ((1 - ρ) * T) - 1) / (1 - ρ) := rfl

theorem audit_cutoff_atom (ρ : ℂ) (T : ℝ) :
    coPoissonCutoffAtom ρ T = (1 - cexp (-ρ * T)) / ρ := rfl

theorem audit_limit_density (ρ : ℂ) (x : ℝ) : coPoissonLimitDensity ρ x =
    coPoissonPowerSums ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ) := rfl

theorem audit_cutoff_measure (ρ : ℂ) (T : ℝ) : coPoissonCutoff ρ T =
    densityAtomMeasure (coPoissonCutoffDensity ρ T) (coPoissonCutoffAtom ρ T)
      (locallyIntegrable_coPoissonCutoffDensity ρ T) := rfl

theorem audit_limit_measure (ρ : ℂ) (h0 : 0 < ρ.re) : coPoissonLimitMeasure ρ h0 =
    densityAtomMeasure (coPoissonLimitDensity ρ) (1 / ρ)
      (locallyIntegrable_coPoissonLimitDensity h0) := rfl

/-! ### Restated root -/

theorem expected_renormalized_copoisson_order_zero (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (∀ T : ℝ, 0 ≤ T → ∀ φ : 𝓢(ℝ, ℂ), (coPoissonCutoff ρ T).integral φ =
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * renormalizedCombKernel t φ) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ φ : 𝓢(ℝ, ℂ), (coPoissonCutoff ρ T).integral φ =
      (∫ x, coPoissonCutoffDensity ρ T x * φ x) + (1 - cexp (-ρ * T)) / ρ * φ 0) ∧
    (∀ (T : ℝ) (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ), MeasurableSet E →
      (coPoissonCutoff ρ T).compactRestriction K hK E =
        (∫ x in E ∩ K, coPoissonCutoffDensity ρ T x) +
          (E ∩ K).indicator (fun _ => (1 - cexp (-ρ * T)) / ρ) 0) ∧
    (∀ (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ), MeasurableSet E →
      (coPoissonLimitMeasure ρ h0).compactRestriction K hK E =
        (∫ x in E ∩ K, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) +
          1 / (1 - ρ))) + (E ∩ K).indicator (fun _ => 1 / ρ) 0) ∧
    (∀ (K : Set ℝ) (hK : IsCompact K), Tendsto (fun T : ℝ =>
      ((coPoissonCutoff ρ T).compactRestriction K hK -
        (coPoissonLimitMeasure ρ h0).compactRestriction K hK).variation.real univ) atTop (𝓝 0)) ∧
    LocalVariationConvergence (fun n : ℕ => coPoissonCutoff ρ n) (coPoissonLimitMeasure ρ h0) ∧
    (∀ φ : 𝓢(ℝ, ℂ), coPoissonFamily (ρ - 1 / 2) φ = (coPoissonLimitMeasure ρ h0).integral φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), coPoissonFamily (ρ - 1 / 2) φ =
      (∫ x, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ)) * φ x) +
        1 / ρ * φ 0) :=
  renormalized_copoisson_order_zero ρ h0 h1

/-! ### Domain consumers -/

lemma singleton_window (K : Set ℝ) (h0 : (0 : ℝ) ∈ K) :
    ({0} : Set ℝ) ∩ K = {0} := by
  ext x; simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, h0⟩

/-- The limit measure carries exactly the origin atom 1/ρ (the origin correction). -/
theorem expected_limit_origin_atom (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (K : Set ℝ)
    (hK : IsCompact K) (hK0 : (0 : ℝ) ∈ K) :
    (coPoissonLimitMeasure ρ h0).compactRestriction K hK {0} = 1 / ρ := by
  rw [(renormalized_copoisson_order_zero ρ h0 h1).2.2.2.1 K hK {0} (measurableSet_singleton 0),
    singleton_window K hK0, Set.indicator_of_mem (mem_singleton 0),
    setIntegral_measure_zero _ (measure_singleton 0), zero_add]

/-- The actual cutoff carries the origin atom (1 - e^(-ρT))/ρ = ∫_0^T e^(-ρt) dt. -/
theorem expected_cutoff_origin_atom (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (T : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : (0 : ℝ) ∈ K) :
    (coPoissonCutoff ρ T).compactRestriction K hK {0} = (1 - cexp (-ρ * T)) / ρ := by
  rw [(renormalized_copoisson_order_zero ρ h0 h1).2.2.1 T K hK {0} (measurableSet_singleton 0),
    singleton_window K hK0, Set.indicator_of_mem (mem_singleton 0),
    setIntegral_measure_zero _ (measure_singleton 0), zero_add]

/-- S_ρ vanishes on |x| < 1, so the limit density there is ζ(ρ)|x|^(ρ-1) + 1/(1-ρ). -/
theorem expected_limit_density_near_origin (ρ : ℂ) {x : ℝ} (hx : |x| < 1) :
    coPoissonLimitDensity ρ x = riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ) := by
  have hf : ⌊|x|⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [coPoissonLimitDensity, finiteSumSrho, coPoissonPowerSums, hf]

/-- The actual cutoff pairings converge to the entire family on every Schwartz test. -/
theorem expected_cutoff_pairing_tendsto (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun T : ℝ => (coPoissonCutoff ρ T).integral φ) atTop
      (𝓝 ((coPoissonLimitMeasure ρ h0).integral φ)) := by
  have hroot := renormalized_copoisson_order_zero ρ h0 h1
  rw [← hroot.2.2.2.2.2.2.1 φ, coPoissonFamily_apply]
  refine Tendsto.congr' ?_ (intervalIntegral_tendsto_integral_Ioi 0
    (renormalizedCombKernel_laplace_integrable _ φ) tendsto_id)
  filter_upwards [eventually_ge_atTop 0] with T hT
  exact (hroot.1 T hT φ).symm

/-- Compact-window integrals of bounded measurable tests converge (parent notion). -/
theorem expected_local_test_convergence (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (K : Set ℝ) (hK : IsCompact K) (f : ℝ → ℂ) (hf : StronglyMeasurable f) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n : ℕ => finiteComplexIntegral ((coPoissonCutoff ρ n).compactRestriction K hK) f)
      atTop (𝓝 (finiteComplexIntegral ((coPoissonLimitMeasure ρ h0).compactRestriction K hK) f)) :=
  ((renormalized_copoisson_order_zero ρ h0 h1).2.2.2.2.2.1).tendsto_local_test K hK f hf C hC
    hbound

/-- Non-vacuity: the critical point ρ = 1/2 lies in the domain. -/
theorem expected_nonvacuous_half (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily ((1 / 2 : ℂ) - 1 / 2) φ =
      (∫ x, (finiteSumSrho (1 / 2) |x| + riemannZeta (1 / 2) * ((|x| : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) +
        1 / (1 - 1 / 2)) * φ x) + 1 / (1 / 2) * φ 0 :=
  (renormalized_copoisson_order_zero (1 / 2) (by norm_num) (by norm_num)).2.2.2.2.2.2.2 φ

end OPICACoPoissonOrderZeroIndependent
#print axioms Zeta23.OPICAFollowup.renormalized_copoisson_order_zero
#print axioms OPICACoPoissonOrderZeroIndependent.audit_cutoff_density
#print axioms OPICACoPoissonOrderZeroIndependent.audit_limit_measure
#print axioms OPICACoPoissonOrderZeroIndependent.expected_renormalized_copoisson_order_zero
#print axioms OPICACoPoissonOrderZeroIndependent.expected_limit_origin_atom
#print axioms OPICACoPoissonOrderZeroIndependent.expected_cutoff_origin_atom
#print axioms OPICACoPoissonOrderZeroIndependent.expected_limit_density_near_origin
#print axioms OPICACoPoissonOrderZeroIndependent.expected_cutoff_pairing_tendsto
#print axioms OPICACoPoissonOrderZeroIndependent.expected_local_test_convergence
#print axioms OPICACoPoissonOrderZeroIndependent.expected_nonvacuous_half
