import Zeta23.OPICAFollowup.RenormalizedCoPoisson
import Zeta23.OPICA.SignedHeatSeparator

/- Independent consumers for the original R1-CP1 root
`Zeta23.OPICAFollowup.zero_measure_exact_properties`.

Definition audits pin b_ρ, κ, the punctured lattice and the four canonical Jordan parts of the
normalized zero measure. The root is restated in full. Domain consumers check:
- the real part η_ρ satisfies the parent H1 predicates `HasUnitGap`, `FourierSelfdual` and
  `HasLinearGrowth` (Zeta23.OPICA.SignedHeatSeparator);
- the atom at -1 is also -1 (evenness);
- for every ρ = 1/2 + δ + iγ with |γ| > 3π/(2 log 2) (in particular every actual zero above that
  height), η_ρ is NOT off-lattice nonnegative: its negative part has positive mass on an open
  subinterval of (1, 2) (the first-cell sign root plus continuity of the first-cell density).
  At such an actual zero η_ρ therefore supplies every H1 hypothesis except off-lattice
  nonnegativity, as the paper states;
- the construction-level clauses that do not use ζ(ρ) = 0 are non-vacuous at ρ = 3/4. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ENNReal
open Zeta23.OPICAFollowup
namespace OPICAZeroMeasureIndependent

/-! ### Definition audits -/

theorem audit_brho (ρ : ℂ) : normalizationBrho ρ = (1 - 2 * ρ) / (ρ * (1 - ρ)) := rfl

theorem audit_kappa (ρ : ℂ) : coPoissonKappa ρ = ρ * (1 - ρ) := rfl

theorem audit_lattice : puncturedLattice = (dilatedCombMeasure 0).restrict {0}ᶜ := rfl

theorem audit_parts (ρ : ℂ) :
    (zeroMeasure ρ).rePart.positive =
      volume.withDensity (fun x => ENNReal.ofReal (coPoissonComplexDensity ρ x).re) ∧
    (zeroMeasure ρ).rePart.negative =
      volume.withDensity (fun x => ENNReal.ofReal (-(coPoissonComplexDensity ρ x).re)) +
        puncturedLattice ∧
    (zeroMeasure ρ).imPart.positive =
      volume.withDensity (fun x => ENNReal.ofReal (coPoissonComplexDensity ρ x).im) ∧
    (zeroMeasure ρ).imPart.negative =
      volume.withDensity (fun x => ENNReal.ofReal (-(coPoissonComplexDensity ρ x).im)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem audit_density (ρ : ℂ) (x : ℝ) :
    coPoissonComplexDensity ρ x = coPoissonPowerSums ρ |x| / (1 / ρ - 1 / (1 - ρ)) := rfl

/-! ### Restated root -/

theorem expected_zero_measure_exact_properties (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    normalizationBrho ρ = (1 - 2 * ρ) / coPoissonKappa ρ ∧
    normalizationBrho ρ = 1 / ρ - 1 / (1 - ρ) ∧ normalizationBrho ρ ≠ 0 ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
        normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (∫ x, coPoissonComplexDensity ρ x * φ x) - ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n) ∧
    (zeroMeasure ρ).HasLinearGrowth ∧
    𝓕 ((zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) =
      (zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1) ∧
    (Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.positive = (zeroMeasure ρ).rePart.positive ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.negative = (zeroMeasure ρ).rePart.negative ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.positive = (zeroMeasure ρ).imPart.positive ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.negative =
        (zeroMeasure ρ).imPart.negative) ∧
    (zeroMeasure ρ).variationControl (Ioo (-1) 1) = 0 ∧
    (zeroMeasure ρ).variationControl {0} = 0 ∧
    ((zeroMeasure ρ).rePart.positive {1} = 0 ∧ (zeroMeasure ρ).rePart.negative {1} = 1 ∧
      (zeroMeasure ρ).imPart.positive {1} = 0 ∧ (zeroMeasure ρ).imPart.negative {1} = 0) ∧
    ((zeroMeasure ρ).rePart.positive =
        volume.withDensity (fun x => ENNReal.ofReal (coPoissonRealDensity ρ x)) ∧
      (zeroMeasure ρ).rePart.negative =
        volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) + puncturedLattice) ∧
    (zeroMeasure ρ).rePart.HasLinearGrowth ∧
    𝓕 ((zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1))) =
      (zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) ∧
    ((zeroMeasure ρ).rePart.positive (Ioo (-1) 1) = 0 ∧
      (zeroMeasure ρ).rePart.negative (Ioo (-1) 1) = 0) ∧
    ((zeroMeasure ρ).rePart.positive {0} = 0 ∧ (zeroMeasure ρ).rePart.negative {0} = 0) ∧
    ((zeroMeasure ρ).rePart.positive.real {1} = 0 ∧ (zeroMeasure ρ).rePart.negative.real {1} = 1) ∧
    (zeroMeasure ρ).rePart.negative ≠ 0 :=
  zero_measure_exact_properties ρ hz h0 h1 hh

/-! ### Domain consumers -/

/-- η_ρ satisfies the parent H1 predicates: exact unit gap, Fourier self-duality and linear growth. -/
theorem expected_real_part_H1_hypotheses (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    (zeroMeasure ρ).rePart.HasUnitGap ∧
      (zeroMeasure ρ).rePart.FourierSelfdual
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) ∧
      (zeroMeasure ρ).rePart.HasLinearGrowth := by
  have h := zero_measure_exact_properties ρ hz h0 h1 hh
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Evenness moves the atom -1 at 1 to an atom -1 at -1. -/
theorem expected_atom_minus_one (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    (zeroMeasure ρ).rePart.negative {-1} = 1 ∧ (zeroMeasure ρ).rePart.positive {-1} = 0 := by
  have h := zero_measure_exact_properties ρ hz h0 h1 hh
  obtain ⟨hp, hn, -, -⟩ := h.2.2.2.2.2.2.2.1
  obtain ⟨a1, a2, -, -⟩ := h.2.2.2.2.2.2.2.2.2.2.1
  have hpre : (fun x : ℝ => -x) ⁻¹' ({-1} : Set ℝ) = {1} := by ext x; simp
  constructor
  · rw [← hn, Measure.map_apply measurable_neg (measurableSet_singleton _), hpre, a2]
  · rw [← hp, Measure.map_apply measurable_neg (measurableSet_singleton _), hpre, a1]

/-- The first-cell density is continuous on (1, 2). -/
lemma first_cell_density_continuousOn (ρ : ℂ) :
    ContinuousOn (coPoissonRealDensity ρ) (Ioo (1 : ℝ) 2) := by
  have heq : EqOn (coPoissonRealDensity ρ)
      (fun x : ℝ => (((x : ℂ) ^ (-ρ) - (x : ℂ) ^ (ρ - 1)) / coPoissonOriginNormalizer ρ).re)
      (Ioo (1 : ℝ) 2) := by
    intro x hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx.1.le
    simp only [coPoissonRealDensity, coPoissonComplexDensity, abs_of_nonneg hx0,
      coPoisson_first_cell_sum ρ hx]
  refine ContinuousOn.congr ?_ heq
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans hx.1
  have hs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx0
  refine (Complex.continuous_re.continuousAt.comp ?_).continuousWithinAt
  refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _
  · exact (continuousAt_cpow_const hs).comp Complex.continuous_ofReal.continuousAt
  · exact (continuousAt_cpow_const hs).comp Complex.continuous_ofReal.continuousAt

/-- Above the first-cell height η_ρ is not off-lattice nonnegative (no zero hypothesis needed). -/
theorem expected_not_offlattice_nonnegative (δ γ : ℝ)
    (hheight : 3 * Real.pi / (2 * Real.log 2) < |γ|) :
    ¬ (zeroMeasure (coPoissonRho δ γ)).rePart.OffLatticeNonnegative := by
  intro hnn
  obtain ⟨hu, hu1, -, hneg⟩ := (zero_measure_first_cell_sign δ γ hheight).1
  set ρ := coPoissonRho δ γ with hρ
  set u := 3 * Real.pi / (2 * |γ|) with hudef
  have hx : Real.exp u ∈ Ioo (1 : ℝ) 2 := ⟨Real.one_lt_exp_iff.mpr hu,
    (Real.exp_lt_exp.mpr hu1).trans_eq (Real.exp_log (by norm_num))⟩
  set U : Set ℝ := Ioo (1 : ℝ) 2 ∩ coPoissonRealDensity ρ ⁻¹' Iio 0 with hU
  have hUopen : IsOpen U :=
    (first_cell_density_continuousOn ρ).isOpen_inter_preimage isOpen_Ioo isOpen_Iio
  have hUmem : Real.exp u ∈ U := ⟨hx, hneg⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨_, hUmem⟩
  have hUlat : U ⊆ Zeta23.OPICA.integerLatticeᶜ := by
    rintro x ⟨hx1, -⟩ ⟨n, rfl⟩
    have h1 : (1 : ℝ) < n := hx1.1
    have h2 : (n : ℝ) < 2 := hx1.2
    have h1' : (1 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (2 : ℤ) := by exact_mod_cast h2
    omega
  have hfm : Measurable (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) :=
    ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp
      (measurable_coPoissonComplexDensity ρ)).neg
  have hmass : 0 < volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) U := by
    rw [withDensity_apply _ hUopen.measurableSet, setLIntegral_pos_iff hfm]
    have hsub : U ⊆ Function.support (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) ∩ U :=
      fun x hx => ⟨by
        simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        have : coPoissonRealDensity ρ x < 0 := hx.2
        linarith, hx⟩
    exact hUpos.trans_le (measure_mono hsub)
  have hzero : (zeroMeasure ρ).rePart.negative Zeta23.OPICA.integerLatticeᶜ = 0 := hnn
  change (volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) +
    puncturedLattice) Zeta23.OPICA.integerLatticeᶜ = 0 at hzero
  rw [Measure.add_apply, add_eq_zero] at hzero
  have := (measure_mono hUlat).trans_eq hzero.1
  exact absurd hmass (not_lt.mpr this)

/-- Non-vacuity of the construction-level clauses (they do not use ζ(ρ) = 0). -/
theorem expected_construction_nonvacuous :
    (zeroMeasure (3 / 4)).HasLinearGrowth ∧
      (zeroMeasure (3 / 4)).variationControl (Ioo (-1) 1) = 0 ∧
      (zeroMeasure (3 / 4)).rePart.negative {1} = 1 :=
  ⟨zeroMeasure_hasLinearGrowth (by norm_num) (by norm_num), zeroMeasure_gap _,
    (zeroMeasure_atom_one _).2.1⟩

end OPICAZeroMeasureIndependent
#print axioms Zeta23.OPICAFollowup.zero_measure_exact_properties
#print axioms OPICAZeroMeasureIndependent.audit_parts
#print axioms OPICAZeroMeasureIndependent.expected_zero_measure_exact_properties
#print axioms OPICAZeroMeasureIndependent.expected_real_part_H1_hypotheses
#print axioms OPICAZeroMeasureIndependent.expected_atom_minus_one
#print axioms OPICAZeroMeasureIndependent.expected_not_offlattice_nonnegative
#print axioms OPICAZeroMeasureIndependent.expected_construction_nonvacuous
