import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ComplexConjugate
namespace Zeta23.OPICAFollowup.SquarePhysicalExpected
open Zeta23.OPICA

/-- Independent literal physical type: real Jordan measure, exact source density
and punctured comb, local finiteness, actual growth/gap/sign/origin and pairing. -/
theorem full_actual_square_measure {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) :
    ∃ ν:LocallyFiniteSignedMeasure,
      ν.positive=volume.withDensity (fun x=>ENNReal.ofReal (‖A-h x‖^2)) ∧
      ν.negative=ENNReal.ofReal (‖A‖^2) • puncturedLattice ∧
      ν.positive.MutuallySingular ν.negative ∧
      (∃ hg:ν.HasLinearGrowth,
        (ν.positive (Ioo (-1) 1)=0 ∧ ν.negative (Ioo (-1) 1)=0) ∧
        (ν.positive {0}=0 ∧ ν.negative {0}=0) ∧
        ν.negative (Set.range (fun n:ℤ=>(n:ℝ)))ᶜ=0 ∧
        (Measure.map (fun x:ℝ=>-x) ν.positive=ν.positive ∧
          Measure.map (fun x:ℝ=>-x) ν.negative=ν.negative) ∧
        (∀ φ:𝓢(ℝ,ℂ),ν.distributionOfLinearGrowth hg φ=
          (∫ x,((‖A-h x‖^2:ℝ):ℂ)*φ x)-
            ((‖A‖^2:ℝ):ℂ)*∑' n:ℤ,if n=0 then 0 else φ n) ∧
        (∀ φ:𝓢(ℝ,ℂ),𝓕 (ν.distributionOfLinearGrowth hg) φ-
          ν.distributionOfLinearGrowth hg φ=
            ∫ x,(autocorr h x-h x*conj (h x))*φ x)) := by
  refine ⟨squareGapJordan h A hcont,rfl,rfl,(squareGapJordan h A hcont).mutuallySingular,
    squareGapJordan_growth hcont hvan A,squareGapJordan_gap hcont A hpl,
    squareGapJordan_origin hcont A,squareGapJordan_off_lattice hcont A,
    squareGapJordan_even hcont A hev,?_,?_⟩
  · intro φ
    exact squareGapJordan_pairing hcont hvan A φ
  · intro φ
    exact squareGapJordan_fourier_defect hcont hint hL2 hsd hev hvan A φ

/-- Every arbitrary true Euclidean-tempered complex measure supported on the
integer lattice is covered. The four coordinate embeddings are derived, then
the literal sum of their genuine positive-measure tempered distributions is used. -/
theorem all_actual_tempered_corrections {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (σ:LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth]
    (hσ:σ.totalVariation (Set.range (fun n:ℤ=>(n:ℝ)))ᶜ=0) :
    ∃ (hrp:σ.rePart.positive.HasTemperateGrowth) (hrn:σ.rePart.negative.HasTemperateGrowth)
      (hip:σ.imPart.positive.HasTemperateGrowth) (hin:σ.imPart.negative.HasTemperateGrowth),
    letI := hrp; letI := hrn; letI := hip; letI := hin
    let T := (squareGapJordan h A hcont).distributionOfLinearGrowth
      (squareGapJordan_growth hcont hvan A)
    𝓕 (T+((σ.rePart.positive.toTemperedDistribution-σ.rePart.negative.toTemperedDistribution)+
      I • (σ.imPart.positive.toTemperedDistribution-σ.imPart.negative.toTemperedDistribution))) ≠
      T+((σ.rePart.positive.toTemperedDistribution-σ.rePart.negative.toTemperedDistribution)+
        I • (σ.imPart.positive.toTemperedDistribution-σ.imPart.negative.toTemperedDistribution)) := by
  let hrp := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).1
  let hrn := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).2.1
  let hip := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).2.2.1
  let hin := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).2.2.2
  refine ⟨hrp,hrn,hip,hin,?_⟩
  exact square_actual_no_tempered_measure_repair hev hcont hint hL2 hsd hvan hpl hne σ hσ

/-- The actual distribution projection, with its literal density identity and
every local positivity/gap-filling clause retained. -/
theorem full_actual_projection {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0) :
    let T := (squareGapJordan h A hcont).distributionOfLinearGrowth
      (squareGapJordan_growth hcont hvan A)
    let P := (1/2:ℂ) • (T+𝓕 T)
    𝓕 P=P ∧
    (∀ φ:𝓢(ℝ,ℂ),P φ=T φ+(1/2)*∫ x,(autocorr h x-h x*conj (h x))*φ x) ∧
    ∃ ε:ℝ,0<ε ∧ ε<1 ∧
      (∀ x∈Ioo (-ε) ε,0<(autocorr h x-h x*conj (h x)).re ∧
        (autocorr h x-h x*conj (h x)).im=0) ∧
      ∀ φ:𝓢(ℝ,ℂ),tsupport φ⊆Ioo (-ε) ε →
        P φ=∫ x,((autocorr h x-h x*conj (h x))/2)*φ x := by
  exact square_actual_projection_fills_gap hev hcont hint hL2 hsd hvan hpl hne

theorem nonzero_lattice_atom_retained :
    (squareGapJordan (fun _ : ℝ => (0:ℂ)) 1 continuous_const).negative {1}=1 := by
  simp [squareGapJordan,Measure.smul_apply,puncturedLattice_one]

theorem no_gap_without_plateau :
    (squareGapJordan (fun _ : ℝ => (0:ℂ)) 1 continuous_const).positive (Ioo (-1) 1)=2 := by
  norm_num [squareGapJordan,Real.volume_Ioo]

theorem zero_square_degenerate :
    (squareGapJordan (fun _ : ℝ => (0:ℂ)) 0 continuous_const).positive=0 ∧
      (squareGapJordan (fun _ : ℝ => (0:ℂ)) 0 continuous_const).negative=0 := by
  simp [squareGapJordan]

end Zeta23.OPICAFollowup.SquarePhysicalExpected
#print axioms Zeta23.OPICAFollowup.SquarePhysicalExpected.full_actual_square_measure
#print axioms Zeta23.OPICAFollowup.SquarePhysicalExpected.all_actual_tempered_corrections
#print axioms Zeta23.OPICAFollowup.SquarePhysicalExpected.full_actual_projection
#print axioms Zeta23.OPICAFollowup.SquarePhysicalExpected.nonzero_lattice_atom_retained
#print axioms Zeta23.OPICAFollowup.SquarePhysicalExpected.no_gap_without_plateau
#print axioms Zeta23.OPICAFollowup.SquarePhysicalExpected.zero_square_degenerate
