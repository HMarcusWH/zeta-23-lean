import Zeta23.OPICAFollowup.FiniteSpanSeparation

noncomputable section
open Set MeasureTheory Complex
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.FiniteSpan

namespace OffcriticalRealBasis

lemma strip_ne_one {ρ : ℂ} (h1 : ρ.re < 1) : ρ ≠ 1 := by
  intro h
  subst ρ
  norm_num at h1

lemma validZeroth {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (c : ℂ) : ValidJet (c,ρ,0) :=
  ⟨hz,h0,h1,one_le_zeroJetOrder hz (strip_ne_one h1)⟩

def canonicalBasis (ρ : ℂ) : Fin 2 → List JetDatum :=
  ![[(1,ρ,0)],[(-I,ρ,0)]]

lemma canonicalBasis_valid {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∀ i, ∀ j ∈ canonicalBasis ρ i, ValidJet j := by
  intro i j hj
  have hk : 0 < zeroJetOrder ρ := by
    have hn : ρ ≠ 1 := by intro h; simpa [h] using h1
    exact one_le_zeroJetOrder hz hn
  fin_cases i <;> simp [canonicalBasis] at hj <;> subst j <;> exact ⟨hz,h0,h1,hk⟩

lemma singleton_realification {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (c : ℂ) (φ : 𝓢(ℝ,ℂ)) :
    (FiniteSpan.zeroJetRealSpan [(c,ρ,0)]).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (valid_singleton _ (validZeroth hz h0 h1 c))) φ =
      (c*(normalizedZeroMeasureJet ρ 0).integral φ +
        starRingEnd ℂ c * (normalizedZeroMeasureJet (starRingEnd ℂ ρ) 0).integral φ)/2 := by
  rw [zeroJetRealSpan_distribution _ (valid_singleton _ (validZeroth hz h0 h1 c))]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,map_mul]
  rw [normalizedZeroMeasureJet_conj h0 h1 (zero_ne_half hz)]

lemma conjugate_zeroth_independent {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hk : (spectralKappa ρ).im ≠ 0) :
    let nodes : Fin 2 → ℂ := ![ρ,starRingEnd ℂ ρ]
    let hz' : ∀ i, riemannZeta (nodes i) = 0 := by
      intro i; fin_cases i <;> simp [nodes,riemannZeta_conj,hz]
    let h0' : ∀ i, 0 < (nodes i).re := by
      intro i; fin_cases i <;> simpa [nodes] using h0
    let h1' : ∀ i, (nodes i).re < 1 := by
      intro i; fin_cases i <;> simpa [nodes] using h1
    LinearIndependent ℂ (fun i => (normalizedZeroMeasureJet (nodes i) 0).distributionOfLinearGrowth
      (normalizedZeroMeasureJet_hasLinearGrowth (h0' i) (h1' i) (zero_ne_half (hz' i))
        (one_le_zeroJetOrder (hz' i) (strip_ne_one (h1' i))))) := by
  dsimp only
  let nodes : Fin 2 → ℂ := ![ρ,starRingEnd ℂ ρ]
  have hz' : ∀ i, riemannZeta (nodes i) = 0 := by
    intro i; fin_cases i <;> simp [nodes,riemannZeta_conj,hz]
  have h0' : ∀ i, 0 < (nodes i).re := by
    intro i; fin_cases i <;> simpa [nodes] using h0
  have h1' : ∀ i, (nodes i).re < 1 := by
    intro i; fin_cases i <;> simpa [nodes] using h1
  have hd : distinctSpectralNodes nodes := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    · have hi := congrArg Complex.im hij
      simp [nodes,spectralKappa_conj] at hi
      exact False.elim (hk (by linarith))
    · have hi := congrArg Complex.im hij
      simp [nodes,spectralKappa_conj] at hi
      exact False.elim (hk (by linarith))
  let select (i : Fin 2) : (j : Fin 2) × Fin (zeroJetOrder (nodes j)) :=
    ⟨i,⟨0,one_le_zeroJetOrder (hz' i) (strip_ne_one (h1' i))⟩⟩
  have hs : Function.Injective select := fun i j h => congrArg Sigma.fst h
  exact (finite_zero_jet_independent nodes hz' h0' h1' hd).comp select hs

/-- For an actual strip zero with nonreal κ, the canonical real/imaginary
pair is independent over ℝ. No basis independence is supplied by the caller. -/
theorem canonicalBasis_independent {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hk : (spectralKappa ρ).im ≠ 0) :
    LinearIndependent ℝ (fun i =>
      (FiniteSpan.zeroJetRealSpan (canonicalBasis ρ i)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (canonicalBasis_valid hz h0 h1 i))) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  let c : Fin 2 → ℂ := ![(a 0 : ℂ)-I*(a 1 : ℂ),(a 0 : ℂ)+I*(a 1 : ℂ)]
  have hcomplex := conjugate_zeroth_independent hz h0 h1 hk
  have hc : (a 0 : ℂ)-I*(a 1 : ℂ)=0 := by
    change c 0=0
    refine Fintype.linearIndependent_iff.mp hcomplex c ?_ 0
    ext φ
    have hsφ := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) ha
    simp only [Fin.sum_univ_two,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply,Complex.real_smul] at hsφ
    change (a 0 : ℂ) * (FiniteSpan.zeroJetRealSpan [(1,ρ,0)]).distributionOfLinearGrowth _ φ +
      (a 1 : ℂ) * (FiniteSpan.zeroJetRealSpan [(-I,ρ,0)]).distributionOfLinearGrowth _ φ = 0 at hsφ
    rw [singleton_realification hz h0 h1 1 φ,singleton_realification hz h0 h1 (-I) φ] at hsφ
    simp only [map_one,map_neg,Complex.conj_I,neg_neg,one_mul] at hsφ
    simp only [Fin.sum_univ_two,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply,smul_eq_mul,
      LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply]
    change ((a 0 : ℂ)-I*(a 1 : ℂ))*(normalizedZeroMeasureJet ρ 0).integral φ +
      ((a 0 : ℂ)+I*(a 1 : ℂ))*(normalizedZeroMeasureJet (starRingEnd ℂ ρ) 0).integral φ = 0
    linear_combination 2*hsφ
  have hr := congrArg Complex.re hc
  have hi := congrArg Complex.im hc
  simp at hr hi
  fin_cases i
  · simpa using hr
  · simpa using hi

/-- The constant is fixed after ρ, before both real coefficients. The norm
is the Euclidean norm, and the right side uses the actual canonical Jordan
negative measure with the original off-lattice sinc-squared weight. -/
theorem canonical_pair_negative_mass_budget {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hk : (spectralKappa ρ).im ≠ 0) :
    ∃ cρ : ℝ, 0<cρ ∧ ∀ a b : ℝ,
      cρ*Real.sqrt (a^2+b^2) ≤ ∫ x in integerLatticeᶜ, sincSquared x
        ∂(FiniteSpan.zeroJetRealSpan [((a : ℂ),ρ,0),((b : ℂ)*(-I),ρ,0)]).negative := by
  obtain ⟨c,hc,hbound⟩ := Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget
    (canonicalBasis ρ) (canonicalBasis_valid hz h0 h1) (canonicalBasis_independent hz h0 h1 hk)
  refine ⟨c,hc,fun a b => ?_⟩
  simpa [EuclideanSpace.norm_eq,realBasisCombinationData,scaleJetData,canonicalBasis,
    Fin.sum_univ_two,Real.norm_eq_abs,sq_abs] using hbound (WithLp.toLp 2 ![a,b])

theorem canonical_pair_no_positive_combination {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hk : (spectralKappa ρ).im ≠ 0)
    (a b : ℝ)
    (hoff : (FiniteSpan.zeroJetRealSpan [((a : ℂ),ρ,0),((b : ℂ)*(-I),ρ,0)]).OffLatticeNonnegative) :
    a=0 ∧ b=0 := by
  have heq : (![a,b] : Fin 2 → ℝ)=0 :=
    independent_real_span_basis_coefficients_zero (canonicalBasis ρ)
      (canonicalBasis_valid hz h0 h1) (canonicalBasis_independent hz h0 h1 hk) ![a,b]
      (by simpa [realBasisCombinationData,scaleJetData,canonicalBasis] using hoff)
  exact ⟨by simpa using congrFun heq 0,by simpa using congrFun heq 1⟩

#print axioms canonicalBasis_independent
#print axioms canonical_pair_negative_mass_budget
#print axioms canonical_pair_no_positive_combination

end OffcriticalRealBasis





