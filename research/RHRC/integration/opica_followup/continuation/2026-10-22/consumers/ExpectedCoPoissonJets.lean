import Zeta23.OPICAFollowup.CoPoissonJets
import Zeta23.OPICAFollowup.ForcedEuler

/- Independent consumers for the original root `Zeta23.OPICAFollowup.copoisson_zero_jets_measures`
(R2-H1).

Definition audits pin the multiplicity (the analytic order of ζ), the entire κ-family density
built from the actual finite sums, the normalized κ-jets (1/k!) ∂_κ^k, the jet measures (the CP1 zero
measure at order zero, the jet density with its canonical Jordan pairs otherwise), the actual
construction (CP1.7)/b at an arbitrary parameter and the local inverse branch. The root is restated
in full. Domain consumers check:
- at every actual strip zero the order-zero jet exists and is the CP1 zero measure, and its
  parameter limit is the construction itself;
- the k = 0 forced chain is exactly the Stage 11 forced Euler identity of `ForcedEuler`;
- at a zero of multiplicity at least two the first jet is a pure density measure with the exact gap,
  density tail -B₂({|x|})/(2x²) + O(|x|⁻³) and forced equation (L - κ₀) h₁ = h₀ + G;
- the reflected zero gives the same node and the same jets, so it is not a separate node;
- on real tests the jets at the conjugate zero are the conjugate pairings. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICAFollowup
namespace OPICACoPoissonJetsIndependent

/-! ### Definition audits -/

theorem audit_zeroJetOrder (ρ : ℂ) : zeroJetOrder ρ = analyticOrderNatAt riemannZeta ρ := rfl

theorem audit_shKernel (w : ℂ) (u : ℝ) :
    shKernel w u = ∑' n : ℕ, w ^ n * (u : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ) := rfl

theorem audit_zeroFamilyDensity (κ : ℂ) (y : ℝ) :
    zeroFamilyDensity κ y = κ * ∑ k ∈ Finset.Icc 1 ⌊|y|⌋₊,
      ((Real.exp (-Real.log (|y| / k) / 2) / k : ℝ) : ℂ) * shKernel (1 / 4 - κ) (Real.log (|y| / k)) :=
  rfl

theorem audit_zeroJetDensity (κ₀ : ℂ) (k : ℕ) (y : ℝ) :
    zeroJetDensity κ₀ k y = iteratedDeriv k (fun κ => zeroFamilyDensity κ y) κ₀ / (k.factorial : ℂ) :=
  rfl

theorem audit_normalizedZeroMeasureJet (ρ : ℂ) (k : ℕ) :
    normalizedZeroMeasureJet ρ k = if k = 0 then zeroMeasure ρ else
      jetDensityMeasure (zeroJetDensity (spectralKappa ρ) k) (measurable_zeroJetDensity _ _)
        (locallyIntegrable_zeroJetDensity _ _) := rfl

theorem audit_jetDensityMeasure (g : ℝ → ℂ) (hgm : Measurable g) (hg : LocallyIntegrable g volume) :
    (jetDensityMeasure g hgm hg).rePart.positive = volume.withDensity (fun x => ENNReal.ofReal (g x).re) ∧
    (jetDensityMeasure g hgm hg).rePart.negative = volume.withDensity (fun x => ENNReal.ofReal (-(g x).re)) ∧
    (jetDensityMeasure g hgm hg).imPart.positive = volume.withDensity (fun x => ENNReal.ofReal (g x).im) ∧
    (jetDensityMeasure g hgm hg).imPart.negative = volume.withDensity (fun x => ENNReal.ofReal (-(g x).im)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem audit_zeroFamilyFunctional (ρ : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    zeroFamilyFunctional ρ φ = (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
      normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ := rfl

theorem audit_zeroLocalInverse (ρ₀ κ : ℂ) :
    zeroLocalInverse ρ₀ κ = 1 / 2 + (ρ₀ - 1 / 2) *
      (1 + (spectralKappa ρ₀ - κ) / (ρ₀ - 1 / 2) ^ 2) ^ ((2 : ℕ)⁻¹ : ℂ) := rfl

theorem audit_zeroJetProfile (κ₀ : ℂ) (k : ℕ) (x : ℝ) :
    zeroJetProfile κ₀ k x = (if k = 0 then 1 else 0) - zeroJetDensity κ₀ k x := rfl

theorem audit_positiveAxisTest (ψ : ℝ → ℂ) : CoPoissonJets.PositiveAxisTest ψ ↔ PositiveAxisTest ψ :=
  Iff.rfl

/-- The κ-family is the actual zero-measure density at every strip parameter ρ ≠ 1/2. -/
theorem expected_family_is_actual {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hh : ρ ≠ 1 / 2) (y : ℝ) :
    coPoissonComplexDensity ρ y = zeroFamilyDensity (spectralKappa ρ) y :=
  coPoissonComplexDensity_eq_family h0 h1 hh y

/-! ### Restated root -/

theorem expected_copoisson_zero_jets_measures (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (k : ℕ) (hk : k < zeroJetOrder ρ) :
    1 ≤ zeroJetOrder ρ ∧ analyticOrderAt riemannZeta ρ = zeroJetOrder ρ ∧
    (zeroLocalInverse ρ (spectralKappa ρ) = ρ ∧ AnalyticAt ℂ (zeroLocalInverse ρ) (spectralKappa ρ) ∧
      deriv (zeroLocalInverse ρ) (spectralKappa ρ) = -1 / (2 * (ρ - 1 / 2)) ∧
      (∀ κ, spectralKappa (zeroLocalInverse ρ κ) = κ) ∧
      analyticOrderAt (fun κ => riemannZeta (zeroLocalInverse ρ κ)) (spectralKappa ρ) = zeroJetOrder ρ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral φ =
      iteratedDeriv k (fun κ => zeroFamilyFunctional (zeroLocalInverse ρ κ) φ) (spectralKappa ρ) /
        (k.factorial : ℂ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral φ =
      (∫ x, zeroJetDensity (spectralKappa ρ) k x * φ x) -
        if k = 0 then ∑' n : ℤ, (if n = 0 then (0 : ℂ) else φ n) else 0) ∧
    (∀ y : ℝ, zeroJetDensity (spectralKappa ρ) k y =
      iteratedDeriv k (fun κ => zeroFamilyDensity κ y) (spectralKappa ρ) / (k.factorial : ℂ)) ∧
    (k = 0 → normalizedZeroMeasureJet ρ k = zeroMeasure ρ) ∧
    (normalizedZeroMeasureJet ρ k).variationControl (Ioo (-1) 1) = 0 ∧
    (normalizedZeroMeasureJet ρ k).variationControl {0} = 0 ∧
    (Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.positive =
        (normalizedZeroMeasureJet ρ k).rePart.positive ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.negative =
        (normalizedZeroMeasureJet ρ k).rePart.negative ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.positive =
        (normalizedZeroMeasureJet ρ k).imPart.positive ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.negative =
        (normalizedZeroMeasureJet ρ k).imPart.negative) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) k y -
        ((if k = 0 then 1 else 0) - ((if k = 0 then spectralKappa ρ else 0) + (if k = 1 then 1 else 0)) *
          ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)))‖ ≤ C * |y| ^ (-3 : ℝ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral (schwartzReflect φ) =
      (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (∃ hL : (normalizedZeroMeasureJet ρ k).HasLinearGrowth,
      𝓕 ((normalizedZeroMeasureJet ρ k).distributionOfLinearGrowth hL) =
          (normalizedZeroMeasureJet ρ k).distributionOfLinearGrowth hL ∧
        𝓕 ((normalizedZeroMeasureJet ρ k).rePart.distributionOfLinearGrowth
            ((normalizedZeroMeasureJet ρ k).re_hasLinearGrowth hL)) =
          (normalizedZeroMeasureJet ρ k).rePart.distributionOfLinearGrowth
            ((normalizedZeroMeasureJet ρ k).re_hasLinearGrowth hL)) ∧
    (∀ ψ : ℝ → ℂ, CoPoissonJets.PositiveAxisTest ψ →
      -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) k x *
          deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
        spectralKappa ρ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) k x * ψ x) =
      if k = 0 then spectralKappa ρ * ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
      else if k = 1 then (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 0 x * ψ x) +
        ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
      else ∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) (k - 1) x * ψ x) ∧
    (zeroJetOrder (1 - ρ) = zeroJetOrder ρ ∧ spectralKappa (1 - ρ) = spectralKappa ρ ∧
      normalizedZeroMeasureJet (1 - ρ) k = normalizedZeroMeasureJet ρ k ∧
      (∀ κ, zeroLocalInverse (1 - ρ) κ = 1 - zeroLocalInverse ρ κ) ∧
      ∀ φ : 𝓢(ℝ, ℂ), iteratedDeriv k (fun κ => zeroFamilyFunctional (1 - zeroLocalInverse ρ κ) φ)
          (spectralKappa ρ) / (k.factorial : ℂ) = (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (zeroJetOrder (starRingEnd ℂ ρ) = zeroJetOrder ρ ∧
      ∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
        starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral (complexSchwartzConj φ))) :=
  copoisson_zero_jets_measures ρ hz h0 h1 k hk

/-! ### Domain consumers -/

/-- At every actual strip zero the order-zero jet exists, is the CP1 zero measure, and its parameter
limit is the actual construction itself. -/
theorem expected_order_zero_jet (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < zeroJetOrder ρ ∧ normalizedZeroMeasureJet ρ 0 = zeroMeasure ρ ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ 0).integral φ = zeroFamilyFunctional ρ φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = (zeroMeasure ρ).integral φ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have h0m : 0 < zeroJetOrder ρ := Nat.lt_of_lt_of_le zero_lt_one (one_le_zeroJetOrder hz hρ1)
  obtain ⟨-, -, ⟨hc, -⟩, hpl, -, -, hz0, -, -, -, -, hF, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 0 h0m
  have hν := hz0 rfl
  refine ⟨h0m, hν, fun φ => ?_, fun φ => ?_⟩
  · rw [hpl φ, iteratedDeriv_zero, hc]; simp
  · rw [← hν]; exact hF φ

/-- The k = 0 forced chain is exactly the Stage 11 forced Euler identity of `ForcedEuler`. -/
theorem expected_chain_is_forced_euler (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {ψ : ℝ → ℂ} (hψ : PositiveAxisTest ψ) :
    eulerImage ρ ψ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * ψ x) +
      ∑' n : ℕ, ψ (n + 1)) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  have hm : 0 < zeroJetOrder ρ := Nat.lt_of_lt_of_le zero_lt_one (one_le_zeroJetOrder hz hρ1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hchain, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 0 hm
  have hc := hchain ψ hψ
  simp only [if_true] at hc
  have hp : ∀ x, zeroJetProfile (spectralKappa ρ) 0 x = zeroProfile ρ x := zeroJetProfile_zero ρ hρ0 hρ1 hh
  simp only [hp] at hc
  have hψc : Continuous ψ := hψ.1.continuous
  have hI : Integrable (fun x => zeroProfile ρ x * ψ x) (volume.restrict (Ioi 0)) :=
    (((continuous_zeroProfile ρ).mul hψc).integrable_of_hasCompactSupport hψ.2.1.mul_left).restrict
  have hW : Integrable ψ (volume.restrict (Ioi 0)) := (hψc.integrable_of_hasCompactSupport hψ.2.1).restrict
  have hsplit : (∫ x in Ioi 0, (zeroProfile ρ x - 1) * ψ x) =
      (∫ x in Ioi 0, zeroProfile ρ x * ψ x) - ∫ x in Ioi 0, ψ x := by
    rw [← integral_sub hI hW]; congr 1; funext x; ring
  rw [eulerImage, hsplit]
  linear_combination hc

/-- At a zero of multiplicity at least two the first jet is a pure density measure. -/
theorem expected_first_jet (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 2 ≤ zeroJetOrder ρ) :
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ 1).integral φ =
      ∫ x, zeroJetDensity (spectralKappa ρ) 1 x * φ x) ∧
    (normalizedZeroMeasureJet ρ 1).variationControl (Ioo (-1) 1) = 0 ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) 1 y + (bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |y| ^ (-3 : ℝ)) ∧
    (∀ ψ : ℝ → ℂ, PositiveAxisTest ψ →
      -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 1 x *
          deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
        spectralKappa ρ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 1 x * ψ x) =
      (∫ x in Ioi 0, zeroProfile ρ x * ψ x) + ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  obtain ⟨-, -, -, -, hint, -, -, hgap, -, -, ⟨C, hC, htail⟩, -, -, -, hchain, -⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 1 (by omega)
  refine ⟨fun φ => by rw [hint φ]; simp, hgap, ⟨C, hC, fun y hy => ?_⟩, fun ψ hψ => ?_⟩
  · have := htail y hy
    simp only [one_ne_zero, if_false, if_true, zero_add, one_mul, zero_sub] at this
    simpa [sub_neg_eq_add] using this
  · have hc := hchain ψ hψ
    simp only [one_ne_zero, if_false, if_true] at hc
    rw [hc]
    congr 2
    funext x
    rw [zeroJetProfile_zero ρ hρ0 hρ1 hh]

/-- The reflected zero gives the same node κ₀ and the same jets: it is not a separate node. -/
theorem expected_reflection_not_new_node (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (k : ℕ) (hk : k < zeroJetOrder ρ) :
    riemannZeta (1 - ρ) = 0 ∧ spectralKappa (1 - ρ) = spectralKappa ρ ∧
      zeroJetOrder (1 - ρ) = zeroJetOrder ρ ∧ normalizedZeroMeasureJet (1 - ρ) k = normalizedZeroMeasureJet ρ k := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hm, hκ, hν, -, -⟩, -⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 k hk
  refine ⟨?_, hκ, hm, hν⟩
  rw [zetaFunctionalFactor_eq h0 hρ1, hz, mul_zero]

/-- On real tests the jets at the conjugate zero are the conjugate pairings. -/
theorem expected_conj_real_test (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) (hk : k < zeroJetOrder ρ) (φ : 𝓢(ℝ, ℂ)) (hφ : complexSchwartzConj φ = φ) :
    riemannZeta (starRingEnd ℂ ρ) = 0 ∧ zeroJetOrder (starRingEnd ℂ ρ) = zeroJetOrder ρ ∧
      (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
        starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral φ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hm, hc⟩⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 k hk
  refine ⟨by rw [_root_.riemannZeta_conj, hz, map_zero], hm, ?_⟩
  rw [hc φ, hφ]

end OPICACoPoissonJetsIndependent

#print axioms OPICACoPoissonJetsIndependent.audit_zeroJetOrder
#print axioms OPICACoPoissonJetsIndependent.audit_normalizedZeroMeasureJet
#print axioms OPICACoPoissonJetsIndependent.expected_family_is_actual
#print axioms OPICACoPoissonJetsIndependent.expected_copoisson_zero_jets_measures
#print axioms OPICACoPoissonJetsIndependent.expected_order_zero_jet
#print axioms OPICACoPoissonJetsIndependent.expected_chain_is_forced_euler
#print axioms OPICACoPoissonJetsIndependent.expected_first_jet
#print axioms OPICACoPoissonJetsIndependent.expected_reflection_not_new_node
#print axioms OPICACoPoissonJetsIndependent.expected_conj_real_test
