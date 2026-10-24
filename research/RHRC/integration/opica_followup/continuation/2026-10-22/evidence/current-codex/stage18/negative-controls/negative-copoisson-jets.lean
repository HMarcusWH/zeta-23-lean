import Zeta23.OPICAFollowup.CoPoissonJets
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICAFollowup
-- (1) jets are claimed only below the multiplicity: k ≤ m is not accepted
theorem bad_beyond_multiplicity (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) (hk : k ≤ zeroJetOrder ρ) :
    (normalizedZeroMeasureJet ρ k).variationControl (Ioo (-1) 1) = 0 :=
  (copoisson_zero_jets_measures ρ hz h0 h1 k hk).2.2.2.2.2.2.2.1
-- (2) the order-zero jet keeps the punctured lattice
theorem bad_no_lattice (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 0 < zeroJetOrder ρ) (φ : 𝓢(ℝ, ℂ)) :
    (normalizedZeroMeasureJet ρ 0).integral φ = ∫ x, zeroJetDensity (spectralKappa ρ) 0 x * φ x := by
  obtain ⟨-, -, -, -, hint, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 0 hm
  exact hint φ
-- (3) the B₂ tail enters with a minus sign
theorem bad_tail_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 1 < zeroJetOrder ρ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) 1 y - (bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |y| ^ (-3 : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htail, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 1 hm
  exact htail
-- (4) the tail rate is |y|^(-3), not |y|^(-4)
theorem bad_tail_rate (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) (hk : k < zeroJetOrder ρ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) k y -
        ((if k = 0 then 1 else 0) - ((if k = 0 then spectralKappa ρ else 0) + (if k = 1 then 1 else 0)) *
          ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)))‖ ≤ C * |y| ^ (-4 : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htail, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 k hk
  exact htail
-- (5) the first differentiated equation keeps its source G
theorem bad_chain_no_source (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 1 < zeroJetOrder ρ) (ψ : ℝ → ℂ) (hψ : CoPoissonJets.PositiveAxisTest ψ) :
    -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 1 x *
        deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
      spectralKappa ρ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 1 x * ψ x) =
    ∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 0 x * ψ x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hchain, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 1 hm
  exact hchain ψ hψ
-- (6) the branch derivative is -1/(2ρ - 1)
theorem bad_branch_derivative (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 0 < zeroJetOrder ρ) :
    deriv (zeroLocalInverse ρ) (spectralKappa ρ) = 1 / (2 * (ρ - 1 / 2)) := by
  obtain ⟨-, -, ⟨-, -, hd, -⟩, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 0 hm
  exact hd
-- (7) the reflected zero is not a separate node
theorem bad_reflected_new_node (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) (hk : k < zeroJetOrder ρ) :
    normalizedZeroMeasureJet (1 - ρ) k ≠ normalizedZeroMeasureJet ρ k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hν, -⟩, -⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 k hk
  exact hν
-- (8) the reflected multiplicity is the same
theorem bad_reflected_order (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 0 < zeroJetOrder ρ) : zeroJetOrder (1 - ρ) = zeroJetOrder ρ + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hr, -⟩, -⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 0 hm
  exact hr
-- (9) the conjugate relation conjugates the test
theorem bad_conj_without_test (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) (hk : k < zeroJetOrder ρ) (φ : 𝓢(ℝ, ℂ)) :
    (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
      starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral φ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hc⟩⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 k hk
  exact hc φ
-- (10) the strip condition 0 < Re ρ is required
theorem bad_no_strip (ρ : ℂ) (hz : riemannZeta ρ = 0) (h1 : ρ.re < 1) (k : ℕ) (hk : k < zeroJetOrder ρ) :
    (normalizedZeroMeasureJet ρ k).HasLinearGrowth := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hL, -⟩, -⟩ := copoisson_zero_jets_measures ρ hz h1 k hk
  exact hL
