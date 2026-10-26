import Zeta23.OPICARound2.ProfileControls

/-! Independent consumers of completed clauses. The full profile contracts
also require their remaining analytic/test-realization clauses. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators SchwartzMap
namespace Zeta23.OPICARound2.Validation

theorem literal_height_free_first_cell_point_consumer (w : ProfileWitness) :
    let q : ℂ := w.rho - 1 / 2
    let kappa : ℂ := w.rho * (1 - w.rho)
    let R : ℝ := ‖q‖ ^ 2 + ‖kappa‖
    let u : ℝ := min (Real.log 2 / 2) (1 / Real.sqrt R)
    0 < u ∧ u < Real.log 2 ∧
      2 * (w.rho.re - 1 / 2) * w.rho.im * u * Real.exp (-u / 2) *
        (1 - 1 / (2 * Real.exp 1)) ≤
          -(OPICAFollowup.coPoissonComplexDensity w.rho (Real.exp u)).im :=
  ⟨profileUStar_pos w, profileUStar_lt_log_two w, profile_height_free_point_margin w⟩

theorem actual_positive_first_cell_test_consumer (w : ProfileWitness) :
    (∀ x : ℝ, 0 ≤ profileUnitTest w x) ∧
    (∫ x : ℝ, profileUnitTest w x) = 1 ∧
    HasCompactSupport (profileUnitTest w) ∧ tsupport (profileUnitTest w) ⊆ Ioo (1 : ℝ) 2 :=
  ⟨profileUnitTest_nonneg w, profileUnitTest_integral w,
    profileUnitTest_compact w, profileUnitTest_support w⟩

theorem exact_factorial_margin_consumer :
    HasSum (fun n : ℕ => (n : ℝ) / ((2 * n + 1).factorial : ℝ)) (1 / (2 * Real.exp 1)) :=
  profile_factorial_margin_series

theorem one_sided_n_linear_tests_counter_consumer {n : ℕ} (hn : 1 ≤ n)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∃ a : Fin n → ℝ, a ≠ 0 ∧ ∀ i : Fin n, 0 ≤ F a i :=
  profile_n_linear_tests_cannot_exclude hn F


theorem actual_density_derivative_budget_consumer (w : ProfileWitness) {x : ℝ}
    (hx : x ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (OPICAFollowup.coPoissonComplexDensity w.rho) (profileCellDerivative w x) x ∧
      ‖profileCellDerivative w x‖ ≤
        ‖OPICAFollowup.coPoissonKappa w.rho / (w.rho - 1 / 2)‖ *
          (‖w.rho - 1 / 2‖ + 1 / 2) * Real.cosh ((w.rho.re - 1 / 2) * Real.log 2) :=
  ⟨profileDensity_hasDerivAt w hx, profileCellDerivative_norm_le w hx⟩

theorem actual_native_imaginary_positive_test_consumer (w : ProfileWitness) :
    ∃ phi : 𝓢(ℝ, ℝ), HasCompactSupport phi ∧ (∀ x : ℝ, 0 ≤ phi x) ∧
      (∫ x : ℝ, phi x) = 1 ∧ tsupport phi ⊆ Ioo (1 : ℝ) 2 ∧
      (OPICAFollowup.zeroMeasure w.rho).imPart.integral phi ≤ -3 * profileMStar w / 4 := by
  exact ⟨profileUnitTest w, profileUnitTest_compact w, profileUnitTest_nonneg w,
    profileUnitTest_integral w, profileUnitTest_support w, profileUnitTest_pairing_margin w⟩

theorem same_fixed_actual_pairing_error_floor (w : ProfileWitness) (P : ℝ) (hP : 0 ≤ P) :
    3 * profileMStar w / 4 ≤
      |P - (OPICAFollowup.zeroMeasure w.rho).imPart.integral (profileUnitTest w)| := by
  by_contra h
  exact profile_fixed_negative_pairing_contradiction _ _ _ (profileMStar_pos w)
    (profileUnitTest_pairing_margin w) hP (lt_of_not_ge h)

theorem actual_critical_line_imaginary_control (gamma u : ℝ) (hg : gamma ≠ 0)
    (hu : 0 < u) (hu2 : u < Real.log 2) :
    (OPICAFollowup.coPoissonComplexDensity
      ((1 / 2 : ℂ) + (gamma : ℂ) * Complex.I) (Real.exp u)).im = 0 := by
  simpa only [OPICAFollowup.coPoissonRho, Complex.ofReal_zero, add_zero] using
    profile_critical_imaginary_density_zero gamma u hg hu hu2


theorem actual_four_sample_values (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    OPICAFollowup.coPoissonComplexDensity w.rho (Real.exp (profileQuarterU w j)) =
      profileQuarterDirection j * (OPICAFollowup.coPoissonKappa w.rho / (w.rho - 1 / 2)) *
        (profileQuarterP w j : ℂ) := profileQuarter_density w hh j

theorem actual_four_fixed_positive_unit_tests (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (j : Fin 4) :
    HasCompactSupport (profileQuarterTest w hh j) ∧
    (∀ x, 0 ≤ profileQuarterTest w hh j x) ∧
    (∫ x : ℝ, profileQuarterTest w hh j x) = 1 ∧
    tsupport (profileQuarterTest w hh j) ⊆ Ioo (1 : ℝ) 2 :=
  ⟨profileQuarterTest_compact w hh j, profileQuarterTest_nonneg w hh j,
    profileQuarterTest_integral w hh j, profileQuarterTest_support w hh j⟩

theorem actual_scaled_zero_measure_phase_margin (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (c : ℂ) :
    ∃ j : Fin 4, ((OPICAFollowup.zeroMeasure w.rho).scale c).rePart.integral
      (profileQuarterTest w hh j) ≤ -profileQuarterEta w * ‖c‖ / 2 :=
  profileQuarter_test_margin w hh c

theorem actual_four_observation_error_floor (w : ProfileWitness)
    (hh : 2 * Real.pi / Real.log 2 < profileGamma w) (c : ℂ) (a0 eps : ℝ)
    (ha0 : 0 < a0) (hc : a0 ≤ ‖c‖) (P : Fin 4 → ℝ) (hP : ∀ j, 0 ≤ P j)
    (herr : ∀ j, |P j - ((OPICAFollowup.zeroMeasure w.rho).scale c).rePart.integral
      (profileQuarterTest w hh j)| ≤ eps) : profileQuarterEta w * a0 / 2 ≤ eps :=
  profileQuarter_observation_error_floor w hh c a0 eps ha0 hc P hP herr

theorem at_most_n_one_sided_tests_control {m n : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ∃ a : Fin n → ℝ, a ≠ 0 ∧ ∀ i : Fin m, 0 ≤ F a i :=
  profile_at_most_n_linear_tests_cannot_exclude hn hm F


open OPICAFollowup.FiniteSpan

theorem actual_finite_zero_jet_covector_realization {n : ℕ}
    (basis : Fin n → List JetDatum) (hv : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (hind : LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (hv i)))) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ phi : 𝓢(ℝ, ℝ), HasCompactSupport phi ∧
      tsupport phi ⊆ Zeta23.OPICA.integerLatticeᶜ ∧ (∀ x, 0 ≤ phi x) ∧
      ∀ i, (zeroJetRealSpan (basis i)).integral phi = v i := by
  obtain ⟨phi, hp, hv⟩ := profile_actual_basis_positive_test_realization basis hv hind v
  exact ⟨phi, hp.1, hp.2.1, hp.2.2, hv⟩

theorem actual_n_plus_one_fixed_positive_test_margin {n : ℕ} (hn : 1 ≤ n)
    (basis : Fin n → List JetDatum) (hv : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (hind : LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (hv i)))) :
    ∃ tests : Fin (n + 1) → 𝓢(ℝ, ℝ), ∃ margin : ℝ, 0 < margin ∧
      (∀ j, HasCompactSupport (tests j) ∧ tsupport (tests j) ⊆ Zeta23.OPICA.integerLatticeᶜ ∧
        ∀ x, 0 ≤ tests j x) ∧
      (∀ j i, (zeroJetRealSpan (basis i)).integral (tests j) = profileSimplexDirection n j i) ∧
      (∀ a : EuclideanSpace ℝ (Fin n), ∃ j,
        (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).integral (tests j) ≤ -margin * ‖a‖) := by
  obtain ⟨tests, margin, hm, hp, hcov, hb, he⟩ := profile_actual_basis_adapted_tests basis hv hind
  exact ⟨tests, margin, hm, hp, hcov, hb⟩

theorem actual_canonical_three_phase_complete_tests {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (hk : (OPICAFollowup.spectralKappa rho).im ≠ 0) :
    ∃ tests : Fin 3 → 𝓢(ℝ, ℝ), ∃ margin : ℝ, 0 < margin ∧
      (∀ j, HasCompactSupport (tests j) ∧ tsupport (tests j) ⊆ Zeta23.OPICA.integerLatticeᶜ ∧
        ∀ x, 0 ≤ tests j x) ∧
      (∀ c : ℂ, ∃ j, ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral (tests j) ≤ -margin * ‖c‖) := by
  obtain ⟨tests, margin, hm, hp, hb, he⟩ := profile_canonical_three_physical_tests hz h0 h1 hk
  exact ⟨tests, margin, hm, hp, hb⟩

theorem actual_canonical_three_same_pairing_error_floor {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (hk : (OPICAFollowup.spectralKappa rho).im ≠ 0) :
    ∃ tests : Fin 3 → 𝓢(ℝ, ℝ), ∃ margin : ℝ, 0 < margin ∧
      (∀ j, profilePositiveOffLatticeTest (tests j)) ∧
      (∀ c : ℂ, ∀ a0 eps : ℝ, 0 < a0 → a0 ≤ ‖c‖ → ∀ P : Fin 3 → ℝ,
        (∀ j, 0 ≤ P j) →
        (∀ j, |P j - ((OPICAFollowup.zeroMeasure rho).scale c).rePart.integral (tests j)| ≤ eps) →
        margin * a0 ≤ eps) := by
  obtain ⟨tests, margin, hm, hp, hb, he⟩ := profile_canonical_three_physical_tests hz h0 h1 hk
  exact ⟨tests, margin, hm, hp, he⟩

theorem actual_canonical_Re_Im_pairing_dictionary {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (phi : 𝓢(ℝ, ℝ)) :
    (zeroJetRealSpan (OPICAFollowup.OffcriticalRealBasis.canonicalBasis rho 0)).integral phi =
      (OPICAFollowup.zeroMeasure rho).rePart.integral phi ∧
    (zeroJetRealSpan (OPICAFollowup.OffcriticalRealBasis.canonicalBasis rho 1)).integral phi =
      (OPICAFollowup.zeroMeasure rho).imPart.integral phi :=
  profile_canonical_basis_physical_pairings hz h0 h1 phi

end Zeta23.OPICARound2.Validation
#print axioms Zeta23.OPICARound2.profile_height_free_point_margin
#print axioms Zeta23.OPICARound2.Validation.literal_height_free_first_cell_point_consumer
#print axioms Zeta23.OPICARound2.Validation.actual_positive_first_cell_test_consumer
#print axioms Zeta23.OPICARound2.Validation.exact_factorial_margin_consumer
#print axioms Zeta23.OPICARound2.Validation.one_sided_n_linear_tests_counter_consumer

#print axioms Zeta23.OPICARound2.fixed_imaginary_direction_positive_test_margin

#print axioms Zeta23.OPICARound2.Validation.actual_density_derivative_budget_consumer

#print axioms Zeta23.OPICARound2.Validation.actual_native_imaginary_positive_test_consumer

#print axioms Zeta23.OPICARound2.Validation.same_fixed_actual_pairing_error_floor

#print axioms Zeta23.OPICARound2.Validation.actual_critical_line_imaginary_control

#print axioms Zeta23.OPICARound2.profile_four_positive_test_observability
#print axioms Zeta23.OPICARound2.Validation.actual_four_sample_values
#print axioms Zeta23.OPICARound2.Validation.actual_four_fixed_positive_unit_tests
#print axioms Zeta23.OPICARound2.Validation.actual_scaled_zero_measure_phase_margin
#print axioms Zeta23.OPICARound2.Validation.actual_four_observation_error_floor
#print axioms Zeta23.OPICARound2.Validation.at_most_n_one_sided_tests_control

#print axioms Zeta23.OPICARound2.phase_complete_positive_test_observability
#print axioms Zeta23.OPICARound2.profile_signed_nonnegative_of_positive_tests
#print axioms Zeta23.OPICARound2.profile_finite_cone_eq_univ
#print axioms Zeta23.OPICARound2.Validation.actual_finite_zero_jet_covector_realization
#print axioms Zeta23.OPICARound2.Validation.actual_n_plus_one_fixed_positive_test_margin
#print axioms Zeta23.OPICARound2.Validation.actual_canonical_three_phase_complete_tests
#print axioms Zeta23.OPICARound2.Validation.actual_canonical_three_same_pairing_error_floor
#print axioms Zeta23.OPICARound2.Validation.actual_canonical_Re_Im_pairing_dictionary


noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform SchwartzMap BigOperators
namespace Zeta23.OPICARound2.Validation
open QuadraticProfileRealification

theorem actual_deduplicated_real_block_source_consumer {r c : ℕ} (F : ProfileBlockFamily r c) :
    (∀ x : ℝ, |x| ≤ 1 → profileBlockH F x = cyclicVector) ∧
    (∃ C : MixedIndex r c → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ x : ℝ, 1 ≤ |x| →
      ∀ i, ‖profileBlockH F x i‖ ≤ C i * |x|^(-2:ℝ)) ∧
    (∀ i : MixedIndex r c, 𝓕 (fun x : ℝ => (profileBlockH F x i : ℂ)) =
      fun x : ℝ => (profileBlockH F x i : ℂ)) ∧
    Submodule.span ℝ (Set.range (fun n : Fin (Fintype.card (MixedIndex r c)) =>
      ((profileBlockKMatrix F)^(n.val+1)).mulVec cyclicVector)) = ⊤ := by
  have h := (finite_quadratic_profile_selfdual_obstruction F).1
  exact ⟨h.gap,h.tail,h.selfdual,h.cyclic⟩

theorem actual_real_block_physical_dictionary {r c : ℕ} (F : ProfileBlockFamily r c) (x : ℝ) :
    (∀ i : Fin r, profileBlockH F x (.inl i) =
      (1 - OPICAFollowup.finiteSumSrho (F.rhoReal i) |x| /
        OPICAFollowup.normalizationBrho (F.rhoReal i)).re) ∧
    (∀ i : Fin c, profileBlockH F x (.inr (i,0)) =
      (1 - OPICAFollowup.finiteSumSrho (F.rhoComplex i) |x| /
        OPICAFollowup.normalizationBrho (F.rhoComplex i)).re) ∧
    (∀ i : Fin c, profileBlockH F x (.inr (i,1)) =
      (1 - OPICAFollowup.finiteSumSrho (F.rhoComplex i) |x| /
        OPICAFollowup.normalizationBrho (F.rhoComplex i)).im) := by
  exact ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

theorem actual_finite_real_quadratic_integrability {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hA : A.IsSymm) :
    Integrable (fun x : ℝ => ∑ i : MixedIndex r c, ∑ j : MixedIndex r c,
      profileBlockH F x i * A i j * profileBlockH F x j) := by
  have he : (fun x : ℝ => ∑ i : MixedIndex r c, ∑ j : MixedIndex r c,
      profileBlockH F x i * A i j * profileBlockH F x j) = profileRealQuadratic F A := by
    funext x
    unfold profileRealQuadratic Matrix.mulVec dotProduct
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact ((finite_quadratic_profile_selfdual_obstruction F).2.1 A hA).1

theorem actual_finite_symmetric_quadratic_rigidity {r c : ℕ} (F : ProfileBlockFamily r c)
    (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hA : A.IsSymm)
    (hsd : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, ((dotProduct (profileBlockH F x) (A.mulVec (profileBlockH F x)) : ℝ) : ℂ) *
        (𝓕 φ : 𝓢(ℝ,ℂ)) x) =
      ∫ x, ((dotProduct (profileBlockH F x) (A.mulVec (profileBlockH F x)) : ℝ) : ℂ) * φ x) : A = 0 :=
  ((finite_quadratic_profile_selfdual_obstruction F).2.1 A hA).2 hsd

theorem actual_quadratic_arbitrary_tempered_lattice_measure_control {r c : ℕ}
    (F : ProfileBlockFamily r c) (A : Matrix (MixedIndex r c) (MixedIndex r c) ℝ) (hA : A.IsSymm)
    (sigma : OPICAFollowup.LocallyFiniteComplexMeasure) (T S : TemperedDistribution ℝ ℂ)
    (hsigma : sigma.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0)
    (hT : OPICAFollowup.TemperedLatticeBridge.ExtendsCompactPairing sigma T) (hS : 𝓕 S = S)
    (hRepair : ∀ φ : 𝓢(ℝ,ℂ),
      (∫ x, (profileRealQuadratic F A x : ℂ) * (𝓕 φ : 𝓢(ℝ,ℂ)) x) + S (𝓕 φ) + T (𝓕 φ) =
        (∫ x, (profileRealQuadratic F A x : ℂ) * φ x) + S φ + T φ) : A = 0 :=
  (finite_quadratic_profile_selfdual_obstruction F).2.2 A hA sigma T S hsigma hT hS hRepair

theorem actual_all_order_source_asymptotic_consumer {rho : ℂ} (hz : riemannZeta rho = 0)
    (h0 : 0 < rho.re) (h1 : rho.re < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖OPICAFollowup.zeroProfile rho x - profileZeroEMTerms rho N |x|‖ ≤ C * |x|^(-(N:ℝ)-1) :=
  profile_zeroProfile_all_order_asymptotic hz h0 h1 N hN

theorem actual_integer_samples_span_consumer {d : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (hinj : Function.Injective (fun i => OPICAFollowup.spectralKappa (rho i))) :
    Submodule.span ℂ (Set.range (fun n : ℕ => fun i => OPICAFollowup.zeroProfile (rho i) ((n+1:ℕ):ℝ))) = ⊤ :=
  profile_zero_integer_samples_span rho hz h0 h1 hinj

theorem actual_odd_projected_jump_consumer {d j : ℕ} (rho : Fin d → ℂ)
    (hz : ∀ i, riemannZeta (rho i) = 0) (h0 : ∀ i, 0 < (rho i).re) (h1 : ∀ i, (rho i).re < 1)
    (A : Matrix (Fin d) (Fin d) ℂ) (hSym : A.IsSymm)
    (hA : ∀ r : ℕ, r < j → A.mulVec (profilePowerRow (fun i => OPICAFollowup.spectralKappa (rho i)) r) = 0)
    (n : ℕ) :
    iteratedDeriv (2*j+1) (profileQuadraticCell rho A (n+1)) ((n+1:ℕ):ℝ) -
      iteratedDeriv (2*j+1) (profileQuadraticCell rho A n) ((n+1:ℕ):ℝ) =
    (2*(-1:ℂ)^(j+1)/((n+1:ℕ):ℂ)^(2*j+2)) *
      dotProduct (fun i => OPICAFollowup.zeroProfile (rho i) ((n+1:ℕ):ℝ))
        (A.mulVec (profilePowerRow (fun i => OPICAFollowup.spectralKappa (rho i)) j)) :=
  profile_actual_quadratic_odd_jump rho h0 h1 (fun i => OPICAFollowup.zero_ne_half (hz i)) A hSym hA n

end Zeta23.OPICARound2.Validation
#print axioms Zeta23.OPICARound2.finite_quadratic_profile_selfdual_obstruction
#print axioms Zeta23.OPICARound2.Validation.actual_deduplicated_real_block_source_consumer
#print axioms Zeta23.OPICARound2.Validation.actual_real_block_physical_dictionary
#print axioms Zeta23.OPICARound2.Validation.actual_finite_real_quadratic_integrability
#print axioms Zeta23.OPICARound2.Validation.actual_finite_symmetric_quadratic_rigidity
#print axioms Zeta23.OPICARound2.Validation.actual_quadratic_arbitrary_tempered_lattice_measure_control
#print axioms Zeta23.OPICARound2.Validation.actual_all_order_source_asymptotic_consumer
#print axioms Zeta23.OPICARound2.Validation.actual_integer_samples_span_consumer
#print axioms Zeta23.OPICARound2.Validation.actual_odd_projected_jump_consumer

