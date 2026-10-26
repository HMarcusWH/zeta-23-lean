import Zeta23.OPICARound2.DualCertificates

noncomputable section

open Set MeasureTheory Matrix
open scoped Topology BigOperators ComplexConjugate ComplexOrder

namespace Zeta23.OPICARound2.Validation

theorem expected_laplace_jet_entries {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (p q : LaplaceJetIndex m) :
    inner ℂ
      (CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)
      (CCM.nativeCausalExponentialWitness (nodes q.1) (hpos q.1) q.2.val) =
      ((p.2.val + q.2.val).factorial : ℂ) /
        (nodes p.1 + conj (nodes q.1)) ^ (p.2.val + q.2.val + 1) :=
  laplaceJetGram_entry nodes hpos m p q

theorem domain_laplace_jet_causal_profile {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (p : LaplaceJetIndex m) :
    (laplaceJetWitness nodes hpos m p : ProbeL2) =ᵐ[volume] fun t : ℝ =>
      (Ici (0 : ℝ)).indicator
        (fun t : ℝ => (t : ℂ) ^ p.2.val * Complex.exp (-conj (nodes p.1) * (t : ℂ))) t :=
  CCM.nativeCausalExponentialPolynomialL2_coeFn (nodes p.1) (hpos p.1) p.2.val

theorem control_repeated_nodes_singular {r : ℕ} (nodes : Fin r → ℂ)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) {i j : Fin r}
    (hij : i ≠ j) (hnode : nodes i = nodes j) (hi : 0 < m i) (hj : 0 < m j) :
    ¬(Matrix.gram ℂ (fun p : LaplaceJetIndex m =>
      CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)).PosDef ∧
    (Matrix.gram ℂ (fun p : LaplaceJetIndex m =>
      CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)).det = 0 :=
  ⟨laplaceJetGram_not_posDef_of_repeated_nodes nodes hpos m hij hnode hi hj,
    laplaceJetGram_det_zero_of_repeated_nodes nodes hpos m hij hnode hi hj⟩

#print axioms Zeta23.OPICARound2.laplaceJetGram_entry
#print axioms Zeta23.OPICARound2.laplaceJetGram_det_zero_of_repeated_nodes

theorem expected_common_denominator_basis_invertible {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualCoefficientMatrix m (dualPoleFamily nodes m)).det ≠ 0 :=
  dualPoleCoefficient_det_ne_zero nodes hnodes m

theorem expected_pole_jet_triangular_determinant {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (m : Fin r → ℕ) :
    (dualPoleReversedEvaluation nodes m).det =
      ∏ i : Fin r, (∏ j ∈ Finset.univ.erase i, (nodes i - nodes j) ^ m j) ^ m i :=
  dualPoleReversedEvaluation_det nodes hnodes m

theorem expected_reciprocal_ordinary_jets (a z : ℂ) (l k : ℕ) :
    iteratedDeriv k (dualRationalColumn a l) z =
      ((-1 : ℂ) ^ k / (l.factorial : ℂ)) *
        ((k + l).factorial : ℂ) / (z - a) ^ (k + l + 1) := dualRationalColumn_deriv a l k z

theorem domain_rational_column_literal (a z : ℂ) (l : ℕ) :
    dualRationalColumn a l z = ((z - a) ^ (l + 1))⁻¹ := dualRationalColumn_eq a l z

#print axioms Zeta23.OPICARound2.dualPoleCoefficient_det_ne_zero
#print axioms Zeta23.OPICARound2.dualPoleEvaluation_det_norm
#print axioms Zeta23.OPICARound2.dualRationalColumn_deriv

theorem expected_actual_jet_positive {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) :
    (Matrix.gram ℂ (fun p : (i : Fin r) × Fin (m i) =>
      CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)).PosDef :=
  laplaceJetGram_posDef nodes hnodes hpos m

theorem expected_native_inverse_is_justified {r : ℕ} (nodes : Fin r → ℂ)
    (hnodes : Function.Injective nodes) (hpos : ∀ i, 0 < (nodes i).re)
    (m : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) :
    (Matrix.gram ℂ (fun p : (i : Fin r) × Fin (m i) =>
      CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)).det ≠ 0 :=
  laplaceJetGram_det_ne_zero nodes hnodes hpos m

theorem expected_actual_ordinary_matrix_product {r : ℕ} (x y : Fin r → ℂ)
    (m : Fin r → ℕ) (hxy : ∀ i j, x i ≠ y j) :
    (dualOrdinaryHermiteEvaluation x m (dualPoleFamily y m)).transpose =
      dualMultiplicationJet x m (dualCommonDenominator y m) * dualOrdinaryRational x y m :=
  dualOrdinary_product_matrix x y m hxy

#print axioms Zeta23.OPICARound2.laplaceJetGram_posDef
#print axioms Zeta23.OPICARound2.dualOrdinary_product_matrix

theorem expected_p17_complete {r : ℕ} (nodes : Fin r → ℂ) (hnodes : Function.Injective nodes)
    (hpos : ∀ i, 0 < (nodes i).re) (m : Fin r → ℕ) (hm : ∀ i, 1 ≤ m i) :
    (∀ p q : (i : Fin r) × Fin (m i),
      inner ℂ (CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)
        (CCM.nativeCausalExponentialWitness (nodes q.1) (hpos q.1) q.2.val) =
          ((p.2.val + q.2.val).factorial : ℂ) /
            (nodes p.1 + conj (nodes q.1)) ^ (p.2.val + q.2.val + 1)) ∧
    (Matrix.gram ℂ (fun p : (i : Fin r) × Fin (m i) =>
      CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)).PosDef ∧
    (Matrix.gram ℂ (fun p : (i : Fin r) × Fin (m i) =>
      CCM.nativeCausalExponentialWitness (nodes p.1) (hpos p.1) p.2.val)).det =
      (((∏ i : Fin r, ∏ k : Fin (m i), (k.val.factorial : ℝ) ^ 2) *
        (∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i - nodes j‖ ^ (2 * m i * m j))) /
          ((∏ i : Fin r, (2 * (nodes i).re) ^ (m i ^ 2)) *
            (∏ j : Fin r, ∏ i ∈ Finset.Iio j, ‖nodes i + conj (nodes j)‖ ^ (2 * m i * m j))) : ℝ) := by
  exact laplace_jet_gram nodes hnodes hpos m hm

theorem control_p17_duplicate_half_nodes :
    (laplaceJetGram (fun _ : Fin 2 => (1 / 2 : ℂ)) (fun _ => by norm_num) (fun _ => 1)).det = 0 :=
  laplaceJetGram_det_zero_of_repeated_nodes _ _ _ (i := 0) (j := 1)
    (by decide) rfl (by norm_num) (by norm_num)

theorem control_p17_ordinary_factorials :
    inner ℂ (CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) 2)
      (CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) 2) = 24 := by
  rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment, nativeExponential_moment_shift,
    nativeExponential_zero_moment _ _ _ (by norm_num)]
  norm_num [map_ofNat]

theorem control_p17_positive_degree_zero_cost :
    ‖CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) 0‖ ^ 2 = 1 := by
  convert probeLaplaceWitness_norm_sq (1 / 2 : ℂ) (by norm_num) using 1 <;> norm_num

#print axioms Zeta23.OPICARound2.laplace_jet_gram

theorem expected_p18_native_distance {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    star (dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ⬝ᵥ
      ((laplaceJetGram (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m)⁻¹ *ᵥ
        dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ≤
      ((Metric.infDist probeTarget
        (closure (Set.range (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)))) ^ 2 : ℝ) : ℂ) := by
  rcases simultaneous_zero_distance rho hdistinct hright m hm hallow with ⟨_, _, _, h, _⟩
  exact h

theorem expected_p18_weight_nonnegative {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) :
    0 ≤ (star (dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget) ⬝ᵥ
      ((laplaceJetGram (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m)⁻¹ *ᵥ
        dualJetPairings (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget)).re := by
  rcases simultaneous_zero_distance rho hdistinct hright m hm hallow with ⟨_, _, h, _, _⟩
  exact h

theorem domain_p18_actual_adjoint_kernel {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ))
    {f : CausalProbeL2} (hf : f ∈ dualJetSpace (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m) :
    CCM.nativeDampedCompletionCausalL2Adjoint 0 (le_rfl) f = 0 := by
  rcases simultaneous_zero_distance rho hdistinct hright m hm hallow with ⟨h, _, _, _, _⟩
  exact h hf

theorem expected_p18_true_target_jet {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) (p : LaplaceJetIndex m) :
    inner ℂ (CCM.nativeCausalExponentialWitness ((rho p.1 : ℂ) - 1 / 2)
      (dualZeroNodes_positive rho hright p.1) p.2.val) probeTarget =
      (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (probeLaplace probeV) ((rho p.1 : ℂ) - 1 / 2) := by
  rcases simultaneous_zero_distance rho hdistinct hright m hm hallow with ⟨_, h, _, _, _⟩
  exact h p

theorem domain_p18_physical_target_moment {r : ℕ} (rho : Fin r → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re) (m : Fin r → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) (p : LaplaceJetIndex m) :
    (∫ t : ℝ, (t : ℂ) ^ p.2.val * Complex.exp (-((rho p.1 : ℂ) - 1 / 2) * (t : ℂ)) * probeV t) =
      (-1 : ℂ) ^ p.2.val * iteratedDeriv p.2.val (probeLaplace probeV) ((rho p.1 : ℂ) - 1 / 2) := by
  have h := expected_p18_true_target_jet rho hdistinct hright m hm hallow p
  rw [CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment ((rho p.1 : ℂ) - 1 / 2)
    (dualZeroNodes_positive rho hright p.1) p.2.val probeTarget, CCM.nativeCausalLaplaceMoment] at h
  have he : (∫ t : ℝ, (t : ℂ) ^ p.2.val * Complex.exp (-((rho p.1 : ℂ) - 1 / 2) * (t : ℂ)) *
      (probeTarget : ProbeL2) t) =
      ∫ t : ℝ, (t : ℂ) ^ p.2.val * Complex.exp (-((rho p.1 : ℂ) - 1 / 2) * (t : ℂ)) * probeV t := by
    apply integral_congr_ae
    filter_upwards [probeTarget_coeFn] with t ht
    rw [ht]
  exact he.symm.trans h

theorem expected_p18_adding_actual_witnesses {r s : ℕ}
    (rho : Fin r → zetaZeroConfig.carrier) (rho' : Fin s → zetaZeroConfig.carrier)
    (hdistinct : Function.Injective (fun i => (rho i : ℂ)))
    (hdistinct' : Function.Injective (fun i => (rho' i : ℂ)))
    (hright : ∀ i, (1 / 2 : ℝ) < (rho i : ℂ).re)
    (hright' : ∀ i, (1 / 2 : ℝ) < (rho' i : ℂ).re)
    (m : Fin r → ℕ) (m' : Fin s → ℕ) (hm : ∀ i, 1 ≤ m i) (hm' : ∀ i, 1 ≤ m' i)
    (hallow : ∀ i, m i ≤ zeroMult (rho i : ℂ)) (hallow' : ∀ i, m' i ≤ zeroMult (rho' i : ℂ))
    (e : LaplaceJetIndex m → LaplaceJetIndex m') (he : Function.Injective e)
    (heNode : ∀ p, (rho' (e p).1 : ℂ) - 1 / 2 = (rho p.1 : ℂ) - 1 / 2)
    (heOrder : ∀ p, (e p).2.val = p.2.val) :
    dualJetBound (dualZeroNodes rho) (dualZeroNodes_positive rho hright) m probeTarget ≤
      dualJetBound (dualZeroNodes rho') (dualZeroNodes_positive rho' hright') m' probeTarget ∧
    dualJetBound (dualZeroNodes rho') (dualZeroNodes_positive rho' hright') m' probeTarget ≤
      Metric.infDist probeTarget (closure (Set.range (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)))) ^ 2 := by
  rcases simultaneous_zero_distance rho hdistinct hright m hm hallow with ⟨_, _, _, _, h⟩
  exact h s rho' hdistinct' hright' m' hm' hallow' e he heNode heOrder

theorem control_p18_laguerre_all_orders (a : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (Matrix.gram ℂ (fun p : (i : Fin 1) × Fin n =>
      CCM.nativeCausalExponentialWitness a ha p.2.val)).det /
      (Matrix.gram ℂ (fun p : (i : Fin 1) × Fin (n + 1) =>
        CCM.nativeCausalExponentialWitness a ha p.2.val)).det =
        (((‖OPICAFollowup.monicLaguerreTailL2 n a 0 ha‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
  dualSingleNativeGram_ratio_laguerre a ha n

#print axioms Zeta23.OPICARound2.simultaneous_zero_distance
#print axioms Zeta23.OPICARound2.dualSingleNativeGram_ratio_laguerre

end Zeta23.OPICARound2.Validation
