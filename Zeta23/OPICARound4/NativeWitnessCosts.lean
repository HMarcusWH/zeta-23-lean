import Zeta23.OPICARound4.WitnessNorms
import Zeta23.OPICARound3.NewbornSource

noncomputable section

namespace Zeta23.OPICARound4

open CCM OPICARound3

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- The existing physical inverse constant is two, independent of cutoff. -/
theorem native_index_inverse_cost {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K) (w : poleNeutralOddSubspace L K) :
    ‖(poleNeutralIndexEquiv hL K hK).symm w‖ ≤ 2 * ‖w‖ :=
  poleNeutralIndexInverse_norm_le_two hL K hK w

/-- The physical bottom is bounded by the quotient of this same nonzero vector. -/
theorem native_even_bottom_le_quotient {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralEvenSubspace L K) (hw : w ≠ 0) :
    poleNeutralEvenRayleighBottom L K hL hK ≤
      rayleighEnergy (poleNeutralEvenCompressedCanonical L K) w := by
  have h := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL K hK w
  exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hw))).mpr h

theorem native_odd_bottom_le_quotient {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K) (hw : w ≠ 0) :
    poleNeutralOddRayleighBottom L K hL hK ≤
      rayleighEnergy (poleNeutralOddCompressedCanonical L K) w := by
  have h := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK w
  exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hw))).mpr h

/-- The quotient adapter covers both actual parity carriers at the same L,K. -/
theorem native_bottom_le_quotient (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : nativePoleNeutralParitySpace p L K) (hw : w ≠ 0) :
    (match p with
    | .even => poleNeutralEvenRayleighBottom L K hL hK
    | .odd => poleNeutralOddRayleighBottom L K hL hK) ≤
      rayleighEnergy (nativePoleNeutralParityCanonical p L K) w := by
  cases p
  · exact native_even_bottom_le_quotient hL K hK w hw
  · exact native_odd_bottom_le_quotient hL K hK w hw

/-- The actual D05 witness pays its full norm before producing a ground bound. -/
theorem newborn_bottom_le_normalized_energy (p : ReversalParity) {L : ℝ}
    (hL : 0 < L) (K : ℕ) (s : NativeNewbornSourceWitness p L K hL) :
    (match p with
    | .even => poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
    | .odd => poleNeutralOddRayleighBottom L K hL s.cutoff_lower) ≤
      (inner ℂ (nativePoleNeutralParityCanonical p L K s.w) s.w).re / ‖s.w‖ ^ 2 ∧
    (inner ℂ (nativePoleNeutralParityCanonical p L K s.w) s.w).re / ‖s.w‖ ^ 2 < 0 := by
  cases p
  · exact ⟨native_even_bottom_le_quotient hL K s.cutoff_lower s.w s.w_ne_zero,
      div_neg_of_neg_of_pos s.native_negative (sq_pos_of_pos (norm_pos_iff.mpr s.w_ne_zero))⟩
  · exact ⟨native_odd_bottom_le_quotient hL K s.cutoff_lower s.w s.w_ne_zero,
      div_neg_of_neg_of_pos s.native_negative (sq_pos_of_pos (norm_pos_iff.mpr s.w_ne_zero))⟩

/-- The actual Schur-created vector retains both regular and resonant norm costs. -/
theorem newborn_witness_norm_branches (p : ReversalParity) {L : ℝ}
    (hL : 0 < L) (K : ℕ) (s : NativeNewbornSourceWitness p L K hL) :
    (s.w = resonantSchurWitness (newbornCutoffInclusion p L K)
        (nativePoleNeutralParityCanonical p L K) s.e ∧
      ‖s.w‖ ^ 2 = 1 +
        ‖(resonantSchurCoefficient (newbornCutoffInclusion p L K)
          (nativePoleNeutralParityCanonical p L K) s.e : ℂ)‖ ^ 2 *
        ‖(predecessorBlock (newbornCutoffInclusion p L K)
          (nativePoleNeutralParityCanonical p L K)).ker.starProjection
          ((newbornCutoffInclusion p L K).toLinearMap.adjoint
            (nativePoleNeutralParityCanonical p L K s.e.val))‖ ^ 2) ∨
    ∃ hb, s.w = regularSchurWitness (newbornCutoffInclusion p L K)
        (nativePoleNeutralParityCanonical p L K) s.e hb ∧
      ‖s.w‖ ^ 2 = 1 +
        ‖kernelSafeResponse (predecessorBlock (newbornCutoffInclusion p L K)
          (nativePoleNeutralParityCanonical p L K)) _ hb‖ ^ 2 := by
  rcases s.realization with ⟨_, hw, _⟩ | ⟨hb, _, hw, _⟩
  · left
    refine ⟨hw, ?_⟩
    rw [hw, resonant_witness_norm_sq]
    have he : ‖(s.e : nativePoleNeutralParitySpace p L K)‖ = 1 := s.e_unit
    rw [he, one_pow]
  · right
    refine ⟨hb, hw, ?_⟩
    rw [hw, regular_witness_norm_sq]
    have he : ‖(s.e : nativePoleNeutralParitySpace p L K)‖ = 1 := s.e_unit
    rw [he, one_pow]

/-- Select a genuine ground eigenmode from a negative even witness.
The new mode shares L,K and its bottom, but is not identified with the witness. -/
theorem even_negative_witness_ground {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralEvenSubspace L K)
    (hneg : (inner ℂ (poleNeutralEvenCompressedCanonical L K w) w).re < 0) :
    ∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K u =
        (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u ∧
      poleNeutralEvenRayleighBottom L K hL hK ≤
        rayleighEnergy (poleNeutralEvenCompressedCanonical L K) w ∧
      poleNeutralEvenRayleighBottom L K hL hK < 0 := by
  have hw : w ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hneg
    change (inner ℂ (0 : EuclideanSpace ℂ (Fin (2 * K + 1))) 0).re < 0 at hneg
    simpa using hneg
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K hK
  have hb := native_even_bottom_le_quotient hL K hK w hw
  exact ⟨u, hu0, hu, hb, lt_of_le_of_lt hb
    (div_neg_of_neg_of_pos hneg (sq_pos_of_pos (norm_pos_iff.mpr hw)))⟩

theorem odd_negative_witness_ground {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K)
    (hneg : (inner ℂ (poleNeutralOddCompressedCanonical L K w) w).re < 0) :
    ∃ u : poleNeutralOddSubspace L K, u ≠ 0 ∧
      poleNeutralOddCompressedCanonical L K u =
        (poleNeutralOddRayleighBottom L K hL hK : ℂ) • u ∧
      poleNeutralOddRayleighBottom L K hL hK ≤
        rayleighEnergy (poleNeutralOddCompressedCanonical L K) w ∧
      poleNeutralOddRayleighBottom L K hL hK < 0 := by
  have hw : w ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hneg
    change (inner ℂ (0 : EuclideanSpace ℂ (Fin (2 * K + 1))) 0).re < 0 at hneg
    simpa using hneg
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K hK
  have hb := native_odd_bottom_le_quotient hL K hK w hw
  exact ⟨u, hu0, hu, hb, lt_of_le_of_lt hb
    (div_neg_of_neg_of_pos hneg (sq_pos_of_pos (norm_pos_iff.mpr hw)))⟩

/-- Common-cutoff selection retains the shared-ground branch. Strictly lower
grounds have their genuine shifted source equality; no genericity is assumed. -/
theorem common_cutoff_negative_ground_alternatives {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :
    (poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK ∧
      poleNeutralEvenRayleighBottom L K hL hK < 0 ∧
      ∃ hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK,
        poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs) = 1) ∨
    (poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK ∧
      poleNeutralOddRayleighBottom L K hL hK < 0 ∧
      ∃ hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK,
        poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs) = 1) ∨
    (poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK ∧
      poleNeutralEvenRayleighBottom L K hL hK < 0) := by
  obtain ⟨we, hwe⟩ := hboth.1
  obtain ⟨wo, hwo⟩ := hboth.2
  obtain ⟨ue, hue0, hue, _, hbe⟩ := even_negative_witness_ground hL K hK we hwe
  obtain ⟨uo, huo0, huo, _, hbo⟩ := odd_negative_witness_ground hL K hK wo hwo
  rcases lt_trichotomy (poleNeutralEvenRayleighBottom L K hL hK)
    (poleNeutralOddRayleighBottom L K hL hK) with hs | hs | hs
  · exact Or.inl ⟨hs, hbe, hs,
      poleNeutral_even_eigen_shiftedRay_source_eq_one hL K hK _ hs ue hue0 hue⟩
  · exact Or.inr (Or.inr ⟨hs, hbe⟩)
  · exact Or.inr (Or.inl ⟨hs, hbo, hs,
      poleNeutral_odd_eigen_adjointRay_pairing_eq_one hL K hK _ hs uo huo0 huo⟩)

/-- Below the opposite bottom, even eigenvectors occupy the same source ray.
This is a conditional simplicity statement, not universal spectral separation. -/
theorem even_eigenvectors_source_collinear {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK)
    (u v : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hv : poleNeutralEvenCompressedCanonical L K v = (lam : ℂ) • v) :
    poleNeutralCorrectedCubicSource L K v • u =
      poleNeutralCorrectedCubicSource L K u • v := by
  have he := poleNeutral_even_eigenvector_eq_source_smul_shiftedRay hL K hK lam hlam u hu
  have hf := poleNeutral_even_eigenvector_eq_source_smul_shiftedRay hL K hK lam hlam v hv
  calc
    _ = poleNeutralCorrectedCubicSource L K v •
        (poleNeutralCorrectedCubicSource L K u • poleNeutralEvenShiftedRay hL K hK lam hlam) :=
      congrArg (fun z : poleNeutralEvenSubspace L K => poleNeutralCorrectedCubicSource L K v • z) he
    _ = poleNeutralCorrectedCubicSource L K u •
        (poleNeutralCorrectedCubicSource L K v • poleNeutralEvenShiftedRay hL K hK lam hlam) :=
      smul_comm _ _ _
    _ = _ := congrArg
      (fun z : poleNeutralEvenSubspace L K => poleNeutralCorrectedCubicSource L K u • z) hf.symm

theorem odd_eigenvectors_source_collinear {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    (u v : poleNeutralOddSubspace L K)
    (hu : poleNeutralOddCompressedCanonical L K u = (lam : ℂ) • u)
    (hv : poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v) :
    poleNeutralCubicPairingFunctional L K v • u =
      poleNeutralCubicPairingFunctional L K u • v := by
  have he := poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay hL K hK lam hlam u hu
  have hf := poleNeutral_odd_eigenvector_eq_pairing_smul_adjointRay hL K hK lam hlam v hv
  calc
    _ = poleNeutralCubicPairingFunctional L K v •
        (poleNeutralCubicPairingFunctional L K u • poleNeutralOddAdjointShiftedRay hL K hK lam hlam) :=
      congrArg (fun z : poleNeutralOddSubspace L K => poleNeutralCubicPairingFunctional L K v • z) he
    _ = poleNeutralCubicPairingFunctional L K u •
        (poleNeutralCubicPairingFunctional L K v • poleNeutralOddAdjointShiftedRay hL K hK lam hlam) :=
      smul_comm _ _ _
    _ = _ := congrArg
      (fun z : poleNeutralOddSubspace L K => poleNeutralCubicPairingFunctional L K u • z) hf.symm

end Zeta23.OPICARound4
