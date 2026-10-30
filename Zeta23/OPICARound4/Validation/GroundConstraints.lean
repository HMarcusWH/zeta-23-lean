import Zeta23.OPICARound4.JointGroundConstraints

noncomputable section
namespace Zeta23.OPICARound4.Validation
open CCM OPICARound3 MeasureTheory
open scoped BigOperators ComplexConjugate Interval

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- The complete arithmetic split is tested on an arbitrary actual input,
without assuming any spectral response or prime-discrepancy bound. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u = nativeArchContinuumRow L K u -
      ((∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * correctedSourceTest L K u (Real.log q)) -
        ∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * correctedSourceTest L K u y) :=
  native_signed_source_decomposition hL K hK u

example {L : ℝ} (hL : 0 < L) (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    nativeSignedPrimeDiscrepancy L K u =
      -∫ y in (0 : ℝ)..L,
        ((Chebyshev.psi (Real.exp y) - Real.exp y : ℝ) : ℂ) * (Real.exp (-y / 2) : ℂ) *
          (correctedSourceTestDerivative L K u y - correctedSourceTest L K u y / 2) :=
  native_signed_discrepancy_integral hL K u

/-- Signed +1 normalization, not unit-norm normalization. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs
    nativeSignedPrimeDiscrepancy L K r = nativeArchContinuumRow L K r - 1 ∧
      nativeGroundPrimePairing L K r = -1 - nativeGroundArchPairing L K r := by
  exact ⟨(actual_even_ground_signed_discrepancy hL K hK hs).2.1,
    (actual_even_ground_signed_discrepancy hL K hK hs).2.2.1⟩

/-- The reciprocal EVEN input of the odd response has source value -1.
It is neither the odd eigenray nor an arbitrary even Riesz input. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    let v := nativeOddReciprocalInput hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs
    poleNeutralCorrectedCubicSource L K v = -1 ∧
      nativeSignedPrimeDiscrepancy L K v = nativeArchContinuumRow L K v + 1 ∧
      nativeGroundPrimePairing L K v = 1 - nativeGroundArchPairing L K v := by
  have h := actual_odd_ground_reciprocal_discrepancy hL K hK hs
  exact ⟨h.1, h.2.1, h.2.2.1⟩

example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    poleNeutralOddRayleighBottom L K hL hK - poleNeutralEvenRayleighBottom L K hL hK ≤
      nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re / 2 :=
  actual_even_ground_signed_budget_feasibility hL K hK hs

example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralEvenRayleighBottom L K hL hK - poleNeutralOddRayleighBottom L K hL hK ≤
      nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ -
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re / 2 :=
  actual_odd_ground_signed_budget_feasibility hL K hK hs

example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs
    (poleNeutralOddRayleighBottom L K hL hK - poleNeutralEvenRayleighBottom L K hL hK) *
      ‖poleNeutralIndexLinearMap hL K r‖ ^ 2 ≤
        (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K r.val)).re ∧
    0 < (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K r.val)).re :=
  actual_even_ground_ray_moment_feasibility hL K hK hs

/-- Absolute negativity stays on the actual normalized even eigenray. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (c : NativeStrictEvenGroundConstraints hL K hK) :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) c.strict
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin r.val.val) r.val.val).re < 0 := by
  dsimp only
  rw [c.absolute_energy]
  exact mul_neg_of_neg_of_pos c.even_negative (sq_pos_of_pos (norm_pos_iff.mpr c.eigen.1))

/-- In the odd branch the actual odd eigenray, not the reciprocal input,
carries the negative energy. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (c : NativeStrictOddGroundConstraints hL K hK) :
    let w := poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) c.strict
    (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin w.val.val) w.val.val).re < 0 := by
  dsimp only
  rw [c.absolute_energy]
  exact mul_neg_of_neg_of_pos c.odd_negative (sq_pos_of_pos (norm_pos_iff.mpr c.eigen.1))

/-- Equality is admitted without simplicity or nonvanishing source. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (ht : poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK)
    (hn : poleNeutralEvenRayleighBottom L K hL hK < 0) : NativeTiedGroundConstraints hL K hK :=
  native_tied_ground_constraints hL K hK ht hn

/-- Positivity is of the shifted operators; it does not assert positivity
of the negative absolute canonical source energy. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (c : NativeTiedGroundConstraints hL K hK) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralEvenSubspace L K)
      (poleNeutralEvenShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)) ∧
    LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralOddSubspace L K)
      (poleNeutralOddShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)) :=
  c.shifted_positive

/-- No strict branch is silently selected by the common-cutoff producer. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :
    NativeStrictEvenGroundConstraints hL K hK ∨
      NativeStrictOddGroundConstraints hL K hK ∨ NativeTiedGroundConstraints hL K hK :=
  joint_ground_constraints_of_both_negative hL K hK hboth

example (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ ∃ hL : 0 < L, ∃ K : ℕ, ∃ hK : 3 ≤ K,
      BothNeutralNegative L K ∧
        (NativeStrictEvenGroundConstraints hL K hK ∨
          NativeStrictOddGroundConstraints hL K hK ∨ NativeTiedGroundConstraints hL K hK) :=
  cofinally_joint_ground_constraints_of_off_line_zero ρ hoff R

end Zeta23.OPICARound4.Validation
