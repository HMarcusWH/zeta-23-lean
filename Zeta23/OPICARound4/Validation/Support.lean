import Zeta23.OPICARound4.NativeWitnessCosts
import Zeta23.OPICARound4.SourceDiscrepancy
import Zeta23.OPICARound4.AbsoluteAnchor
import Zeta23.OPICARound4.TraceMetric
import Zeta23.OPICARound4.NegativeIndex
import Zeta23.OPICARound4.SignedSpectral
import Zeta23.OPICARound4.OperatorSignedBound
import Zeta23.OPICARound4.RegularCells.SourceSupport

noncomputable section
namespace Zeta23.OPICARound4.Validation
open CCM OPICARound3
open scoped BigOperators

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

theorem native_inverse_cost_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K) (w : poleNeutralOddSubspace L K) :
    ‖(poleNeutralIndexEquiv hL K hK).symm w‖ ≤ 2 * ‖w‖ :=
  native_index_inverse_cost hL K hK w

theorem even_physical_quotient_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralEvenSubspace L K) (hw : w ≠ 0) :
    poleNeutralEvenRayleighBottom L K hL hK ≤
      (inner ℂ (poleNeutralEvenCompressedCanonical L K w) w).re / ‖w‖ ^ 2 :=
  native_even_bottom_le_quotient hL K hK w hw

theorem odd_physical_quotient_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (w : poleNeutralOddSubspace L K) (hw : w ≠ 0) :
    poleNeutralOddRayleighBottom L K hL hK ≤
      (inner ℂ (poleNeutralOddCompressedCanonical L K w) w).re / ‖w‖ ^ 2 :=
  native_odd_bottom_le_quotient hL K hK w hw

theorem native_newborn_normalized_cost_consumer (p : ReversalParity) {L : ℝ}
    (hL : 0 < L) (K : ℕ) (s : NativeNewbornSourceWitness p L K hL) :
    (match p with
    | .even => poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
    | .odd => poleNeutralOddRayleighBottom L K hL s.cutoff_lower) ≤
      (inner ℂ (nativePoleNeutralParityCanonical p L K s.w) s.w).re / ‖s.w‖ ^ 2 ∧
    (inner ℂ (nativePoleNeutralParityCanonical p L K s.w) s.w).re / ‖s.w‖ ^ 2 < 0 :=
  newborn_bottom_le_normalized_energy p hL K s

/-- Independent common-cutoff consumer, retaining the shared-negative-ground
alternative and both actual source orientations at that same cutoff. -/
theorem common_cutoff_source_or_shared_ground_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :
    (poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK ∧
      poleNeutralEvenRayleighBottom L K hL hK < 0) ∨
    (∃ lam : ℝ, lam < 0 ∧ ∃ hs : lam < poleNeutralOddRayleighBottom L K hL hK,
      poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hs) = 1) ∨
    (∃ lam : ℝ, lam < 0 ∧ ∃ hs : lam < poleNeutralEvenRayleighBottom L K hL hK,
      poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hs) = 1) := by
  rcases common_cutoff_negative_ground_alternatives hL K hK hboth with he | ho | hshared
  · obtain ⟨_, hn, hs, hsource⟩ := he
    exact Or.inr (Or.inl ⟨_, hn, hs, hsource⟩)
  · obtain ⟨_, hn, hs, hsource⟩ := ho
    exact Or.inr (Or.inr ⟨_, hn, hs, hsource⟩)
  · exact Or.inl hshared

theorem corrected_native_row_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u =
      inner ℂ (correctedSourceRow L K) ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) :=
  correctedSourceRow_native hL K hK u

theorem complete_arithmetic_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u =
      -inner ℂ (correctedSourceRow L K) ((canonicalArchMatrix L K).toEuclideanLin u.val.val) -
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * correctedSourceTest L K u (Real.log q) :=
  correctedSourceTest_complete_arithmetic hL K hK u

theorem source_test_endpoint_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    correctedSourceTest L K u 0 = 0 ∧ correctedSourceTest L K u L = 0 :=
  ⟨correctedSourceTest_lower_endpoint L K u, correctedSourceTest_upper_endpoint hL K u⟩

theorem source_test_derivative_consumer (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (y : ℝ) :
    HasDerivAt (correctedSourceTest L K u)
      ((-(1 / L) : ℝ) • sourceAtomPairingDerivative K (correctedSourceRow L K)
        u.val.val (1 - y / L)) y :=
  correctedSourceTest_hasDerivAt L K u y

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem exact_negative_index_consumer (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hP : ∀ x : E, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re)
    (hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1)
    (w : F) (hneg : (inner ℂ (T w) w).re < 0) :
    (∀ N : Submodule ℂ F,
      (∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0) → Module.finrank ℂ N ≤ 1) ∧
    ∃ N : Submodule ℂ F, Module.finrank ℂ N = 1 ∧
      ∀ u : N, u ≠ 0 → (inner ℂ (T u) (u : F)).re < 0 :=
  one_shell_negative_index_exact J T hP hshell w hneg

theorem trace_displacement_consumer (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (h : RankOneIntertwining A B D g f) :
    LinearMap.trace ℂ F B - LinearMap.trace ℂ E A = f (D.symm g) :=
  rank_one_trace_displacement A B D g f h

theorem nonunit_metric_consumer (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (D : E ≃ₗ[ℂ] F) (g : F) (f : E →ₗ[ℂ] ℂ)
    (hB : B.IsSymmetric) (h : RankOneIntertwining A B D g f) (x y : E) :
    inner ℂ (D (A x)) (D y) - inner ℂ (D x) (D (A y)) =
      f y * inner ℂ (D x) g - star (f x) * inner ℂ g (D y) :=
  rank_one_metric_identity A B D g f hB h x y

theorem signed_resolvent_budget_consumer {ι : Type*} [Fintype ι]
    (eigenvalue residue : ι → ℝ) (b lam : ℝ)
    (hbottom : ∀ i, b ≤ eigenvalue i) (hlam : lam < b) :
    (b - lam) * (∑ i, residue i / (eigenvalue i - lam)) ≤
      ((∑ i, |residue i|) + ∑ i, residue i) / 2 :=
  signed_resolvent_upper eigenvalue residue b lam hbottom hlam

theorem signed_prefix_comparison_consumer (residue kernel : ℕ → ℝ) (n : ℕ)
    (hp : ∀ j, j ≤ n → 0 ≤ ∑ i ∈ Finset.range j, residue i)
    (hk : 0 ≤ kernel n) (hdec : ∀ i, i < n → kernel (i + 1) ≤ kernel i) :
    0 ≤ ∑ i ∈ Finset.range n, residue i * kernel i :=
  signed_prefix_nonnegative residue kernel n hp hk hdec

theorem frozen_source_cell_consumer {Q : ℕ} (hQ : 1 ≤ Q)
    {L : ℝ} (hcell : L ∈ fixedCanonicalCutoffCell Q) (K : ℕ) :
    frozenCanonicalSourceMatrix Q L K = canonicalSourceMatrix L K :=
  RegularCells.frozen_source_cell_consumer hQ hcell K

theorem actual_even_signed_bound_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    (poleNeutralOddRayleighBottom L K hL hK - lam) *
      (poleNeutralCorrectedCubicSource L K (poleNeutralEvenShiftedRay hL K hK lam hlam)).re ≤
      (‖nativeIndexInverseAdjoint hL K hK
          (poleNeutralCorrectedCubicRieszVector L K)‖ * ‖poleNeutralCubicCompressionVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re) / 2 :=
  native_even_signed_upper hL K hK lam hlam

theorem actual_odd_signed_bound_consumer {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    (poleNeutralEvenRayleighBottom L K hL hK - lam) *
      (poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re ≤
      (‖(poleNeutralIndexEquiv hL K (by omega)).symm (poleNeutralCubicCompressionVector L K)‖ *
          ‖poleNeutralCorrectedCubicRieszVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K)).re) / 2 :=
  native_odd_signed_upper hL K hK lam hlam

end Zeta23.OPICARound4.Validation
