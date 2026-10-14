import Zeta23.CCM.CanonicalPoleNeutralNesting
import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Native bottom antitonicity and the actual one-dimensional successor shells.

The nesting and form transport are proved for the unchanged pole kernels.
The actual smaller ground is transported as a trial vector at the larger
cutoff, so the actual larger bottom is no greater. No nested-form assumption
or threshold selector is supplied. Ground bottoms are used only for K ≥ 3;
the shell dimension also covers the empty predecessor at K = 2.
-/

theorem poleNeutralEvenRayleighBottom_antitone_of_le {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    poleNeutralEvenRayleighBottom L M hL (le_trans hN hNM) ≤
      poleNeutralEvenRayleighBottom L N hL hN := by
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL N hN
  let w := poleNeutralEvenCenteredZeroExtend L hNM u
  have hnorm : ‖w‖ = ‖u‖ := (poleNeutralEvenCenteredZeroExtend L hNM).norm_map u
  have hform : (inner ℂ (poleNeutralEvenCompressedCanonical L M w) w).re =
      (inner ℂ (poleNeutralEvenCompressedCanonical L N u) u).re :=
    congrArg Complex.re (inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend hL hNM u)
  have hold : (inner ℂ (poleNeutralEvenCompressedCanonical L N u) u).re =
      poleNeutralEvenRayleighBottom L N hL hN * ‖u‖ ^ 2 := by
    rw [hu]
    exact @re_inner_ofReal_smul_self (poleNeutralEvenSubspace L N) inferInstance
      (poleNeutralEven_innerProductSpace L N) _ u
  have hb := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL M (le_trans hN hNM) w
  rw [hnorm, hform, hold] at hb
  have hn : 0 < ‖u‖ ^ 2 := by positivity
  exact (mul_le_mul_iff_left₀ hn).mp hb

theorem poleNeutralOddRayleighBottom_antitone_of_le {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    poleNeutralOddRayleighBottom L M hL (le_trans hN hNM) ≤
      poleNeutralOddRayleighBottom L N hL hN := by
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL N hN
  let w := poleNeutralOddCenteredZeroExtend L hNM u
  have hnorm : ‖w‖ = ‖u‖ := (poleNeutralOddCenteredZeroExtend L hNM).norm_map u
  have hform : (inner ℂ (poleNeutralOddCompressedCanonical L M w) w).re =
      (inner ℂ (poleNeutralOddCompressedCanonical L N u) u).re :=
    congrArg Complex.re (inner_poleNeutralOddCompressedCanonical_centeredZeroExtend hL hNM u)
  have hold : (inner ℂ (poleNeutralOddCompressedCanonical L N u) u).re =
      poleNeutralOddRayleighBottom L N hL hN * ‖u‖ ^ 2 := by
    rw [hu]
    exact @re_inner_ofReal_smul_self (poleNeutralOddSubspace L N) inferInstance
      (poleNeutralOdd_innerProductSpace L N) _ u
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL M (le_trans hN hNM) w
  rw [hnorm, hform, hold] at hb
  have hn : 0 < ‖u‖ ^ 2 := by positivity
  exact (mul_le_mul_iff_left₀ hn).mp hb

def poleNeutralGlobalRayleighBottom (L : ℝ) (K : ℕ) (hL : 0 < L) (hK : 3 ≤ K) : ℝ :=
  min (poleNeutralEvenRayleighBottom L K hL hK) (poleNeutralOddRayleighBottom L K hL hK)

theorem poleNeutralGlobalRayleighBottom_antitone_of_le {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    poleNeutralGlobalRayleighBottom L M hL (le_trans hN hNM) ≤
      poleNeutralGlobalRayleighBottom L N hL hN :=
  min_le_min (poleNeutralEvenRayleighBottom_antitone_of_le hL hN hNM)
    (poleNeutralOddRayleighBottom_antitone_of_le hL hN hNM)

/-- The full actual even sesquilinear form transports to the predecessor. -/
theorem inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend_pair
    {L : ℝ} (hL : 0 < L) {N M : ℕ} (hNM : N ≤ M) (u v : poleNeutralEvenSubspace L N) :
    inner ℂ (poleNeutralEvenCompressedCanonical L M (poleNeutralEvenCenteredZeroExtend L hNM u))
      (poleNeutralEvenCenteredZeroExtend L hNM v) = inner ℂ (poleNeutralEvenCompressedCanonical L N u) v := by
  rw [(poleNeutralEvenCompressedCanonical_isSymmetric L M).inner_map_polarization,
    (poleNeutralEvenCompressedCanonical_isSymmetric L N).inner_map_polarization]
  have hsub (x y : poleNeutralEvenSubspace L N) :
      poleNeutralEvenCenteredZeroExtend L hNM x - poleNeutralEvenCenteredZeroExtend L hNM y =
        poleNeutralEvenCenteredZeroExtend L hNM (x - y) :=
    ((poleNeutralEvenCenteredZeroExtend L hNM).map_sub x y).symm
  simp only [← map_add, hsub, ← map_smul,
    inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend hL hNM]

/-- The actual odd sesquilinear form has the same predecessor consistency. -/
theorem inner_poleNeutralOddCompressedCanonical_centeredZeroExtend_pair
    {L : ℝ} (hL : 0 < L) {N M : ℕ} (hNM : N ≤ M) (u v : poleNeutralOddSubspace L N) :
    inner ℂ (poleNeutralOddCompressedCanonical L M (poleNeutralOddCenteredZeroExtend L hNM u))
      (poleNeutralOddCenteredZeroExtend L hNM v) = inner ℂ (poleNeutralOddCompressedCanonical L N u) v := by
  rw [(poleNeutralOddCompressedCanonical_isSymmetric L M).inner_map_polarization,
    (poleNeutralOddCompressedCanonical_isSymmetric L N).inner_map_polarization]
  have hsub (x y : poleNeutralOddSubspace L N) :
      poleNeutralOddCenteredZeroExtend L hNM x - poleNeutralOddCenteredZeroExtend L hNM y =
        poleNeutralOddCenteredZeroExtend L hNM (x - y) :=
    ((poleNeutralOddCenteredZeroExtend L hNM).map_sub x y).symm
  simp only [← map_add, hsub, ← map_smul,
    inner_poleNeutralOddCompressedCanonical_centeredZeroExtend hL hNM]

/-- The actual predecessor block is constructed from the actual larger
operator and the actual native isometry; it is not a nested-form premise. -/
theorem poleNeutralEven_predecessor_compression_eq {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M) :
    (LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralEvenSubspace L N)
      (F := poleNeutralEvenSubspace L M) (poleNeutralEvenCenteredZeroExtend L hNM).toLinearMap).comp
      ((poleNeutralEvenCompressedCanonical L M).comp (poleNeutralEvenCenteredZeroExtend L hNM).toLinearMap) =
        poleNeutralEvenCompressedCanonical L N := by
  apply LinearMap.ext
  intro u
  apply ext_inner_right ℂ
  intro v
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left]
  exact inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend_pair hL hNM u v

theorem poleNeutralOdd_predecessor_compression_eq {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M) :
    (LinearMap.adjoint (𝕜 := ℂ) (E := poleNeutralOddSubspace L N)
      (F := poleNeutralOddSubspace L M) (poleNeutralOddCenteredZeroExtend L hNM).toLinearMap).comp
      ((poleNeutralOddCompressedCanonical L M).comp (poleNeutralOddCenteredZeroExtend L hNM).toLinearMap) =
        poleNeutralOddCompressedCanonical L N := by
  apply LinearMap.ext
  intro u
  apply ext_inner_right ℂ
  intro v
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left]
  exact inner_poleNeutralOddCompressedCanonical_centeredZeroExtend_pair hL hNM u v

theorem finrank_poleNeutralEven_successor_shell_eq_one {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 2 ≤ N) :
    Module.finrank ℂ (@Submodule.orthogonal ℂ (poleNeutralEvenSubspace L (N + 1))
      inferInstance inferInstance (poleNeutralEven_innerProductSpace L (N + 1))
      (LinearMap.range (poleNeutralEvenCenteredZeroExtend L (Nat.le_succ N)).toLinearMap)) = 1 := by
  have hr := LinearMap.finrank_range_of_inj
    (f := (poleNeutralEvenCenteredZeroExtend L (Nat.le_succ N)).toLinearMap)
    (poleNeutralEvenCenteredZeroExtend L (Nat.le_succ N)).injective
  have hs := @Submodule.finrank_add_finrank_orthogonal ℂ (poleNeutralEvenSubspace L (N + 1))
    inferInstance inferInstance (poleNeutralEven_innerProductSpace L (N + 1)) inferInstance
    (LinearMap.range (poleNeutralEvenCenteredZeroExtend L (Nat.le_succ N)).toLinearMap)
  rw [hr, finrank_poleNeutralEvenSubspace hL N hN,
    finrank_poleNeutralEvenSubspace hL (N + 1) (by omega)] at hs
  omega

theorem finrank_poleNeutralOdd_successor_shell_eq_one {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 2 ≤ N) :
    Module.finrank ℂ (@Submodule.orthogonal ℂ (poleNeutralOddSubspace L (N + 1))
      inferInstance inferInstance (poleNeutralOdd_innerProductSpace L (N + 1))
      (LinearMap.range (poleNeutralOddCenteredZeroExtend L (Nat.le_succ N)).toLinearMap)) = 1 := by
  have hr := LinearMap.finrank_range_of_inj
    (f := (poleNeutralOddCenteredZeroExtend L (Nat.le_succ N)).toLinearMap)
    (poleNeutralOddCenteredZeroExtend L (Nat.le_succ N)).injective
  have hs := @Submodule.finrank_add_finrank_orthogonal ℂ (poleNeutralOddSubspace L (N + 1))
    inferInstance inferInstance (poleNeutralOdd_innerProductSpace L (N + 1)) inferInstance
    (LinearMap.range (poleNeutralOddCenteredZeroExtend L (Nat.le_succ N)).toLinearMap)
  rw [hr, finrank_poleNeutralOddSubspace hL N hN,
    finrank_poleNeutralOddSubspace hL (N + 1) (by omega)] at hs
  omega

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutralEvenRayleighBottom_antitone_of_le
#print axioms Zeta23.CCM.poleNeutralOddRayleighBottom_antitone_of_le
#print axioms Zeta23.CCM.poleNeutralGlobalRayleighBottom_antitone_of_le
#print axioms Zeta23.CCM.poleNeutralEven_predecessor_compression_eq
#print axioms Zeta23.CCM.poleNeutralOdd_predecessor_compression_eq
#print axioms Zeta23.CCM.finrank_poleNeutralEven_successor_shell_eq_one
#print axioms Zeta23.CCM.finrank_poleNeutralOdd_successor_shell_eq_one
