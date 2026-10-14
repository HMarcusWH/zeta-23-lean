import Zeta23.CCM.NativeDeepThresholdInverseBudgets
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
Simplicity at the actual selected eigenvalue comes from the native single
new shell and the actual shifted predecessor coercivity. Both parity
eigenspaces have dimension at most one. A parity containing the selected
ground has dimension exactly one. An even/odd tie remains possible.
-/

private theorem eigenspace_disjoint_coercive_predecessor
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (J : E →ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (lam c : ℝ)
    (hc : 0 < c)
    (hform : ∀ v, (inner ℂ (B (J v)) (J v)).re = (inner ℂ (A v) v).re)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤
      (inner ℂ ((A - (lam : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) v) v).re) :
    Disjoint (Module.End.eigenspace B (lam : ℂ)) (LinearMap.range J.toLinearMap) := by
  refine Submodule.disjoint_def.mpr ?_
  intro u hu hrange
  obtain ⟨v, hv⟩ := hrange
  have hJu : J v = u := hv
  have heig : B (J v) = (lam : ℂ) • J v := by
    rw [hJu]
    exact Module.End.mem_eigenspace_iff.mp hu
  have henergy : (inner ℂ (A v) v).re = lam * ‖v‖ ^ 2 := by
    rw [← hform v, heig]
    simpa only [J.norm_map] using
      (@re_inner_ofReal_smul_self F inferInstance inferInstance lam (J v))
  have hscalar := @re_inner_ofReal_smul_self E inferInstance inferInstance lam v
  have hzero : (inner ℂ ((A - (lam : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) v) v).re = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_sub_left, Complex.sub_re]
    rw [henergy, hscalar]
    ring
  have hb := hcoercive v
  rw [hzero] at hb
  have hsq : ‖v‖ ^ 2 ≤ 0 := by
    by_contra hn
    push Not at hn
    have hp := mul_pos hc hn
    linarith
  have hv0 : v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  rw [← hJu, hv0, map_zero]

/-- Every native even eigenspace at the selected actual spectral value is
at most one-dimensional, including the first cutoff with empty predecessor. -/
theorem nativeDeepThreshold_even_eigenspace_finrank_le_one {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    Module.finrank ℂ (Module.End.eigenspace
      (poleNeutralEvenCompressedCanonical L s.cutoff) (s.lam : ℂ)) ≤ 1 := by
  have hprev : 2 ≤ s.cutoff - 1 := by have hK := s.cutoff_nonempty; omega
  have hle : s.cutoff - 1 ≤ s.cutoff := by omega
  let J := poleNeutralEvenCenteredZeroExtend L hle
  have hg := nativeDeepThresholdGap_pos D Kd hD
    (s.cutoff_nonempty.trans s.cutoff_le_detector)
  have hdisjoint := @eigenspace_disjoint_coercive_predecessor
    (poleNeutralEvenSubspace L (s.cutoff - 1)) (poleNeutralEvenSubspace L s.cutoff)
    inferInstance (poleNeutralEven_innerProductSpace L _) inferInstance (poleNeutralEven_innerProductSpace L _)
    J (poleNeutralEvenCompressedCanonical L (s.cutoff - 1))
    (poleNeutralEvenCompressedCanonical L s.cutoff) s.lam (2 * nativeDeepThresholdGap D Kd)
    (mul_pos (by norm_num) hg)
    (fun v => congrArg Complex.re (inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend hL hle v))
    (nativeDeepThreshold_even_ground_coercive s)
  have hd := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
  have hr := LinearMap.finrank_range_of_inj (f := J.toLinearMap) J.injective
  rw [hr, finrank_poleNeutralEvenSubspace hL (s.cutoff - 1) hprev,
    finrank_poleNeutralEvenSubspace hL s.cutoff (by have hK := s.cutoff_nonempty; omega)] at hd
  omega

/-- The odd counterpart uses its actual native nesting and its own
predecessor form; no even branch is selected by this theorem. -/
theorem nativeDeepThreshold_odd_eigenspace_finrank_le_one {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    Module.finrank ℂ (Module.End.eigenspace
      (poleNeutralOddCompressedCanonical L s.cutoff) (s.lam : ℂ)) ≤ 1 := by
  have hprev : 2 ≤ s.cutoff - 1 := by have hK := s.cutoff_nonempty; omega
  have hle : s.cutoff - 1 ≤ s.cutoff := by omega
  let J := poleNeutralOddCenteredZeroExtend L hle
  have hg := nativeDeepThresholdGap_pos D Kd hD
    (s.cutoff_nonempty.trans s.cutoff_le_detector)
  have hdisjoint := @eigenspace_disjoint_coercive_predecessor
    (poleNeutralOddSubspace L (s.cutoff - 1)) (poleNeutralOddSubspace L s.cutoff)
    inferInstance (poleNeutralOdd_innerProductSpace L _) inferInstance (poleNeutralOdd_innerProductSpace L _)
    J (poleNeutralOddCompressedCanonical L (s.cutoff - 1))
    (poleNeutralOddCompressedCanonical L s.cutoff) s.lam (2 * nativeDeepThresholdGap D Kd)
    (mul_pos (by norm_num) hg)
    (fun v => congrArg Complex.re (inner_poleNeutralOddCompressedCanonical_centeredZeroExtend hL hle v))
    (nativeDeepThreshold_odd_ground_coercive s)
  have hd := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
  have hr := LinearMap.finrank_range_of_inj (f := J.toLinearMap) J.injective
  rw [hr, finrank_poleNeutralOddSubspace hL (s.cutoff - 1) hprev,
    finrank_poleNeutralOddSubspace hL s.cutoff (by have hK := s.cutoff_nonempty; omega)] at hd
  omega

private theorem eigenspace_finrank_positive_of_nonzero
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (lam : ℝ) (u : E) (hu0 : u ≠ 0)
    (hu : A u = (lam : ℂ) • u) :
    0 < Module.finrank ℂ (Module.End.eigenspace A (lam : ℂ)) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨u, Module.End.mem_eigenspace_iff.mpr hu⟩, ?_⟩
  intro hz
  exact hu0 (congrArg Subtype.val hz)

/-- A native even ground at the selected spectral value has a simple
even eigenspace. This allows an odd ground at the same spectral value. -/
theorem nativeDeepThreshold_even_ground_simple {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (u : poleNeutralEvenSubspace L s.cutoff) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) :
    Module.finrank ℂ (Module.End.eigenspace
      (poleNeutralEvenCompressedCanonical L s.cutoff) (s.lam : ℂ)) = 1 := by
  have hlo := eigenspace_finrank_positive_of_nonzero
    (poleNeutralEvenCompressedCanonical L s.cutoff) s.lam u hu0 hu
  have hhi := nativeDeepThreshold_even_eigenspace_finrank_le_one hD s
  omega

theorem nativeDeepThreshold_odd_ground_simple {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (w : poleNeutralOddSubspace L s.cutoff) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L s.cutoff w = (s.lam : ℂ) • w) :
    Module.finrank ℂ (Module.End.eigenspace
      (poleNeutralOddCompressedCanonical L s.cutoff) (s.lam : ℂ)) = 1 := by
  have hlo := eigenspace_finrank_positive_of_nonzero
    (poleNeutralOddCompressedCanonical L s.cutoff) s.lam w hw0 hw
  have hhi := nativeDeepThreshold_odd_eigenspace_finrank_le_one hD s
  omega

/-- The selected actual unit ground belongs to a simple parity eigenspace;
the disjunction preserves the possibility that both parities are tied. -/
theorem nativeDeepThreshold_selectedParity_simple {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    (Module.finrank ℂ (Module.End.eigenspace
        (poleNeutralEvenCompressedCanonical L s.cutoff) (s.lam : ℂ)) = 1 ∧
      ∃ u : poleNeutralEvenSubspace L s.cutoff, ‖u‖ = 1 ∧
        poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) ∨
    (Module.finrank ℂ (Module.End.eigenspace
        (poleNeutralOddCompressedCanonical L s.cutoff) (s.lam : ℂ)) = 1 ∧
      ∃ w : poleNeutralOddSubspace L s.cutoff, ‖w‖ = 1 ∧
        poleNeutralOddCompressedCanonical L s.cutoff w = (s.lam : ℂ) • w) := by
  rcases s.unit_actual_ground with ⟨u, hunit, hu⟩ | ⟨w, hunit, hw⟩
  · have hu0 : u ≠ 0 := by
      intro hz
      have hn : ‖(u.val.val : EuclideanSpace ℂ (Fin (2 * s.cutoff + 1)))‖ = 1 := hunit
      have hzv : (u.val.val : EuclideanSpace ℂ (Fin (2 * s.cutoff + 1))) = 0 :=
        congrArg (fun v : poleNeutralEvenSubspace L s.cutoff => v.val.val) hz
      rw [hzv, norm_zero] at hn
      norm_num at hn
    exact Or.inl ⟨nativeDeepThreshold_even_ground_simple hD s u hu0 hu, u, hunit, hu⟩
  · have hw0 : w ≠ 0 := by
      intro hz
      have hn : ‖(w.val.val : EuclideanSpace ℂ (Fin (2 * s.cutoff + 1)))‖ = 1 := hunit
      have hzv : (w.val.val : EuclideanSpace ℂ (Fin (2 * s.cutoff + 1))) = 0 :=
        congrArg (fun v : poleNeutralOddSubspace L s.cutoff => v.val.val) hz
      rw [hzv, norm_zero] at hn
      norm_num at hn
    exact Or.inr ⟨nativeDeepThreshold_odd_ground_simple hD s w hw0 hw, w, hunit, hw⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDeepThreshold_even_eigenspace_finrank_le_one
#print axioms Zeta23.CCM.nativeDeepThreshold_odd_eigenspace_finrank_le_one
#print axioms Zeta23.CCM.nativeDeepThreshold_even_ground_simple
#print axioms Zeta23.CCM.nativeDeepThreshold_odd_ground_simple
#print axioms Zeta23.CCM.nativeDeepThreshold_selectedParity_simple
