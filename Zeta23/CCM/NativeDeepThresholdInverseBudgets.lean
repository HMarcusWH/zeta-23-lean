import Zeta23.CCM.NativeDeepThresholdGround

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The two actual predecessor shifts supplied by the native least crossing.

At the selected actual eigenvalue `lam`, both predecessor operators have
coercivity `2g`. At the detector value `-eta`, they have coercivity `g`.
Their inverse bounds are therefore respectively 6 and 12 times (Kd-1)/D.
The cutoff-3 case uses the actual zero-dimensional predecessor spaces.
No bottom is assigned to an empty space, and the two shifts stay distinct.
-/

private theorem coerciveEndomorphism_injective {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →ₗ[ℂ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ u, c * ‖u‖ ^ 2 ≤ (inner ℂ (T u) u).re) : Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have hb := hT u
  rw [hu, inner_zero_left, Complex.zero_re] at hb
  have hs : ‖u‖ ^ 2 ≤ 0 := by
    by_contra hn
    push Not at hn
    have hp := mul_pos hc hn
    linarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

private theorem coerciveEquiv_inverse_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (Ti : E ≃ₗ[ℂ] E) (hTi : ∀ u, Ti u = T u) (c : ℝ) (hc : 0 < c)
    (hT : ∀ u, c * ‖u‖ ^ 2 ≤ (inner ℂ (T u) u).re) :
    ‖Ti.symm.toLinearMap.toContinuousLinearMap‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
  intro w
  change ‖Ti.symm w‖ ≤ c⁻¹ * ‖w‖
  by_cases hz : Ti.symm w = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg w)
  · have hv : 0 < ‖Ti.symm w‖ := norm_pos_iff.mpr hz
    have hb := hT (Ti.symm w)
    rw [← hTi, Ti.apply_symm_apply] at hb
    have hi : (inner ℂ w (Ti.symm w)).re ≤ ‖w‖ * ‖Ti.symm w‖ :=
      re_inner_le_norm (𝕜 := ℂ) w (Ti.symm w)
    have hmul : c * ‖Ti.symm w‖ ≤ ‖w‖ := by
      apply (mul_le_mul_iff_left₀ hv).mp
      nlinarith
    calc
      ‖Ti.symm w‖ ≤ ‖w‖ / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hmul)
      _ = c⁻¹ * ‖w‖ := by ring

private theorem nativePredecessor_even_shift_coercive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) (shift c : ℝ)
    (hc : c ≤ -s.eta + nativeDeepThresholdGap D Kd - shift)
    (u : poleNeutralEvenSubspace L (s.cutoff - 1)) :
    c * ‖u‖ ^ 2 ≤
      (inner ℂ (poleNeutralEvenShiftedCanonical L (s.cutoff - 1) shift u) u).re := by
  by_cases hprev : 3 ≤ s.cutoff - 1
  · have hbottom := (s.predecessor_bottoms hprev).1
    have hdiff : c ≤ poleNeutralEvenRayleighBottom L (s.cutoff - 1) hL hprev - shift := by
      linarith
    exact (mul_le_mul_of_nonneg_right hdiff (sq_nonneg ‖u‖)).trans
      (poleNeutralEvenShiftedCanonical_coercive hL (s.cutoff - 1) hprev shift u)
  · have hfirst : s.cutoff = 3 := by have hK := s.cutoff_nonempty; omega
    have hpred : s.cutoff - 1 = 2 := by omega
    have hzero : Module.finrank ℂ (poleNeutralEvenSubspace L (s.cutoff - 1)) = 0 := by
      rw [hpred]
      exact (s.first_predecessor_empty hfirst).1
    have hu : u = 0 :=
      (finrank_zero_iff_forall_zero (K := ℂ) (V := poleNeutralEvenSubspace L (s.cutoff - 1))).mp hzero u
    subst u
    simp

private theorem nativePredecessor_odd_shift_coercive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) (shift c : ℝ)
    (hc : c ≤ -s.eta + nativeDeepThresholdGap D Kd - shift)
    (w : poleNeutralOddSubspace L (s.cutoff - 1)) :
    c * ‖w‖ ^ 2 ≤
      (inner ℂ (poleNeutralOddShiftedCanonical L (s.cutoff - 1) shift w) w).re := by
  by_cases hprev : 3 ≤ s.cutoff - 1
  · have hbottom := (s.predecessor_bottoms hprev).2
    have hdiff : c ≤ poleNeutralOddRayleighBottom L (s.cutoff - 1) hL hprev - shift := by
      linarith
    exact (mul_le_mul_of_nonneg_right hdiff (sq_nonneg ‖w‖)).trans
      (poleNeutralOddShiftedCanonical_coercive hL (s.cutoff - 1) hprev shift w)
  · have hfirst : s.cutoff = 3 := by have hK := s.cutoff_nonempty; omega
    have hpred : s.cutoff - 1 = 2 := by omega
    have hzero : Module.finrank ℂ (poleNeutralOddSubspace L (s.cutoff - 1)) = 0 := by
      rw [hpred]
      exact (s.first_predecessor_empty hfirst).2
    have hw : w = 0 :=
      (finrank_zero_iff_forall_zero (K := ℂ) (V := poleNeutralOddSubspace L (s.cutoff - 1))).mp hzero w
    subst w
    simp

theorem nativeDeepThreshold_even_ground_coercive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (u : poleNeutralEvenSubspace L (s.cutoff - 1)) :
    (2 * nativeDeepThresholdGap D Kd) * ‖u‖ ^ 2 ≤
      (inner ℂ (poleNeutralEvenShiftedCanonical L (s.cutoff - 1) s.lam u) u).re :=
  nativePredecessor_even_shift_coercive s s.lam _ (by have hd := s.lam_depth; linarith) u

theorem nativeDeepThreshold_odd_ground_coercive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (w : poleNeutralOddSubspace L (s.cutoff - 1)) :
    (2 * nativeDeepThresholdGap D Kd) * ‖w‖ ^ 2 ≤
      (inner ℂ (poleNeutralOddShiftedCanonical L (s.cutoff - 1) s.lam w) w).re :=
  nativePredecessor_odd_shift_coercive s s.lam _ (by have hd := s.lam_depth; linarith) w

theorem nativeDeepThreshold_even_detector_coercive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (u : poleNeutralEvenSubspace L (s.cutoff - 1)) :
    nativeDeepThresholdGap D Kd * ‖u‖ ^ 2 ≤
      (inner ℂ (poleNeutralEvenShiftedCanonical L (s.cutoff - 1) (-s.eta) u) u).re :=
  nativePredecessor_even_shift_coercive s (-s.eta) _ (by linarith) u

theorem nativeDeepThreshold_odd_detector_coercive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (w : poleNeutralOddSubspace L (s.cutoff - 1)) :
    nativeDeepThresholdGap D Kd * ‖w‖ ^ 2 ≤
      (inner ℂ (poleNeutralOddShiftedCanonical L (s.cutoff - 1) (-s.eta) w) w).re :=
  nativePredecessor_odd_shift_coercive s (-s.eta) _ (by linarith) w

private theorem nativeDeepThreshold_gap_positive {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    0 < nativeDeepThresholdGap D Kd :=
  nativeDeepThresholdGap_pos D Kd hD (s.cutoff_nonempty.trans s.cutoff_le_detector)

private theorem nativeDeepThreshold_gap_inv (D : ℝ) (Kd : ℕ) :
    (nativeDeepThresholdGap D Kd)⁻¹ = 12 * ((Kd - 1 : ℕ) : ℝ) / D := by
  simp only [nativeDeepThresholdGap, inv_div] <;> ring

private theorem nativeDeepThreshold_two_gap_inv (D : ℝ) (Kd : ℕ) :
    (2 * nativeDeepThresholdGap D Kd)⁻¹ = 6 * ((Kd - 1 : ℕ) : ℝ) / D := by
  simp only [nativeDeepThresholdGap, mul_inv_rev, inv_div] <;> ring

/-- Four genuine inverses of the literal predecessor shifts, with their
distinct ground-relative and detector budgets. -/
structure NativeDeepThresholdInverseData {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL) where
  evenGround : poleNeutralEvenSubspace L (s.cutoff - 1) ≃ₗ[ℂ]
    poleNeutralEvenSubspace L (s.cutoff - 1)
  oddGround : poleNeutralOddSubspace L (s.cutoff - 1) ≃ₗ[ℂ]
    poleNeutralOddSubspace L (s.cutoff - 1)
  evenDetector : poleNeutralEvenSubspace L (s.cutoff - 1) ≃ₗ[ℂ]
    poleNeutralEvenSubspace L (s.cutoff - 1)
  oddDetector : poleNeutralOddSubspace L (s.cutoff - 1) ≃ₗ[ℂ]
    poleNeutralOddSubspace L (s.cutoff - 1)
  evenGround_actual : ∀ u, evenGround u =
    poleNeutralEvenShiftedCanonical L (s.cutoff - 1) s.lam u
  oddGround_actual : ∀ w, oddGround w =
    poleNeutralOddShiftedCanonical L (s.cutoff - 1) s.lam w
  evenDetector_actual : ∀ u, evenDetector u =
    poleNeutralEvenShiftedCanonical L (s.cutoff - 1) (-s.eta) u
  oddDetector_actual : ∀ w, oddDetector w =
    poleNeutralOddShiftedCanonical L (s.cutoff - 1) (-s.eta) w
  evenGround_inverse_bound : ‖evenGround.symm.toLinearMap.toContinuousLinearMap‖ ≤
    6 * ((Kd - 1 : ℕ) : ℝ) / D
  oddGround_inverse_bound : ‖oddGround.symm.toLinearMap.toContinuousLinearMap‖ ≤
    6 * ((Kd - 1 : ℕ) : ℝ) / D
  evenDetector_inverse_bound : ‖evenDetector.symm.toLinearMap.toContinuousLinearMap‖ ≤
    12 * ((Kd - 1 : ℕ) : ℝ) / D
  oddDetector_inverse_bound : ‖oddDetector.symm.toLinearMap.toContinuousLinearMap‖ ≤
    12 * ((Kd - 1 : ℕ) : ℝ) / D

/-- No inverse or coercivity is assumed: the actual selected ground data
constructs all four inverses, including the empty predecessor case. -/
def nativeDeepThresholdInverseData {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    NativeDeepThresholdInverseData s := by
  have hg := nativeDeepThreshold_gap_positive hD s
  have h2g : 0 < 2 * nativeDeepThresholdGap D Kd := mul_pos (by norm_num) hg
  let E := poleNeutralEvenSubspace L (s.cutoff - 1)
  let O := poleNeutralOddSubspace L (s.cutoff - 1)
  let Ae := poleNeutralEvenShiftedCanonical L (s.cutoff - 1) s.lam
  let Ao := poleNeutralOddShiftedCanonical L (s.cutoff - 1) s.lam
  let Be := poleNeutralEvenShiftedCanonical L (s.cutoff - 1) (-s.eta)
  let Bo := poleNeutralOddShiftedCanonical L (s.cutoff - 1) (-s.eta)
  let eG : E ≃ₗ[ℂ] E := LinearEquiv.ofInjectiveEndo Ae
    (@coerciveEndomorphism_injective E inferInstance (poleNeutralEven_innerProductSpace L _)
      Ae _ h2g (nativeDeepThreshold_even_ground_coercive s))
  let oG : O ≃ₗ[ℂ] O := LinearEquiv.ofInjectiveEndo Ao
    (@coerciveEndomorphism_injective O inferInstance (poleNeutralOdd_innerProductSpace L _)
      Ao _ h2g (nativeDeepThreshold_odd_ground_coercive s))
  let eD : E ≃ₗ[ℂ] E := LinearEquiv.ofInjectiveEndo Be
    (@coerciveEndomorphism_injective E inferInstance (poleNeutralEven_innerProductSpace L _)
      Be _ hg (nativeDeepThreshold_even_detector_coercive s))
  let oD : O ≃ₗ[ℂ] O := LinearEquiv.ofInjectiveEndo Bo
    (@coerciveEndomorphism_injective O inferInstance (poleNeutralOdd_innerProductSpace L _)
      Bo _ hg (nativeDeepThreshold_odd_detector_coercive s))
  refine {
    evenGround := eG
    oddGround := oG
    evenDetector := eD
    oddDetector := oD
    evenGround_actual := fun _ => rfl
    oddGround_actual := fun _ => rfl
    evenDetector_actual := fun _ => rfl
    oddDetector_actual := fun _ => rfl
    evenGround_inverse_bound := ?_
    oddGround_inverse_bound := ?_
    evenDetector_inverse_bound := ?_
    oddDetector_inverse_bound := ?_ }
  · rw [← nativeDeepThreshold_two_gap_inv]
    exact @coerciveEquiv_inverse_norm_le E inferInstance (poleNeutralEven_innerProductSpace L _)
      inferInstance Ae eG (fun _ => rfl) _ h2g (nativeDeepThreshold_even_ground_coercive s)
  · rw [← nativeDeepThreshold_two_gap_inv]
    exact @coerciveEquiv_inverse_norm_le O inferInstance (poleNeutralOdd_innerProductSpace L _)
      inferInstance Ao oG (fun _ => rfl) _ h2g (nativeDeepThreshold_odd_ground_coercive s)
  · rw [← nativeDeepThreshold_gap_inv]
    exact @coerciveEquiv_inverse_norm_le E inferInstance (poleNeutralEven_innerProductSpace L _)
      inferInstance Be eD (fun _ => rfl) _ hg (nativeDeepThreshold_even_detector_coercive s)
  · rw [← nativeDeepThreshold_gap_inv]
    exact @coerciveEquiv_inverse_norm_le O inferInstance (poleNeutralOdd_innerProductSpace L _)
      inferInstance Bo oD (fun _ => rfl) _ hg (nativeDeepThreshold_odd_detector_coercive s)

private theorem operator_norm_zero_of_finrank_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hE : Module.finrank ℂ E = 0)
    (T : E →L[ℂ] E) : ‖T‖ = 0 := by
  have hz : T = 0 := by
    ext u
    exact (finrank_zero_iff_forall_zero (K := ℂ) (V := E)).mp hE (T u)
  rw [hz, norm_zero]

/-- At the first cutoff every actual predecessor inverse has norm zero. -/
theorem nativeDeepThreshold_inverse_norms_zero_at_first {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (r : NativeDeepThresholdInverseData s) (hfirst : s.cutoff = 3) :
    ‖r.evenGround.symm.toLinearMap.toContinuousLinearMap‖ = 0 ∧
      ‖r.oddGround.symm.toLinearMap.toContinuousLinearMap‖ = 0 ∧
      ‖r.evenDetector.symm.toLinearMap.toContinuousLinearMap‖ = 0 ∧
      ‖r.oddDetector.symm.toLinearMap.toContinuousLinearMap‖ = 0 := by
  have hpred : s.cutoff - 1 = 2 := by omega
  have he : Module.finrank ℂ (poleNeutralEvenSubspace L (s.cutoff - 1)) = 0 := by
    rw [hpred]
    exact (s.first_predecessor_empty hfirst).1
  have ho : Module.finrank ℂ (poleNeutralOddSubspace L (s.cutoff - 1)) = 0 := by
    rw [hpred]
    exact (s.first_predecessor_empty hfirst).2
  exact ⟨@operator_norm_zero_of_finrank_zero (poleNeutralEvenSubspace L (s.cutoff - 1))
      inferInstance (poleNeutralEven_innerProductSpace L _) inferInstance he _,
    @operator_norm_zero_of_finrank_zero (poleNeutralOddSubspace L (s.cutoff - 1))
      inferInstance (poleNeutralOdd_innerProductSpace L _) inferInstance ho _,
    @operator_norm_zero_of_finrank_zero (poleNeutralEvenSubspace L (s.cutoff - 1))
      inferInstance (poleNeutralEven_innerProductSpace L _) inferInstance he _,
    @operator_norm_zero_of_finrank_zero (poleNeutralOddSubspace L (s.cutoff - 1))
      inferInstance (poleNeutralOdd_innerProductSpace L _) inferInstance ho _⟩

/-- The supplied original mixed-parity detector constructs the actual least
crossing ground and all four predecessor inverses with the 6/12 budgets. -/
theorem exists_nativeDeepThresholdGround_with_inverseBudgets_of_given_trial
    {L : ℝ} (hL : 0 < L) (Kd : ℕ) (hKd : 3 ≤ Kd) (D : ℝ) (hD : 0 < D)
    (p : EuclideanSpace ℂ (Fin (2 * Kd + 1)))
    (hlegal : p ∈ euclideanBoundaryFlatSubspace Kd)
    (hpEven : canonicalPoleEvenFunctional L Kd p = 0)
    (hpOdd : canonicalPoleOddFunctional L Kd p = 0) (hpUnit : ‖p‖ = 1)
    (hpDepth : (inner ℂ ((canonicalSourceMatrix L Kd).toEuclideanLin p) p).re ≤ -D) :
    ∃ s : NativeDeepThresholdGroundData L Kd D hL, Nonempty (NativeDeepThresholdInverseData s) := by
  obtain ⟨s⟩ := exists_nativeDeepThresholdGround_of_given_trial hL Kd hKd D hD
    p hlegal hpEven hpOdd hpUnit hpDepth
  exact ⟨s, ⟨nativeDeepThresholdInverseData hD s⟩⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDeepThreshold_even_ground_coercive
#print axioms Zeta23.CCM.nativeDeepThreshold_odd_ground_coercive
#print axioms Zeta23.CCM.nativeDeepThreshold_even_detector_coercive
#print axioms Zeta23.CCM.nativeDeepThreshold_odd_detector_coercive
#print axioms Zeta23.CCM.nativeDeepThresholdInverseData
#print axioms Zeta23.CCM.nativeDeepThreshold_inverse_norms_zero_at_first
#print axioms Zeta23.CCM.exists_nativeDeepThresholdGround_with_inverseBudgets_of_given_trial
