import Zeta23.OPICARound4.JointGroundBirth
import Zeta23.OPICARound4.NativeVisibility
import Zeta23.OPICARound4.NativeWitnessCosts

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

private theorem negative_eigenvalue_eq_of_nonnegative_complement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (b lam : ℝ)
    (u v : E) (hu : T u = (b : ℂ) • u) (hv : T v = (lam : ℂ) • v)
    (hv0 : v ≠ 0) (hlam : lam < 0)
    (hcomp : ∀ x : E, inner ℂ u x = 0 → 0 ≤ (inner ℂ (T x) x).re) : lam = b := by
  by_contra hne
  have hcast : (b : ℂ) - (lam : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (Complex.ofReal_injective h).symm)
  have hs := hT u v
  rw [hu, hv, inner_smul_left, inner_smul_right] at hs
  simp only [Complex.conj_ofReal] at hs
  have hm : ((b : ℂ) - (lam : ℂ)) * inner ℂ u v = 0 := by
    calc
      _ = (b : ℂ) * inner ℂ u v - (lam : ℂ) * inner ℂ u v := by ring
      _ = 0 := sub_eq_zero.mpr hs
  have horth : inner ℂ u v = 0 := (mul_eq_zero.mp hm).resolve_left hcast
  have hp := hcomp v horth
  rw [hv, re_inner_ofReal_smul_self] at hp
  exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hv0)))

private theorem eigenspace_finrank_le_one_of_visible
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (lam : ℂ) (f : E →ₗ[ℂ] ℂ)
    (hvis : ∀ v : E, v ≠ 0 → T v = lam • v → f v ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace T lam) ≤ 1 := by
  let q := f.comp (Module.End.eigenspace T lam).subtype
  have hi : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have hv0 : (v : E) ≠ 0 := fun h => hne (Subtype.ext h)
    exact (hvis v hv0 ((Module.End.mem_eigenspace_iff).mp v.property)) hv
  simpa using q.finrank_le_finrank_of_injective hi

private theorem inverse_eigen_of_rankOne_output_zero
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hrank : RankOneIntertwining A B D g f)
    (lam : ℂ) (w : F) (hw : B w = lam • w) (hf : f (D.symm w) = 0) :
    A (D.symm w) = lam • D.symm w := by
  apply D.injective
  have hr := hrank (D.symm w)
  rw [D.apply_symm_apply, hf, zero_smul, hw] at hr
  rw [map_smul, D.apply_symm_apply]
  exact (sub_eq_zero.mp hr).symm

/-- Every negative eigenmode of an actual own newborn has its actual ground
eigenvalue. This uses the whole nonnegative complement, not just simplicity
of each individual eigenspace. -/
theorem nativeNewborn_negative_eigenvalue_eq_ground
    (p : ReversalParity) {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness p L K hL) (lam : ℝ) (hlam : lam < 0)
    (v : nativePoleNeutralParitySpace p L K) (hv0 : v ≠ 0)
    (hv : nativePoleNeutralParityCanonical p L K v = (lam : ℂ) • v) :
    lam = match p with
      | .even => poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
      | .odd => poleNeutralOddRayleighBottom L K hL s.cutoff_lower := by
  cases p
  · obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K s.cutoff_lower
    have hneg := newborn_bottom_le_normalized_energy .even hL K s
    have hb : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower < 0 := hneg.1.trans_lt hneg.2
    apply @negative_eigenvalue_eq_of_nonnegative_complement
      (poleNeutralEvenSubspace L K) inferInstance (poleNeutralEven_innerProductSpace L K) _
      (poleNeutralEvenCompressedCanonical_isSymmetric L K) _ _ u v hu hv hv0 hlam
    intro x hx
    exact (nativeNewborn_negative_eigen_complement_bounds .even s _ hb u hu0 hu x hx).1
  · obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K s.cutoff_lower
    have hneg := newborn_bottom_le_normalized_energy .odd hL K s
    have hb : poleNeutralOddRayleighBottom L K hL s.cutoff_lower < 0 := hneg.1.trans_lt hneg.2
    apply @negative_eigenvalue_eq_of_nonnegative_complement
      (poleNeutralOddSubspace L K) inferInstance (poleNeutralOdd_innerProductSpace L K) _
      (poleNeutralOddCompressedCanonical_isSymmetric L K) _ _ u v hu hv hv0 hlam
    intro x hx
    exact (nativeNewborn_negative_eigen_complement_bounds .odd s _ hb u hu0 hu x hx).1

/-- When the even side is its own newborn, every opposite negative mode
away from the one shared eigenvalue is visible to the ACTUAL cubic pairing.
No ordering of the two bottoms is assumed. -/
theorem evenNewborn_odd_negative_eigen_channels_visible
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .even L K hL) (lam : ℝ) (hlam : lam < 0)
    (hne : lam ≠ poleNeutralEvenRayleighBottom L K hL s.cutoff_lower)
    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 ∧
      poleNeutralCorrectedCubicSource L K
        ((poleNeutralIndexEquiv hL K (Nat.le_trans (by decide : 1 ≤ 3) s.cutoff_lower)).symm w) ≠ 0 := by
  have hc : poleNeutralCubicPairingFunctional L K w ≠ 0 := by
    rcases native_odd_visible_or_shared_mode hL K s.cutoff_lower lam w hw0 hw with hc | ⟨v,hv0,hv,_⟩
    · exact hc
    · exact False.elim (hne (nativeNewborn_negative_eigenvalue_eq_ground .even s lam hlam v hv0 hv))
  refine ⟨hc, ?_⟩
  intro hf
  let D := poleNeutralIndexEquiv hL K (Nat.le_trans (by decide : 1 ≤ 3) s.cutoff_lower)
  have hv0 : D.symm w ≠ 0 := by
    intro hz
    apply hw0
    simpa only [map_zero, D.apply_symm_apply] using congrArg D hz
  have hv := inverse_eigen_of_rankOne_output_zero
    (poleNeutralEvenCompressedCanonical L K) (poleNeutralOddCompressedCanonical L K)
    D (poleNeutralCubicCompressionVector L K) (poleNeutralCorrectedCubicFunctional L K)
    (canonicalPoleNeutralRankOneIntertwining hL K
      (Nat.le_trans (by decide : 2 ≤ 3) s.cutoff_lower)) (lam : ℂ) w hw hf
  exact hne (nativeNewborn_negative_eigenvalue_eq_ground .even s lam hlam _ hv0 hv)

/-- Reversed own-newborn orientation, retaining the actual corrected even
source rather than an odd eigenray's energy or a substituted reciprocal test. -/
theorem oddNewborn_even_negative_eigen_channels_visible
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL) (lam : ℝ) (hlam : lam < 0)
    (hne : lam ≠ poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      poleNeutralCubicPairingFunctional L K
        ((poleNeutralIndexAdjointEquiv hL K s.cutoff_lower).symm u) ≠ 0 := by
  have hf : poleNeutralCorrectedCubicSource L K u ≠ 0 := by
    rcases native_even_visible_or_shared_mode hL K s.cutoff_lower lam u hu0 hu with hf | ⟨v,hv0,hv,_⟩
    · exact hf
    · exact False.elim (hne (nativeNewborn_negative_eigenvalue_eq_ground .odd s lam hlam v hv0 hv))
  refine ⟨hf, ?_⟩
  intro hc
  let D := poleNeutralIndexAdjointEquiv hL K s.cutoff_lower
  have hv0 : D.symm u ≠ 0 := by
    intro hz
    apply hu0
    simpa only [map_zero, D.apply_symm_apply] using congrArg D hz
  have hv := inverse_eigen_of_rankOne_output_zero
    (poleNeutralOddCompressedCanonical L K) (poleNeutralEvenCompressedCanonical L K)
    D (-poleNeutralCorrectedCubicRieszVector L K) (poleNeutralCubicPairingFunctional L K)
    (native_odd_rank_one_unshifted hL K s.cutoff_lower) (lam : ℂ) u hu hc
  exact hne (nativeNewborn_negative_eigenvalue_eq_ground .odd s lam hlam _ hv0 hv)

/-- All multiplicities are retained: each opposite negative eigenspace away
from the newborn eigenvalue has dimension at most one. -/
theorem evenNewborn_odd_negative_eigenspace_finrank_le_one
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .even L K hL) (lam : ℝ) (hlam : lam < 0)
    (hne : lam ≠ poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) :
    Module.finrank ℂ (Module.End.eigenspace (poleNeutralOddCompressedCanonical L K) (lam : ℂ)) ≤ 1 := by
  apply eigenspace_finrank_le_one_of_visible _ _ (poleNeutralCubicPairingFunctional L K)
  intro w hw0 hw
  exact (evenNewborn_odd_negative_eigen_channels_visible s lam hlam hne w hw0 hw).1

theorem oddNewborn_even_negative_eigenspace_finrank_le_one
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL) (lam : ℝ) (hlam : lam < 0)
    (hne : lam ≠ poleNeutralOddRayleighBottom L K hL s.cutoff_lower) :
    Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (lam : ℂ)) ≤ 1 := by
  apply eigenspace_finrank_le_one_of_visible _ _ (poleNeutralCorrectedCubicFunctional L K)
  intro u hu0 hu
  exact (oddNewborn_even_negative_eigen_channels_visible s lam hlam hne u hu0 hu).1

end Zeta23.OPICARound4
