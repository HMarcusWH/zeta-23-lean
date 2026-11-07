import Zeta23.OPICARound4.CommonQuarticGround

/-!
# Exact native moment slices at the literal quartic detector cutoff

The even slice is the actual even pole-neutral carrier with fourth centered
moment zero; the odd slice is the actual odd pole-neutral carrier with third
and fifth centered moments zero. Moments are those of the physical coordinate
vector itself. The boundary-flat and pole-neutral conditions are inherited
from the ambient carriers and are not restated or weakened.

The energy is the literal compressed canonical self-energy, and the norm is
the inherited Euclidean norm of the physical coordinate vector: exactly the
objects of `eventually_both_moment_slice_margins_at_original_quartic`.
These definitions supply no positivity and no arithmetic estimate.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero OPICARound3 Filter

/-- The literal centered moment of order `k` of the physical coordinates of an
even native carrier vector. -/
def evenPhysicalMoment (L : ℝ) (K k : ℕ) : poleNeutralEvenSubspace L K →ₗ[ℂ] ℂ :=
  (centeredMomentLinearMap K k).comp
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).toLinearEquiv.toLinearMap.comp
      ((euclideanEvenBoundaryFlatSubspace K).subtype.comp
        (poleNeutralEvenSubspace L K).subtype))

/-- The literal centered moment of order `k` of the physical coordinates of an
odd native carrier vector. -/
def oddPhysicalMoment (L : ℝ) (K k : ℕ) : poleNeutralOddSubspace L K →ₗ[ℂ] ℂ :=
  (centeredMomentLinearMap K k).comp
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).toLinearEquiv.toLinearMap.comp
      ((euclideanOddBoundaryFlatSubspace K).subtype.comp
        (poleNeutralOddSubspace L K).subtype))

theorem evenPhysicalMoment_apply (L : ℝ) (K k : ℕ) (u : poleNeutralEvenSubspace L K) :
    evenPhysicalMoment L K k u =
      centeredMoment K k ((EuclideanSpace.equiv _ ℂ) u.val.val) := rfl

theorem oddPhysicalMoment_apply (L : ℝ) (K k : ℕ) (v : poleNeutralOddSubspace L K) :
    oddPhysicalMoment L K k v =
      centeredMoment K k ((EuclideanSpace.equiv _ ℂ) v.val.val) := rfl

/-- The even quartic moment slice: fourth centered physical moment zero. -/
def evenMomentSlice (L : ℝ) (K : ℕ) : Submodule ℂ (poleNeutralEvenSubspace L K) :=
  LinearMap.ker (evenPhysicalMoment L K 4)

/-- The odd moment slice: third and fifth centered physical moments zero. -/
def oddMomentSlice (L : ℝ) (K : ℕ) : Submodule ℂ (poleNeutralOddSubspace L K) :=
  LinearMap.ker (oddPhysicalMoment L K 3) ⊓ LinearMap.ker (oddPhysicalMoment L K 5)

theorem mem_evenMomentSlice_iff (L : ℝ) (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    u ∈ evenMomentSlice L K ↔
      centeredMoment K 4 ((EuclideanSpace.equiv _ ℂ) u.val.val) = 0 := Iff.rfl

theorem mem_oddMomentSlice_iff (L : ℝ) (K : ℕ) (v : poleNeutralOddSubspace L K) :
    v ∈ oddMomentSlice L K ↔
      centeredMoment K 3 ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 ∧
        centeredMoment K 5 ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 := Iff.rfl

/-- The literal even native self-energy; no normalization is inserted. -/
def evenNativeEnergy (L : ℝ) (K : ℕ) (u : poleNeutralEvenSubspace L K) : ℝ :=
  (inner ℂ (poleNeutralEvenCompressedCanonical L K u) u).re

/-- The literal odd native self-energy; no normalization is inserted. -/
def oddNativeEnergy (L : ℝ) (K : ℕ) (v : poleNeutralOddSubspace L K) : ℝ :=
  (inner ℂ (poleNeutralOddCompressedCanonical L K v) v).re

/-- An all-vector lower bound on the entire even slice, measured in the
inherited physical norm. A positive trial vector does not establish it. -/
def EvenMomentSliceLowerBound (L : ℝ) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ u : poleNeutralEvenSubspace L K, u ∈ evenMomentSlice L K →
    -ε * ‖u‖ ^ 2 ≤ evenNativeEnergy L K u

/-- An all-vector lower bound on the entire odd slice, in the physical norm. -/
def OddMomentSliceLowerBound (L : ℝ) (K : ℕ) (ε : ℝ) : Prop :=
  ∀ v : poleNeutralOddSubspace L K, v ∈ oddMomentSlice L K →
    -ε * ‖v‖ ^ 2 ≤ oddNativeEnergy L K v

/-- One parity, chosen once for the whole state, covers its entire slice. -/
def MomentSliceLowerBound (L : ℝ) (K : ℕ) (ε : ℝ) : Prop :=
  EvenMomentSliceLowerBound L K ε ∨ OddMomentSliceLowerBound L K ε

/-- **Contract (C1).** Cofinal vanishing-error bounds on the actual moment
slices at the literal quartic detector cutoff. No fixed parity, compression
rank, positive gap or estimate between the selected apertures is required.
This proposition is OPEN; defining it proves nothing about it. -/
def CofinalMomentSliceVanishingErrorBounds : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ) + 2 ≤ L ∧
    MomentSliceLowerBound L (originalDetectorQuarticCutoff L) (1 / (n : ℝ))

theorem EvenMomentSliceLowerBound.mono {L : ℝ} {K : ℕ} {ε ε' : ℝ}
    (h : EvenMomentSliceLowerBound L K ε) (hε : ε ≤ ε') :
    EvenMomentSliceLowerBound L K ε' := by
  intro u hu
  have hb := h u hu
  have hn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  nlinarith

theorem OddMomentSliceLowerBound.mono {L : ℝ} {K : ℕ} {ε ε' : ℝ}
    (h : OddMomentSliceLowerBound L K ε) (hε : ε ≤ ε') :
    OddMomentSliceLowerBound L K ε' := by
  intro v hv
  have hb := h v hv
  have hn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith

theorem MomentSliceLowerBound.mono {L : ℝ} {K : ℕ} {ε ε' : ℝ}
    (h : MomentSliceLowerBound L K ε) (hε : ε ≤ ε') :
    MomentSliceLowerBound L K ε' :=
  h.imp (fun he => he.mono hε) (fun ho => ho.mono hε)

/-- A whole-carrier Rayleigh-bottom bound restricts to the even slice. The
converse is not claimed: the slice bound is the weaker, narrower premise. -/
theorem evenMomentSliceLowerBound_of_bottom {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K)
    {ε : ℝ} (h : -ε ≤ poleNeutralEvenRayleighBottom L K hL hK) :
    EvenMomentSliceLowerBound L K ε := by
  intro u _
  have hb := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL K hK u
  have hn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  unfold evenNativeEnergy
  nlinarith

/-- A whole-carrier Rayleigh-bottom bound restricts to the odd slice. -/
theorem oddMomentSliceLowerBound_of_bottom {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K)
    {ε : ℝ} (h : -ε ≤ poleNeutralOddRayleighBottom L K hL hK) :
    OddMomentSliceLowerBound L K ε := by
  intro v _
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL K hK v
  have hn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  unfold oddNativeEnergy
  nlinarith

/-- The existing fixed-margin theorem, restated on the exact slices. The
witnesses are the literal moment-zero trial vectors, not ground eigenvectors. -/
theorem eventually_both_moment_slice_witnesses
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      (∃ u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),
        u ≠ 0 ∧ u ∈ evenMomentSlice L (originalDetectorQuarticCutoff L) ∧
        evenNativeEnergy L (originalDetectorQuarticCutoff L) u < -d * ‖u‖ ^ 2) ∧
      (∃ v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L),
        v ≠ 0 ∧ v ∈ oddMomentSlice L (originalDetectorQuarticCutoff L) ∧
        oddNativeEnergy L (originalDetectorQuarticCutoff L) v < -d * ‖v‖ ^ 2) := by
  obtain ⟨d, hd, h⟩ := eventually_both_moment_slice_margins_at_original_quartic ρ hoff
  refine ⟨d, hd, ?_⟩
  filter_upwards [h] with L hL
  obtain ⟨hL2, ⟨u, hu0, hu4, hue⟩, ⟨v, hv0, hv3, hv5, hve⟩⟩ := hL
  exact ⟨hL2, ⟨u, hu0, hu4, hue⟩, ⟨v, hv0, ⟨hv3, hv5⟩, hve⟩⟩

/-- Under an off-line zero, one margin is fixed before every late aperture:
no slice bound with tolerance below it holds in either parity. -/
theorem eventually_no_moment_slice_lower_bound_below_margin
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ L : ℝ in atTop, ∀ ε : ℝ, ε < d →
      ¬ MomentSliceLowerBound L (originalDetectorQuarticCutoff L) ε := by
  obtain ⟨d, hd, h⟩ := eventually_both_moment_slice_witnesses ρ hoff
  refine ⟨d, hd, ?_⟩
  filter_upwards [h] with L hL
  obtain ⟨_, ⟨u, hu0, hus, hue⟩, ⟨v, hv0, hvs, hve⟩⟩ := hL
  intro ε hε hb
  rcases hb with he | ho
  · have hl := he u hus
    have hn : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
    have hp := mul_pos (sub_pos.mpr hε) hn
    nlinarith
  · have hl := ho v hvs
    have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
    have hp := mul_pos (sub_pos.mpr hε) hn
    nlinarith

end Zeta23.OPICARound4.ArithmeticFrontier
