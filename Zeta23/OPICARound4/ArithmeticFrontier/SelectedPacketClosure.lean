import Zeta23.OPICARound4.ClosureConsumers
import Zeta23.OPICARound4.RegularCells.PacketSpectralSelection
import Zeta23.OPICARound4.CommonQuarticGround

/-!
# A narrower consumer on the same selected regular packet

At the actual generated packet, the full even and odd native spectra are
disjoint at its detector cutoff. Both Rayleigh bottoms are genuine eigenvalues,
so they cannot tie there. The pointwise ground consumer therefore needs only
the two exact ground-response tests at that same state; no separate global
shared-ground exclusion and no uniformity over all cutoffs is required.

The ground-response tests are OPEN. The existing ground identities make each
response exactly one, so a restriction strictly below one contradicts the
packet. A favorable bound at an independently selected aperture does not
suffice: the restriction must hold on the eligible packet outputs themselves,
or one output must carry both the packet properties and the restriction.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM ExceptionalZero OPICARound3 Module.End

/-- The two exact native ground-response tests at one state `(L, K)`. -/
def NativeGroundResponseRestriction {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) : Prop :=
  (poleNeutralEvenRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs)).re < 1) ∧
  (poleNeutralOddRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs)).re < 1)

/-- Full cross-parity spectral disjointness at one native state. -/
def NativeSpectraDisjoint (L : ℝ) (K : ℕ) : Prop :=
  ∀ μ : ℂ, HasEigenvalue (nativePoleNeutralParityCanonical .even L K) μ →
    ¬ HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) μ

/-- Both Rayleigh bottoms are eigenvalues, so disjoint spectra forbid every
tie, negative or not. This is qualitative: no gap size follows. -/
theorem rayleighBottoms_ne_of_spectra_disjoint {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (hsep : NativeSpectraDisjoint L K) :
    poleNeutralEvenRayleighBottom L K hL hK ≠ poleNeutralOddRayleighBottom L K hL hK := by
  intro heq
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K hK
  obtain ⟨w, hw0, hw⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K hK
  rw [← heq] at hw
  exact hsep _ (hasEigenvalue_of_hasEigenvector (f := nativePoleNeutralParityCanonical .even L K)
      ⟨mem_eigenspace_iff.mpr hu, hu0⟩)
    (hasEigenvalue_of_hasEigenvector (f := nativePoleNeutralParityCanonical .odd L K)
      ⟨mem_eigenspace_iff.mpr hw, hw0⟩)

/-- Pointwise closure at a disjoint state: the two ground tests suffice. -/
theorem noBothNeg_of_ground_response_and_disjoint_spectra {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (hsep : NativeSpectraDisjoint L K)
    (hground : NativeGroundResponseRestriction hL K hK) : ¬ BothNeutralNegative L K :=
  noBothNeg_of_actual_ground_comparisons hL K hK hground.1 hground.2
    (fun h => rayleighBottoms_ne_of_spectra_disjoint hL K hK hsep h.1)

/-- The aperture of an actual generated packet. -/
def packetAperture {ρ : zetaZeroConfig.carrier} {β : ℝ} {p : ReversalParity} {R : ℝ}
    (out : GeneratedStep123ComposedEvidencePacket ρ β p R) : ℝ :=
  fixedOriginalSincTrialAperture out.integrated.boundary.generated.sourceData.separation

theorem packetAperture_pos {ρ : zetaZeroConfig.carrier} {β : ℝ} {p : ReversalParity} {R : ℝ}
    (out : GeneratedStep123ComposedEvidencePacket ρ β p R) : 0 < packetAperture out :=
  out.integrated.boundary.generated.native.aperture_pos

theorem packetAperture_gt {ρ : zetaZeroConfig.carrier} {β : ℝ} {p : ReversalParity} {R : ℝ}
    (out : GeneratedStep123ComposedEvidencePacket ρ β p R) : R < packetAperture out :=
  (le_max_left R 4).trans_lt out.integrated.boundary.generated.native_aperture_bound

theorem packetDetectorCutoff_three_le {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {p : ReversalParity} {R : ℝ} (out : GeneratedStep123ComposedEvidencePacket ρ β p R) :
    3 ≤ originalDetectorQuarticCutoff (packetAperture out) :=
  out.integrated.boundary.generated.native.retained.state.selection.cutoff_nonempty.trans
    out.integrated.boundary.generated.native.retained.state.selection.cutoff_le_detector

/-- **Narrow packet supplier.** On every sufficiently late eligible output of the
actual construction (disjoint at its own detector cutoff), both exact ground
tests hold at that packet's own aperture and cutoff. OPEN. -/
def SelectedPacketGroundRestriction (ρ : zetaZeroConfig.carrier) : Prop :=
  ∃ R1 : ℝ, ∀ (β : ℝ) (p : ReversalParity) (R : ℝ), R1 ≤ R →
    ∀ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      NativeSpectraDisjoint (packetAperture out) (originalDetectorQuarticCutoff (packetAperture out)) →
      NativeGroundResponseRestriction (packetAperture_pos out)
        (originalDetectorQuarticCutoff (packetAperture out)) (packetDetectorCutoff_three_le out)

/-- The packet-uniform restriction excludes the hypothetical zero. -/
theorem no_off_line_zero_of_selected_packet_ground_restriction
    (h : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2 → SelectedPacketGroundRestriction ρ) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  by_contra hoff
  obtain ⟨R0, hR0⟩ := NativeParityPencils.cofinally_actual_packet_joint_regular_disjoint_spectra ρ hoff
  obtain ⟨R1, hR1⟩ := h ρ hoff
  have hδ : 0 < |(ρ : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  obtain ⟨out, hboth, _, _, _, _, _, hsep⟩ :=
    hR0 (|(ρ : ℂ).re - 1 / 2| / 2) (by positivity) (by linarith) .even (max R0 R1) (le_max_left _ _)
  have hdisj : NativeSpectraDisjoint (packetAperture out)
      (originalDetectorQuarticCutoff (packetAperture out)) :=
    hsep _ (packetDetectorCutoff_three_le out) le_rfl
  exact noBothNeg_of_ground_response_and_disjoint_spectra (packetAperture_pos out) _
    (packetDetectorCutoff_three_le out) hdisj
    (hR1 _ .even _ (le_max_right _ _) out hdisj) hboth

/-- **Narrow state supplier**, free of the hypothetical zero: late disjoint states
at the literal quartic cutoff satisfy both exact ground tests. OPEN. -/
def EventualDisjointQuarticGroundRestriction : Prop :=
  ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ (hL : 0 < L) (hK : 3 ≤ originalDetectorQuarticCutoff L),
    NativeSpectraDisjoint L (originalDetectorQuarticCutoff L) →
      NativeGroundResponseRestriction hL (originalDetectorQuarticCutoff L) hK

theorem selected_packet_ground_restriction_of_eventual_disjoint
    (h : EventualDisjointQuarticGroundRestriction) (ρ : zetaZeroConfig.carrier) :
    SelectedPacketGroundRestriction ρ := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun β p R' hR' out hdisj => ?_⟩
  exact hR _ (lt_of_le_of_lt hR' (packetAperture_gt out)) _ _ hdisj

/-- **Conditional reduction.** The state supplier is OPEN. -/
theorem riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction
    (h : EventualDisjointQuarticGroundRestriction) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hm : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  exact no_off_line_zero_of_selected_packet_ground_restriction
    (fun ρ _ => selected_packet_ground_restriction_of_eventual_disjoint h ρ) ⟨s, hm⟩

/-- The older eventual ground wrapper is uniform in every cutoff and also
demands a separate shared-ground exclusion; it implies the narrow supplier. -/
theorem eventual_disjoint_quartic_ground_restriction_of_ground_closure
    (h : EventualNegativeGroundClosure) : EventualDisjointQuarticGroundRestriction := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun L hL hp hK _ => ?_⟩
  obtain ⟨he, ho, _⟩ := hR L hL hp _ hK
  exact ⟨he, ho⟩

/-- One-output form: for every threshold, some actual packet carries its own
detector disjointness and the ground restriction. Joint ground negativity of
every late packet is inherited from the existing construction. -/
def SelectedPacketWithGroundRestriction (ρ : zetaZeroConfig.carrier) : Prop :=
  ∀ R : ℝ, ∃ (β : ℝ) (p : ReversalParity) (out : GeneratedStep123ComposedEvidencePacket ρ β p R),
    NativeSpectraDisjoint (packetAperture out) (originalDetectorQuarticCutoff (packetAperture out)) ∧
      NativeGroundResponseRestriction (packetAperture_pos out)
        (originalDetectorQuarticCutoff (packetAperture out)) (packetDetectorCutoff_three_le out)

theorem no_off_line_zero_of_selected_packet_with_ground_restriction
    (h : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2 → SelectedPacketWithGroundRestriction ρ) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  by_contra hoff
  obtain ⟨R0, hR0⟩ := every_late_generated_packet_has_joint_detector_ground ρ hoff
  obtain ⟨β, p, out, hdisj, hground⟩ := h ρ hoff R0
  obtain ⟨hboth, _⟩ := hR0 β p R0 le_rfl out
  exact noBothNeg_of_ground_response_and_disjoint_spectra (packetAperture_pos out) _
    (packetDetectorCutoff_three_le out) hdisj hground hboth

end Zeta23.OPICARound4.ArithmeticFrontier
