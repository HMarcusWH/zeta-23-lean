import Zeta23.OPICARound4.RegularCells.NativeRegularBirthSelection

noncomputable section

namespace Zeta23.OPICARound4.RegularCells

open CCM ExceptionalZero OPICARound3 Complex Set Filter
open scoped Topology

/-- Continuity is for the literal fixed-source correlation, retaining its complete zero family. -/
theorem continuousAt_actual_original_phase_energy {σ a : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) :
    ContinuousAt (fun b : ℝ => (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ b)
      (fixedOriginalSincPhaseTrial σ b)).re) a := by
  have hc : ContinuousAt fixedOriginalSincCorrelation a := by
    have heq : fixedOriginalSincCorrelation =
        filteredZeroFamily fixedOriginalSincSquaredFilter (1/2 : ℂ) :=
      funext fixedOriginalSincCorrelation_eq_filteredFamily
    rw [heq]
    exact continuousAt_filteredZeroFamily_of_pos
      (absolutelySummable_originalSincSquaredFilter UniversalSinc.fixedScale_pos)
      (by norm_num) ha
  have hr : ContinuousAt fixedOriginalSincCorrelationReal a :=
    Complex.continuous_re.continuousAt.comp hc
  simpa only [fixedOriginalSincPhaseTrial_Weil_re hσ, Pi.add_apply, Pi.mul_apply] using
    (continuousAt_const.add (continuousAt_const.mul hr)).div_const fixedOriginalSincKernelL2Mass

/-- One source-only threshold converts a fourfold smooth margin at any actual separation
into the exact quartic, true-norm normalized original data. -/
theorem exists_actual_original_depth_transport_threshold :
    ∃ T : ℝ, ∀ (β σ R a : ℝ), 0 < β → (σ = 1 ∨ σ = -1) →
      UniversalSinc.fixedScale < a →
      max (max R 4) T < fixedOriginalSincTrialAperture a →
      (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
        (fixedOriginalSincPhaseTrial σ a)).re ≤
        -4 * Real.exp (β * fixedOriginalSincTrialAperture a) →
      ∃ d : OriginalDetectorPaddedFinitePhaseData β σ R, d.separation = a := by
  obtain ⟨Lm,hLm,hmass⟩ := exists_originalDetectorPaddedFinitePhase_mass_control_threshold
  obtain ⟨Lu,hLu,hunit⟩ := exists_originalDetectorPaddedFinitePhase_unit_threshold
  have hWlim := originalDetectorPaddedFinitePhaseWeilErrorBudget_mul_exp_tendsto_zero 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hWlim
  obtain ⟨Lw,hWsmall⟩ := eventually_atTop.1
    (hWlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let T := max (max Lm Lu) (max Lw originalDetectorPaddedImageThreshold)
  refine ⟨T,?_⟩
  intro β σ R a hβ hσ ha hlate hdeep
  let L := fixedOriginalSincTrialAperture a
  have hTL : T < L := (le_max_right _ _).trans_lt hlate
  have hLmL : Lm ≤ L := (le_max_left Lm Lu |>.trans (le_max_left _ _)).trans hTL.le
  have hLuL : Lu ≤ L := (le_max_right Lm Lu |>.trans (le_max_left _ _)).trans hTL.le
  have hLwL : Lw ≤ L := (le_max_left Lw originalDetectorPaddedImageThreshold |>.trans
    (le_max_right _ _)).trans hTL.le
  have hImage : originalDetectorPaddedImageThreshold < L :=
    (le_max_right Lw originalDetectorPaddedImageThreshold |>.trans
      (le_max_right _ _)).trans_lt hTL
  have hLp : 0 < L := (by norm_num : (0:ℝ)<2).trans_le (hLm.trans hLmL)
  have hm := hmass σ a hσ ha hLp hLmL
  have hu := hunit σ a hσ ha hLp hLuL
  have herr := originalDetectorPaddedFinitePhase_Weil_error_le hσ ha hLp
  have hlt := herr.trans_lt (hWsmall L hLwL)
  have hRe := (Complex.re_le_norm _).trans_lt hlt
  have hE : 1 ≤ Real.exp (β * L) := Real.one_le_exp_iff.mpr (mul_nonneg hβ.le hLp.le)
  have hfinite : (zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)
      (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)).re ≤ -3 * Real.exp (β*L) := by
    change _ - _ < 1 at hRe
    linarith
  refine ⟨{
    separation := a
    aperture_pos := hLp
    separation_gt_scale := ha
    late := (le_max_left _ _).trans_lt hlate
    image_threshold_paid := hImage
    unit := hu.2
    depth := ?_
    original_depth := hdeep },rfl⟩
  rw [originalDetectorPaddedFinitePhaseUnitVector_nativeEnergy_eq_Weil_div_mass
    (UniversalSinc.fixedScale_pos.le.trans ha.le) σ hLp hu.1]
  apply (div_le_iff₀ (lt_trans (by norm_num : (0:ℝ)<1/2) hm.1)).mpr
  have hmul := mul_le_mul_of_nonneg_left
    (hm.2.le.trans (by norm_num : (3/2:ℝ)≤3)) (Real.exp_pos (β*L)).le
  linarith

/-- The selector acts only after a bounded open interval of genuine original exponential
depth has been fixed. The actual source data and retained state are then constructed there. -/
theorem exists_actual_generated_packet_with_open_selection
    (P : ℝ → ℕ → Prop)
    (hmono : ∀ L N K, K ≤ N → P L N → P L K)
    (hselect : ∀ N (J : Set ℝ), IsOpen J → J.Nonempty → J ⊆ Ioi 1 →
      ∃ L ∈ J, P L N)
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123Output ρ β p R,
      P (fixedOriginalSincTrialAperture out.sourceData.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture out.sourceData.separation)) := by
  obtain ⟨T,hT⟩ := exists_actual_original_depth_transport_threshold
  obtain ⟨Lu,hLu,hunit⟩ := exists_originalDetectorPaddedFinitePhase_unit_threshold
  let σ := nativeOriginalDetectorPhaseSign p
  have hσ : σ = 1 ∨ σ = -1 := by cases p <;> simp [σ,nativeOriginalDetectorPhaseSign]
  let B := max (max (max (max R 4) T) Lu)
    (2 * UniversalSinc.fixedScale + 2 * fixedOriginalSincLobeCenter)
  obtain ⟨β',hββ',hβ'ρ⟩ := exists_between hβρ
  obtain ⟨d0⟩ := originalDetectorPaddedFinitePhase_producer ρ
    (hβ.trans hββ') hβ'ρ hσ B
  let L0 := fixedOriginalSincTrialAperture d0.separation
  have hBL : B < L0 := (le_max_left B 4).trans_lt d0.late
  have hL0p : 0 < L0 := d0.aperture_pos
  have hsep : L0/2-fixedOriginalSincLobeCenter=d0.separation := by
    dsimp [L0,fixedOriginalSincTrialAperture]; ring
  let E : ℝ → ℝ := fun L =>
    (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ (L/2-fixedOriginalSincLobeCenter))
      (fixedOriginalSincPhaseTrial σ (L/2-fixedOriginalSincLobeCenter))).re +
        4 * Real.exp (β*L)
  have hcont : ContinuousAt E L0 := by
    have hc := continuousAt_actual_original_phase_energy hσ
      (UniversalSinc.fixedScale_pos.trans d0.separation_gt_scale)
    have hf : ContinuousAt (fun L : ℝ => L/2-fixedOriginalSincLobeCenter) L0 := by fun_prop
    have hc' : ContinuousAt (fun L : ℝ =>
        (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ (L/2-fixedOriginalSincLobeCenter))
          (fixedOriginalSincPhaseTrial σ (L/2-fixedOriginalSincLobeCenter))).re) L0 := by
      have hc'' : ContinuousAt (fun b : ℝ => (zetaZeroConfig.W
          (fixedOriginalSincPhaseTrial σ b) (fixedOriginalSincPhaseTrial σ b)).re)
          (L0/2-fixedOriginalSincLobeCenter) := by simpa only [hsep] using hc
      exact ContinuousAt.comp (f := fun L : ℝ => L/2-fixedOriginalSincLobeCenter)
        (x := L0) hc'' hf
    exact hc'.add (by fun_prop)
  have hnegative : E L0 < 0 := by
    have hexp : Real.exp (β*L0) < Real.exp (β'*L0) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hββ' hL0p)
    have hd := d0.original_depth
    dsimp [E]
    rw [hsep]
    linarith
  have hn : {L | E L < 0} ∈ 𝓝 L0 := hcont.preimage_mem_nhds (Iio_mem_nhds hnegative)
  obtain ⟨V,hVsub,hVo,hL0V⟩ := mem_nhds_iff.mp hn
  let J := V ∩ Ioo B (L0+1)
  have hJo : IsOpen J := hVo.inter isOpen_Ioo
  have hJn : J.Nonempty := ⟨L0,hL0V,hBL,by linarith⟩
  have hB4 : 4 ≤ B := (le_max_right R 4 |>.trans (le_max_left _ _) |>.trans
    (le_max_left _ _)).trans (le_max_left _ _)
  have hJp : J ⊆ Ioi 1 := by intro L hL; have := hL.2.1; change 1<L; linarith
  let N := Nat.ceil ((L0+1)^4)
  obtain ⟨L,hLJ,hPL⟩ := hselect N J hJo hJn hJp
  have hLB : B < L := hLJ.2.1
  have hLp : 0 < L := lt_trans zero_lt_one (hJp hLJ)
  let a := L/2-fixedOriginalSincLobeCenter
  have hLa : fixedOriginalSincTrialAperture a = L := by
    dsimp [a,fixedOriginalSincTrialAperture]; ring
  have ha : UniversalSinc.fixedScale < a := by
    have hlow := (le_max_right _ _).trans_lt hLB
    dsimp [a]; linarith
  have hlate : max (max R 4) T < fixedOriginalSincTrialAperture a := by
    rw [hLa]
    exact (le_max_left _ _ |>.trans (le_max_left _ _)).trans_lt hLB
  have hdeep : (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a)
      (fixedOriginalSincPhaseTrial σ a)).re ≤ -4*Real.exp (β*fixedOriginalSincTrialAperture a) := by
    have hv := hVsub hLJ.1
    change E L < 0 at hv
    rw [hLa]
    dsimp [E] at hv
    dsimp [a]
    linarith
  obtain ⟨d,hd⟩ := hT β σ R a hβ hσ ha hlate hdeep
  have hdL : fixedOriginalSincTrialAperture d.separation=L := by rw [hd,hLa]
  have hLuL : Lu ≤ fixedOriginalSincTrialAperture d.separation := by
    rw [hdL]
    exact (le_max_right _ _ |>.trans (le_max_left _ _)).trans hLB.le
  have he := hunit 1 d.separation (Or.inl rfl) d.separation_gt_scale d.aperture_pos hLuL
  have ho := hunit (-1) d.separation (Or.inr rfl) d.separation_gt_scale d.aperture_pos hLuL
  have hKd : 3 ≤ originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation) := by
    have h2 := d.two_le_aperture
    have hs : 4 ≤ fixedOriginalSincTrialAperture d.separation ^ 2 := by nlinarith
    have hf : (3:ℝ) ≤ fixedOriginalSincTrialAperture d.separation ^ 4 := by
      nlinarith [sq_nonneg (fixedOriginalSincTrialAperture d.separation ^ 2-4)]
    have hc := Nat.le_ceil (fixedOriginalSincTrialAperture d.separation ^ 4)
    exact_mod_cast hf.trans hc
  have hu : ‖nativeOriginalDetectorPaddedUnit p fixedOriginalSincLobeCenter d.two_le_aperture‖=1 := by
    cases p <;> exact d.unit
  have hdepth : (inner ℂ (nativePoleNeutralParityCanonical p
      (fixedOriginalSincTrialAperture d.separation)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
      (nativeOriginalDetectorPaddedUnit p fixedOriginalSincLobeCenter d.two_le_aperture))
      (nativeOriginalDetectorPaddedUnit p fixedOriginalSincLobeCenter d.two_le_aperture)).re ≤
        -Real.exp (β*fixedOriginalSincTrialAperture d.separation) := by
    cases p
    · exact (originalDetectorPaddedFiniteEvenPhaseUnit_energy fixedOriginalSincLobeCenter
        d.two_le_aperture).symm ▸ d.depth
    · exact (originalDetectorPaddedFiniteOddPhaseUnit_energy fixedOriginalSincLobeCenter
        d.two_le_aperture).symm ▸ d.depth
  obtain ⟨state,hstate⟩ := exists_detectorRetainedSchurState_of_original_native_trial p
    d.aperture_pos _ hKd _ (Real.exp_pos _)
    (nativeOriginalDetectorPaddedUnit p fixedOriginalSincLobeCenter d.two_le_aperture) hu hdepth
  have hlarge : 4 < fixedOriginalSincTrialAperture d.separation :=
    (le_max_right R 4).trans_lt d.late
  have hsel := admissibleDetectorSelector_of_actual_ground hlarge he.1 ho.1 he.2 ho.2 state.selection
  let out := GeneratedStep123Output.fromActualRetained ρ hβ hβρ p d state hstate hsel
  refine ⟨out,?_⟩
  change P (fixedOriginalSincTrialAperture d.separation)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
  rw [hdL]
  apply hmono L N _ _ hPL
  apply Nat.ceil_mono
  exact pow_le_pow_left₀ hLp.le hLJ.2.2.le 4

/-- Actual regular-selection consumer: one genuine generated packet retains its exponential
depth, source normalization, and mandated detector while all smaller native cutoffs are regular. -/
theorem exists_actual_generated_packet_native_regular
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123Output ρ β p R,
      ∀ q K, K ≤ originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture out.sourceData.separation) →
        Function.Bijective (nativePoleNeutralParityCanonical q
          (fixedOriginalSincTrialAperture out.sourceData.separation) K) := by
  apply exists_actual_generated_packet_with_open_selection
    (fun L N => ∀ q K, K ≤ N → Function.Bijective (nativePoleNeutralParityCanonical q L K))
    (fun L N K hKN h q j hj => h q j (hj.trans hKN))
    (fun N J hJo hJn hJp => exists_bounded_native_regular_in_open_positive N hJo hJn
      (by intro L hL; exact lt_trans (by norm_num : (0:ℝ)<1) (hJp hL)))
    ρ hβ hβρ p R

/-- Boundary, arithmetic and spectral evidence extend the SAME selected original packet. -/
theorem exists_actual_composed_packet_native_regular
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      ∀ q K, K ≤ originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture out.integrated.boundary.generated.sourceData.separation) →
        Function.Bijective (nativePoleNeutralParityCanonical q
          (fixedOriginalSincTrialAperture out.integrated.boundary.generated.sourceData.separation) K) := by
  obtain ⟨g,hg⟩ := exists_actual_generated_packet_native_regular ρ hβ hβρ p R
  exact ⟨GeneratedStep123ComposedEvidencePacket.fromIntegrated
    (GeneratedStep123IntegratedPacket.fromActualBoundary
      (GeneratedStep123BoundaryPacket.fromActualGenerated g)),hg⟩

/-- One threshold precedes exponent, phase and packet selection. The generated packet has
its original exponential detector depth, both native negative parities at that detector,
all joint ground constraints, and regularity at every cutoff up to the SAME detector. -/
theorem cofinally_actual_regular_packet_joint_detector_ground
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ R0 : ℝ, ∀ (β : ℝ), 0 < β → β < |(ρ : ℂ).re - 1/2| →
      ∀ (p : ReversalParity) (R : ℝ), R0 ≤ R →
      ∃ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      let g := out.integrated.boundary.generated
      let native := g.native
      let L := fixedOriginalSincTrialAperture g.sourceData.separation
      let Kd := originalDetectorQuarticCutoff L
      let hKd : 3 ≤ Kd := native.retained.state.selection.cutoff_nonempty.trans
        native.retained.state.selection.cutoff_le_detector
      BothNeutralNegative L Kd ∧
        NativeJointGroundConstraints native.aperture_pos Kd hKd ∧
        ‖native.retained.state.detector‖ = 1 ∧
        (inner ℂ (nativePoleNeutralParityCanonical p L Kd native.retained.state.detector)
          native.retained.state.detector).re ≤ -Real.exp (β*L) ∧
        native.retained.state.selection.cutoff ≤ Kd ∧
        ∀ q K, K ≤ Kd → Function.Bijective (nativePoleNeutralParityCanonical q L K) := by
  obtain ⟨R0,hR0⟩ := every_late_generated_packet_has_joint_detector_ground ρ hoff
  refine ⟨R0,?_⟩
  intro β hβ hβρ p R hR
  obtain ⟨out,hreg⟩ := exists_actual_composed_packet_native_regular ρ hβ hβρ p R
  have h := hR0 β p R hR out
  exact ⟨out,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,hreg⟩

end Zeta23.OPICARound4.RegularCells
