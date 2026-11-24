import Zeta23.OPICASupport.ApertureSlack.FormStability
import Zeta23.CCM.CanonicalGroundContinuity
import Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates
import Zeta23.OPICASupport.CofinalAperture.Sampling

/-!
Direct aperture-slack refinement of the literal native C1 contract.
The proof changes aperture on the left of a fixed quartic ceiling, using
strict error slack and the full physical Gram. It uses no C1-to-RH reduction.
-/
noncomputable section

open Filter Set
open scoped Topology

namespace Zeta23.OPICARound22.ApertureSlack

open CCM OPICARound4.ArithmeticFrontier OPICARound4.RegularCells
open OPICARound21.CofinalAperture

private abbrev Ambient (K : ℕ) := EuclideanSpace ℂ (Fin (2 * K + 1))

private def seedDiagonalCLM (K : ℕ) (L : ℝ) : Ambient K →L[ℂ] Ambient K :=
  Matrix.toEuclideanCLM (n := Fin (2 * K + 1)) (𝕜 := ℂ) (Matrix.diagonal (fun i => (fixedSeedDiagonalEntry L K i : ℂ)))

private theorem seedDiagonalCLM_apply (K : ℕ) (L : ℝ) (y : Fin (2 * K + 1) → ℂ) :
    seedDiagonalCLM K L (WithLp.toLp 2 y) =
      WithLp.toLp 2 (fixedSeedDiagonal L K y) := by
  simp only [seedDiagonalCLM, Matrix.toEuclideanCLM_toLp]
  congr 1
  funext i
  exact Matrix.mulVec_diagonal _ _ i

private theorem continuous_seedDiagonalCLM (K : ℕ) : Continuous (seedDiagonalCLM K) := by
  have hd : Continuous (fun L : ℝ => fun i : Fin (2 * K + 1) =>
      (fixedSeedDiagonalEntry L K i : ℂ)) := by
    apply continuous_pi
    intro i
    unfold fixedSeedDiagonalEntry fixedSeedParameter
    fun_prop
  have hto : Continuous (Matrix.toEuclideanCLM (n := Fin (2 * K + 1)) (𝕜 := ℂ)) :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin (2 * K + 1)) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact hto.comp hd.matrix_diagonal

/-- The shifted seed operator retains the physical Gram D*D. -/
private def shiftedSeedOperator (K : ℕ) (ε L : ℝ) : Ambient K →L[ℂ] Ambient K :=
  (seedDiagonalCLM K L).adjoint.comp
    ((Matrix.toEuclideanCLM (n := Fin (2 * K + 1)) (𝕜 := ℂ) (canonicalSourceMatrix L K) +
      (ε : ℂ) • ContinuousLinearMap.id ℂ (Ambient K)).comp (seedDiagonalCLM K L))

private theorem continuousAt_shiftedSeedOperator (K : ℕ) (ε : ℝ)
    {L : ℝ} (hL : 0 < L) : ContinuousAt (shiftedSeedOperator K ε) L := by
  have hD := (continuous_seedDiagonalCLM K).continuousAt (x := L)
  have hA := (continuousOn_canonicalSourceMatrix_toEuclideanCLM_Ioi K).continuousAt
    (Ioi_mem_nhds hL)
  have hAdj : ContinuousAt (fun t => (seedDiagonalCLM K t).adjoint) L :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp hD
  exact hAdj.clm_comp ((hA.add continuousAt_const).clm_comp hD)

private theorem shiftedSeedOperator_self (K : ℕ) (ε L : ℝ)
    (y : Fin (2 * K + 1) → ℂ) :
    (inner ℂ (shiftedSeedOperator K ε L (WithLp.toLp 2 y)) (WithLp.toLp 2 y)).re =
      (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin
        (WithLp.toLp 2 (fixedSeedDiagonal L K y)))
        (WithLp.toLp 2 (fixedSeedDiagonal L K y))).re +
      ε * (fixedSeedGram L K y y).re := by
  simp only [shiftedSeedOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, Complex.add_re, seedDiagonalCLM_apply]
  rw [fixedSeedGram_eq_physical_inner, _root_.inner_smul_left, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

private theorem shiftedSeedOperator_even (K : ℕ) (ε : ℝ) {L : ℝ} (hL : 0 < L)
    (y : fixedEvenMomentSeed K) :
    (inner ℂ (shiftedSeedOperator K ε L (WithLp.toLp 2 y.val)) (WithLp.toLp 2 y.val)).re =
      evenNativeEnergy L K (evenMomentSliceSeedEquiv hL K y).val +
        ε * (fixedSeedGram L K y.val y.val).re := by
  rw [shiftedSeedOperator_self, evenNativeEnergy,
    inner_poleNeutralEvenCompressedCanonical_self]
  rfl

private theorem shiftedSeedOperator_odd (K : ℕ) (ε : ℝ) {L : ℝ} (hL : 0 < L)
    (y : fixedOddMomentSeed K) :
    (inner ℂ (shiftedSeedOperator K ε L (WithLp.toLp 2 y.val)) (WithLp.toLp 2 y.val)).re =
      oddNativeEnergy L K (oddMomentSliceSeedEquiv hL K y).val +
        ε * (fixedSeedGram L K y.val y.val).re := by
  rw [shiftedSeedOperator_self, oddNativeEnergy,
    inner_poleNeutralOddCompressedCanonical_self]
  rfl

/-- Spending strictly positive error slack makes the exact physical even
whole-slice bound stable near a positive aperture, at a fixed cutoff. -/
theorem evenMomentSliceLowerBound_eventually_of_slack
    {L₀ ε ε' : ℝ} (hL : 0 < L₀) (K : ℕ) (hε : ε < ε')
    (hbound : EvenMomentSliceLowerBound L₀ K ε) :
    ∀ᶠ L in 𝓝 L₀, EvenMomentSliceLowerBound L K ε' := by
  let μ := (ε' - ε) * fixedSeedParameter L₀ ^ 2
  have hβ : 0 < fixedSeedParameter L₀ := by
    unfold fixedSeedParameter
    positivity
  have hμ : 0 < μ := mul_pos (sub_pos.mpr hε) (sq_pos_of_pos hβ)
  let S : Set (Ambient K) := {x | ∃ y : fixedEvenMomentSeed K, x = WithLp.toLp 2 y.val}
  have hm : ∀ x ∈ S, μ * ‖x‖ ^ 2 ≤ (inner ℂ (shiftedSeedOperator K ε' L₀ x) x).re := by
    rintro x ⟨y, rfl⟩
    rw [shiftedSeedOperator_even K ε' hL]
    have hb := (evenMomentSliceLowerBound_iff_seed_gram hL K ε).mp hbound y
    have hg := mul_le_mul_of_nonneg_left (fixedSeedGram_re_ge L₀ K y.val)
      (sub_nonneg.mpr hε.le)
    have hn : ‖(WithLp.toLp 2 y.val : Ambient K)‖ ^ 2 = seedCoordinateNormSq K y.val := by
      simp only [EuclideanSpace.norm_sq_eq, seedCoordinateNormSq]
    rw [hn]
    dsimp [μ]
    nlinarith
  have hev := eventually_lower_bound_on_set_of_operator_continuity
    (continuousAt_shiftedSeedOperator K ε' hL) S hμ hm
  filter_upwards [hev, eventually_gt_nhds hL] with L he hpos
  apply (evenMomentSliceLowerBound_iff_seed_gram hpos K ε').mpr
  intro y
  have h := he (WithLp.toLp 2 y.val) ⟨y, rfl⟩
  rw [shiftedSeedOperator_even K ε' hpos] at h
  have hnonneg : 0 ≤ μ / 2 * ‖(WithLp.toLp 2 y.val : Ambient K)‖ ^ 2 := by positivity
  linarith

/-- The same direct stability result for the exact physical odd slice. -/
theorem oddMomentSliceLowerBound_eventually_of_slack
    {L₀ ε ε' : ℝ} (hL : 0 < L₀) (K : ℕ) (hε : ε < ε')
    (hbound : OddMomentSliceLowerBound L₀ K ε) :
    ∀ᶠ L in 𝓝 L₀, OddMomentSliceLowerBound L K ε' := by
  let μ := (ε' - ε) * fixedSeedParameter L₀ ^ 2
  have hβ : 0 < fixedSeedParameter L₀ := by
    unfold fixedSeedParameter
    positivity
  have hμ : 0 < μ := mul_pos (sub_pos.mpr hε) (sq_pos_of_pos hβ)
  let S : Set (Ambient K) := {x | ∃ y : fixedOddMomentSeed K, x = WithLp.toLp 2 y.val}
  have hm : ∀ x ∈ S, μ * ‖x‖ ^ 2 ≤ (inner ℂ (shiftedSeedOperator K ε' L₀ x) x).re := by
    rintro x ⟨y, rfl⟩
    rw [shiftedSeedOperator_odd K ε' hL]
    have hb := (oddMomentSliceLowerBound_iff_seed_gram hL K ε).mp hbound y
    have hg := mul_le_mul_of_nonneg_left (fixedSeedGram_re_ge L₀ K y.val)
      (sub_nonneg.mpr hε.le)
    have hn : ‖(WithLp.toLp 2 y.val : Ambient K)‖ ^ 2 = seedCoordinateNormSq K y.val := by
      simp only [EuclideanSpace.norm_sq_eq, seedCoordinateNormSq]
    rw [hn]
    dsimp [μ]
    nlinarith
  have hev := eventually_lower_bound_on_set_of_operator_continuity
    (continuousAt_shiftedSeedOperator K ε' hL) S hμ hm
  filter_upwards [hev, eventually_gt_nhds hL] with L he hpos
  apply (oddMomentSliceLowerBound_iff_seed_gram hpos K ε').mpr
  intro y
  have h := he (WithLp.toLp 2 y.val) ⟨y, rfl⟩
  rw [shiftedSeedOperator_odd K ε' hpos] at h
  have hnonneg : 0 ≤ μ / 2 * ‖(WithLp.toLp 2 y.val : Ambient K)‖ ^ 2 := by positivity
  linarith


/-- Exact C1 with the additional requirement that every selected aperture
avoid resonance for every actual complex zero coordinate. -/
def GoodApertureC1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ) + 2 ≤ L ∧
    (∀ ρ : zetaZeroConfig.carrier,
      Complex.exp (Complex.I * gammaOf (ρ : ℂ) * (L : ℂ)) ≠ 1) ∧
    MomentSliceLowerBound L (originalDetectorQuarticCutoff L) (1 / (n : ℝ))

/-- The left interval preserves the ceiling even when L₀^4 is an integer. -/
private theorem exists_good_left_aperture {L₀ A : ℝ} (hL : 0 < L₀) (hA : A < L₀)
    {P : ℝ → Prop} (hP : ∀ᶠ L in 𝓝 L₀, P L) :
    ∃ L : ℝ, A < L ∧ L < L₀ ∧
      originalDetectorQuarticCutoff L = originalDetectorQuarticCutoff L₀ ∧
      (∀ ρ : zetaZeroConfig.carrier,
        Complex.exp (Complex.I * gammaOf (ρ : ℂ) * (L : ℂ)) ≠ 1) ∧ P L := by
  have hK : Nat.ceil (L₀ ^ 4) ≠ 0 := by
    intro hz
    exact (not_le_of_gt (pow_pos hL 4)) (Nat.ceil_eq_zero.mp hz)
  have hc := (Nat.ceil_eq_iff hK).mp (rfl : Nat.ceil (L₀ ^ 4) = Nat.ceil (L₀ ^ 4))
  have hp : ∀ᶠ L in 𝓝 L₀, ((Nat.ceil (L₀ ^ 4) - 1 : ℕ) : ℝ) < L ^ 4 :=
    (continuousAt_id.pow 4).tendsto.eventually (eventually_gt_nhds hc.1)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hP.and ((eventually_gt_nhds hL).and ((eventually_gt_nhds hA).and hp)))
  obtain ⟨L, hlo, hhi, hgood⟩ := exists_actual_nonresonant_aperture_in_interval
    (show L₀ - δ < L₀ by linarith)
  have hd : dist L L₀ < δ := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hhi)]
    linarith
  obtain ⟨hPL, hpos, hAL, hpow⟩ := hnear hd
  refine ⟨L, hAL, hhi, ?_, hgood, hPL⟩
  apply (Nat.ceil_eq_iff hK).mpr
  exact ⟨hpow, (pow_le_pow_left₀ hpos.le hhi.le 4).trans hc.2⟩

/-- Dense simultaneous nonresonance can be added to native C1 by spending
error slack and moving slightly left with unchanged literal quartic cutoff.
This proof does not use C1⇒RH or any RH-derived positivity theorem. -/
theorem c1_iff_good_aperture_c1 :
    CofinalMomentSliceVanishingErrorBounds ↔ GoodApertureC1 := by
  constructor
  · intro hc n hn
    obtain ⟨L₀, hlarge, hbound⟩ := hc (2 * n) (by omega)
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    have hlarge' : 2 * (n : ℝ) + 2 ≤ L₀ := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlarge
    have hL : 0 < L₀ := by linarith
    have hA : (n : ℝ) + 2 < L₀ := by linarith
    have hε : 1 / ((2 * n : ℕ) : ℝ) < 1 / (n : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (one_div_lt_one_div_of_lt hnpos (show (n : ℝ) < 2 * (n : ℝ) by linarith))
    have hs : ∀ᶠ L in 𝓝 L₀,
        MomentSliceLowerBound L (originalDetectorQuarticCutoff L₀) (1 / (n : ℝ)) := by
      rcases hbound with he | ho
      · exact (evenMomentSliceLowerBound_eventually_of_slack hL _ hε he).mono
          (fun _ h => Or.inl h)
      · exact (oddMomentSliceLowerBound_eventually_of_slack hL _ hε ho).mono
          (fun _ h => Or.inr h)
    obtain ⟨L, hAL, _, hcut, hgood, hb⟩ := exists_good_left_aperture hL hA hs
    refine ⟨L, hAL.le, hgood, ?_⟩
    rw [hcut]
    exact hb
  · intro h n hn
    obtain ⟨L, hL, _, hb⟩ := h n hn
    exact ⟨L, hL, hb⟩

end Zeta23.OPICARound22.ApertureSlack
