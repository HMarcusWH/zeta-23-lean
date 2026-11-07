import Zeta23.OPICARound4.JointGroundBirth
import Zeta23.OPICARound4.NativeWitnessCosts
import Zeta23.CCM.CanonicalSourceEnergy
import Mathlib.Algebra.QuadraticDiscriminant

noncomputable section
namespace Zeta23.OPICARound4
open CCM OPICARound3
open scoped ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

private theorem actual_odd_projection_zero_pairing (L : ℝ) (K : ℕ) (lam : ℝ)
    (g w : poleNeutralOddSubspace L K)
    (hp : poleNeutralOddShiftedKernelProjection L K lam g = 0)
    (hw : poleNeutralOddShiftedCanonical L K lam w = 0) : inner ℂ g w = 0 := by
  rw [poleNeutralOddShiftedKernelProjection,
    Submodule.orthogonalProjectionOnto_eq_zero_iff] at hp
  exact inner_eq_zero_symm.mp (hp w (LinearMap.mem_ker.mpr hw))

/-- An active corrected source at an actual negative tie places the fixed
canonical cubic vector in the whole odd-ground complement. At the odd
side's own birth its unshifted canonical energy must therefore be nonnegative. -/
theorem actual_odd_newborn_tied_active_cubic_energy_nonneg
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :
    0 ≤ (inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re := by
  let lam := poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
  let g := poleNeutralCubicCompressionVector L K
  have hn := newborn_bottom_le_normalized_energy .odd hL K s
  have hlam : lam < 0 := by
    simpa only [lam, htie] using lt_of_le_of_lt hn.1 hn.2
  obtain ⟨v, hv0, hv⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K s.cutoff_lower
  have hvl : poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v := by
    simpa only [lam, htie] using hv
  have hp0 := poleNeutral_even_eigen_shifted_kernel_compatibility hL K s.cutoff_lower lam u hu
  have hp : poleNeutralOddShiftedKernelProjection L K lam g = 0 :=
    (smul_eq_zero.mp hp0).resolve_left hf
  have hvg : inner ℂ v g = 0 := by
    apply inner_eq_zero_symm.mp
    apply actual_odd_projection_zero_pairing L K lam g v hp
    change poleNeutralOddCompressedCanonical L K v - (lam : ℂ) • v = 0
    rw [hvl, sub_self]
  exact (nativeNewborn_negative_eigen_complement_bounds .odd s lam hlam v hv0 hvl g hvg).1

/-- The same necessary sign is on the complete production arithmetic energy,
including every von-Mangoldt prime-power atom and the archimedean scalar. -/
theorem actual_odd_newborn_tied_active_cubic_channel_nonneg
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :
    0 ≤ canonicalSourceChannelEnergy L K (poleNeutralCubicCompressionVector L K).val.val := by
  have h := actual_odd_newborn_tied_active_cubic_energy_nonneg s htie u hu hf
  rw [inner_poleNeutralOddCompressedCanonical_self,
    ← matrixRealEnergy_eq_re_inner_apply_self,
    matrixRealEnergy_canonicalSourceMatrix_eq_channels hL K] at h
  exact h

/-- Negative energy of the actual cubic vector rules out the active-source
branch and forces the retained whole odd kernel to see that vector. No even
simplicity or nonzero even-vector premise is needed; the tie is not excluded. -/
theorem actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hgneg : (inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re < 0) :
    poleNeutralCorrectedCubicSource L K u = 0 ∧
      poleNeutralOddShiftedKernelProjection L K
        (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower)
        (poleNeutralCubicCompressionVector L K) ≠ 0 := by
  have hf : poleNeutralCorrectedCubicSource L K u = 0 := by
    by_contra hn
    have hp := actual_odd_newborn_tied_active_cubic_energy_nonneg s htie u hu hn
    linarith
  refine ⟨hf, ?_⟩
  intro hp
  let lam := poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
  let g := poleNeutralCubicCompressionVector L K
  have hn := newborn_bottom_le_normalized_energy .odd hL K s
  have hlam : lam < 0 := by
    simpa only [lam, htie] using lt_of_le_of_lt hn.1 hn.2
  obtain ⟨v, hv0, hv⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K s.cutoff_lower
  have hvl : poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v := by
    simpa only [lam, htie] using hv
  have hvg : inner ℂ v g = 0 := by
    apply inner_eq_zero_symm.mp
    apply actual_odd_projection_zero_pairing L K lam g v hp
    change poleNeutralOddCompressedCanonical L K v - (lam : ℂ) • v = 0
    rw [hvl, sub_self]
  have hpos := (nativeNewborn_negative_eigen_complement_bounds .odd s lam hlam v hv0 hvl g hvg).1
  change 0 ≤ (inner ℂ (poleNeutralOddCompressedCanonical L K g) g).re at hpos
  exact (not_lt_of_ge hpos) hgneg

private theorem positive_re_inner_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (x y : E) :
    (inner ℂ (T x) y).re ^ 2 ≤ (inner ℂ (T x) x).re * (inner ℂ (T y) y).re := by
  let a := (inner ℂ (T x) x).re
  let b := (inner ℂ (T x) y).re
  let c := (inner ℂ (T y) y).re
  have hswap : (inner ℂ (T y) x).re = b := by
    rw [hT.1 y x]
    exact inner_re_symm (𝕜 := ℂ) _ _
  have hp (t : ℝ) : 0 ≤ a * (t * t) + (2 * b) * t + c := by
    have h := hT.2 ((t : ℂ) • x + y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      RCLike.re_eq_complex_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    rw [hswap] at h
    change 0 ≤ a * (t * t) + (2 * b) * t + c
    dsimp only [a, b, c] at h ⊢
    nlinarith only [h]
  have hd := discrim_le_zero hp
  change (2 * b)^2 - 4 * a * c ≤ 0 at hd
  change b^2 ≤ a * c
  nlinarith only [hd]

/-- An exact arithmetic-energy lower constraint for the source-normalized
fourth moment. It holds at any actual even eigenvalue below or at the odd
floor, with the entire index vector retained. No newborn hypothesis is used. -/
theorem actual_normalized_even_moment_cubic_energy_lower
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hle : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (hf : poleNeutralCorrectedCubicSource L K u = 1) :
    (‖poleNeutralCubicCompressionVector L K‖^2)^2 ≤
      (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re *
      ((inner ℂ (poleNeutralOddCompressedCanonical L K
        (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re -
        lam * ‖poleNeutralCubicCompressionVector L K‖^2) := by
  let g := poleNeutralCubicCompressionVector L K
  let y := poleNeutralIndexLinearMap hL K u
  let T : poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K :=
    poleNeutralOddCompressedCanonical L K -
    (lam : ℂ) • (LinearMap.id : poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K)
  have hT : LinearMap.IsPositive (𝕜 := ℂ) (E := poleNeutralOddSubspace L K) T :=
    poleNeutralOddShifted_isPositive_of_le_bottom hL K hK lam hle
  have hy : T y = g := by
    have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) u
    change poleNeutralOddCompressedCanonical L K y -
      poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
    rw [hu, map_smul, hf, one_smul] at hd
    exact hd
  have hn : (inner ℂ g g).re = ‖g‖^2 := by
    change (inner ℂ g.val.val g.val.val).re = ‖g.val.val‖^2
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) g.val.val).symm
  have hm : (inner ℂ g y).re =
      (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re :=
    congrArg Complex.re (poleNeutral_cubic_pairing_eq_momentFour hL K u)
  have he : (inner ℂ (T g) g).re =
      (inner ℂ (poleNeutralOddCompressedCanonical L K g) g).re - lam * ‖g‖^2 := by
    change (inner ℂ ((poleNeutralOddCompressedCanonical L K g).val.val -
      (lam : ℂ) • g.val.val) g.val.val).re = _
    rw [inner_sub_left, Complex.sub_re, inner_smul_left, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change _ - lam * (inner ℂ g g).re = _
    rw [hn]
    rfl
  have hc := positive_re_inner_sq_le T hT y g
  rw [hy, hn, hm, he] at hc
  exact hc

end Zeta23.OPICARound4
