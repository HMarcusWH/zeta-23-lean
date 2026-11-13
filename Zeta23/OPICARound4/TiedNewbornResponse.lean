import Zeta23.OPICARound4.JointGroundBirth
import Zeta23.OPICARound4.NativeWitnessCosts

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

private theorem own_odd_newborn_ground_negative {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL) :
    poleNeutralOddRayleighBottom L K hL s.cutoff_lower < 0 := by
  have h := newborn_bottom_le_normalized_energy .odd hL K s
  exact lt_of_le_of_lt h.1 h.2

private theorem actual_odd_projection_zero_pairing (L : ℝ) (K : ℕ) (lam : ℝ)
    (g w : poleNeutralOddSubspace L K)
    (hp : poleNeutralOddShiftedKernelProjection L K lam g = 0)
    (hw : poleNeutralOddShiftedCanonical L K lam w = 0) : inner ℂ g w = 0 := by
  rw [poleNeutralOddShiftedKernelProjection,
    Submodule.orthogonalProjectionOnto_eq_zero_iff] at hp
  exact inner_eq_zero_symm.mp (hp w (LinearMap.mem_ker.mpr hw))

private theorem actual_odd_norm_smul (L : ℝ) (K : ℕ) (c : ℂ)
    (w : poleNeutralOddSubspace L K) : ‖c • w‖ = ‖c‖ * ‖w‖ := by
  change ‖c • w.val.val‖ = ‖c‖ * ‖w.val.val‖
  exact norm_smul c w.val.val

/-- At the actual odd first birth, the actual tied index response retains
the entire kernel and costs at most the reciprocal negative depth. The
negative sign follows from the newborn witness; no parity gap is assumed. -/
theorem actual_odd_newborn_tied_indexComplement_norm_le
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u) :
    ‖poleNeutralEvenEigen_indexComplementComponent hL K
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) u‖ ≤
      ‖poleNeutralCorrectedCubicSource L K u‖ * ‖poleNeutralCubicCompressionVector L K‖ /
        (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) := by
  let lam := poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
  let z := poleNeutralEvenEigen_indexComplementComponent hL K lam u
  have hlam : lam < 0 := by simpa only [lam, htie] using own_odd_newborn_ground_negative s
  obtain ⟨v, hv0, hv⟩ := exists_eigenmode_at_poleNeutralOddRayleighBottom hL K s.cutoff_lower
  have hvl : poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v := by
    simpa only [lam, htie] using hv
  have hvker : v ∈ LinearMap.ker (poleNeutralOddShiftedCanonical L K lam) := by
    apply LinearMap.mem_ker.mpr
    change poleNeutralOddCompressedCanonical L K v - (lam : ℂ) • v = 0
    rw [hvl, sub_self]
  have horth := poleNeutralEvenEigen_indexComplement_mem_kernel_orthogonal hL K lam u
  have hvz : inner ℂ v z = 0 := horth v hvker
  have hn := (nativeNewborn_negative_eigen_complement_bounds .odd s lam hlam v hv0 hvl z hvz).2.2
  have he := poleNeutral_even_eigen_complement_source_eq hL K s.cutoff_lower lam u hu
  change poleNeutralOddCompressedCanonical L K z - (lam : ℂ) • z =
    poleNeutralCorrectedCubicSource L K u • poleNeutralCubicCompressionVector L K at he
  change ‖z‖ ≤ ‖poleNeutralOddCompressedCanonical L K z - (lam : ℂ) • z‖ / (-lam) at hn
  rw [he, actual_odd_norm_smul] at hn
  exact hn

/-- The same actual source has a positive, finite moment-energy budget at
a negative tie when the odd side is its own newborn. The kernel pairing
vanishes by source compatibility, not by dropping a ground component. -/
theorem actual_odd_newborn_tied_active_source_moment_bounds
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ∧
    (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤
      ‖poleNeutralCorrectedCubicSource L K u‖^2 * ‖poleNeutralCubicCompressionVector L K‖^2 /
        (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) := by
  refine ⟨native_source_active_moment_pos_of_le_odd_bottom hL K s.cutoff_lower _ u hu htie.le hf, ?_⟩
  let lam := poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
  let f := poleNeutralCorrectedCubicSource L K u
  let g := poleNeutralCubicCompressionVector L K
  let z := poleNeutralEvenEigen_indexComplementComponent hL K lam u
  let k := poleNeutralEvenEigen_indexKernelComponent hL K lam u
  have hp0 := poleNeutral_even_eigen_shifted_kernel_compatibility hL K s.cutoff_lower lam u hu
  have hp : poleNeutralOddShiftedKernelProjection L K lam g = 0 :=
    (smul_eq_zero.mp hp0).resolve_left hf
  have hk : inner ℂ g (k : poleNeutralOddSubspace L K) = 0 :=
    actual_odd_projection_zero_pairing L K lam g k hp (LinearMap.mem_ker.mp k.property)
  have hd := poleNeutralEvenEigen_index_eq_kernel_add_complement hL K lam u
  have hm : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) = inner ℂ g z := by
    rw [← poleNeutral_cubic_pairing_eq_momentFour hL K u, hd]
    change inner ℂ g.val.val ((k : poleNeutralOddSubspace L K).val.val + z.val.val) =
      inner ℂ g.val.val z.val.val
    have hk' : inner ℂ g.val.val (k : poleNeutralOddSubspace L K).val.val = 0 := hk
    rw [inner_add_right, hk', zero_add]
  have he : (star f * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re =
      (inner ℂ (f • g) z).re := by
    change (star f * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re =
      (inner ℂ (f • g.val.val) z.val.val).re
    rw [inner_smul_left]
    have hm' : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) =
      inner ℂ g.val.val z.val.val := hm
    rw [hm', starRingEnd_apply]
  have hb : (star f * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤
      (‖f‖ * ‖g‖) * ‖z‖ := by
    rw [he]
    calc
      _ ≤ ‖f • g‖ * ‖z‖ := by simpa only [RCLike.re_eq_complex_re] using
        (re_inner_le_norm (𝕜 := ℂ) (f • g) z)
      _ = _ := by rw [actual_odd_norm_smul]
  have hn : ‖z‖ ≤ ‖f‖ * ‖g‖ / (-lam) :=
    actual_odd_newborn_tied_indexComplement_norm_le s htie u hu
  have hc := mul_le_mul_of_nonneg_left hn (mul_nonneg (norm_nonneg f) (norm_nonneg g))
  calc
    _ = (star f * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := rfl
    _ ≤ (‖f‖ * ‖g‖) * ‖z‖ := hb
    _ ≤ (‖f‖ * ‖g‖) * (‖f‖ * ‖g‖ / (-lam)) := hc
    _ = _ := by dsimp only [f, g, lam]; ring

/-- Source normalization preserves the tied state and yields a finite
positive fourth-moment interval without a strict parity gap. -/
theorem actual_odd_newborn_tied_normalized_moment_bounds
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u = 1) :
    0 < (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ∧
    (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤
      ‖poleNeutralCubicCompressionVector L K‖^2 /
        (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) := by
  have h := actual_odd_newborn_tied_active_source_moment_bounds s htie u hu
    (by rw [hf]; exact one_ne_zero)
  simpa only [hf, star_one, one_mul, norm_one, one_pow] using h

end Zeta23.OPICARound4
