import Zeta23.OPICARound4.TiedCubicEnergy

noncomputable section
namespace Zeta23.OPICARound4
open CCM OPICARound3
open scoped ComplexConjugate

private theorem negative_eigen_energy_lower {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (B : F →ₗ[ℂ] F) (hB : B.IsSymmetric)
    (lam : ℝ) (v : F) (hv0 : v ≠ 0) (hv : B v = (lam : ℂ) • v)
    (hcomp : ∀ x : F, inner ℂ v x = 0 → 0 ≤ (inner ℂ (B x) x).re)
    (g : F) :
    (-(inner ℂ (B g) g).re) * ‖v‖^2 ≤ (-lam) * ‖inner ℂ g v‖^2 := by
  let n : ℝ := ‖v‖^2
  let c : ℂ := inner ℂ v g
  let a : F := c • v
  let x : F := (n : ℂ) • g - a
  have hn : 0 < n := by dsimp [n]; positivity
  have hself : inner ℂ v v = (n : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp only [n, Complex.ofReal_pow]
    rfl
  have hx : inner ℂ v x = 0 := by
    dsimp only [x, a]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hself]
    change (n : ℂ) * c - c * (n : ℂ) = 0
    ring
  have hp := hcomp x hx
  have ha : B a = (lam : ℂ) • a := by
    dsimp only [a]
    rw [map_smul, hv, smul_comm]
  have hax : inner ℂ a x = 0 := by
    dsimp only [a]
    rw [inner_smul_left, hx, mul_zero]
  have hxa : inner ℂ x a = 0 := inner_eq_zero_symm.mp hax
  have hc1 : inner ℂ (B x) a = 0 := by
    rw [hB x a, ha, inner_smul_right, hxa, mul_zero]
  have hc2 : inner ℂ (B a) x = 0 := by
    rw [ha, inner_smul_left, hax, mul_zero]
  have hnorm : ‖a‖^2 = ‖c‖^2 * n := by
    dsimp only [a, n]
    rw [norm_smul]
    ring
  have hdecomp : (n : ℂ) • g = x + a := by
    dsimp only [x]
    abel
  have hscale : (inner ℂ (B ((n : ℂ) • g)) ((n : ℂ) • g)).re =
      n^2 * (inner ℂ (B g) g).re := by
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have he : n^2 * (inner ℂ (B g) g).re =
      (inner ℂ (B x) x).re + lam * ‖c‖^2 * n := by
    rw [← hscale, hdecomp, map_add, inner_add_left, inner_add_right,
      inner_add_right, hc1, hc2, add_zero, zero_add, Complex.add_re,
      ha, re_inner_ofReal_smul_self, hnorm]
    ring
  have hp' : 0 ≤ n * (n * (inner ℂ (B g) g).re - lam * ‖c‖^2) := by
    nlinarith only [he, hp]
  have hr : 0 ≤ n * (inner ℂ (B g) g).re - lam * ‖c‖^2 :=
    nonneg_of_mul_nonneg_right hp' hn
  have hc : ‖c‖ = ‖inner ℂ g v‖ := norm_inner_symm (𝕜 := ℂ) v g
  rw [hc] at hr
  change (-(inner ℂ (B g) g).re) * n ≤ (-lam) * ‖inner ℂ g v‖^2
  nlinarith only [hr]

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- At the same actual odd birth, a source-silent tied even mode has a
quantitative fourth-moment lower constraint from the literal cubic energy.
The full odd ground complement is retained, without even simplicity. -/
theorem actual_odd_newborn_tied_silent_moment_depth_lower
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u = 0) :
    (-(inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re) *
      ‖poleNeutralIndexLinearMap hL K u‖^2 ≤
    (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) *
      ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)‖^2 := by
  have hK := s.cutoff_lower
  by_cases hu0 : u = 0
  · subst u
    simp [evenBoundaryFlatRawCoefficients, centeredMoment]
  let lam := poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
  let v := poleNeutralIndexLinearMap hL K u
  let g := poleNeutralCubicCompressionVector L K
  have hv0 : v ≠ 0 := by
    intro hz
    apply hu0
    apply poleNeutralIndexLinearMap_injective hL K
    simpa only [map_zero] using hz
  have hn := newborn_bottom_le_normalized_energy .odd hL K s
  have hlam : lam < 0 := by
    simpa only [lam, htie] using lt_of_le_of_lt hn.1 hn.2
  have hv : poleNeutralOddCompressedCanonical L K v = (lam : ℂ) • v := by
    have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) u
    change poleNeutralOddCompressedCanonical L K v -
      poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
    rw [hu, map_smul, hf, zero_smul] at hd
    exact sub_eq_zero.mp hd
  have hp (x : poleNeutralOddSubspace L K) (hx : inner ℂ v x = 0) :
      0 ≤ (inner ℂ (poleNeutralOddCompressedCanonical L K x) x).re :=
    (nativeNewborn_negative_eigen_complement_bounds .odd s lam hlam v hv0 hv x hx).1
  have h := @negative_eigen_energy_lower (poleNeutralOddSubspace L K) inferInstance
    (poleNeutralOdd_innerProductSpace L K) (poleNeutralOddCompressedCanonical L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K) lam v hv0 hv hp g
  rw [poleNeutral_cubic_pairing_eq_momentFour hL K u] at h
  exact h

/-- Negative literal cubic energy forces a normalized lower fourth-moment
bound on every even tied ground, using the actual inverse-index constant two. -/
theorem actual_odd_newborn_tied_negative_cubic_energy_moment_norm_lower
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hgneg : (inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re < 0) :
    (-(inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re) * ‖u‖^2 ≤
    4 * (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) *
      ‖centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)‖^2 := by
  have hK := s.cutoff_lower
  have hf := (actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility
    s htie u hu hgneg).1
  have hm := actual_odd_newborn_tied_silent_moment_depth_lower s htie u hu hf
  have hc := native_index_inverse_cost hL K (show 1 ≤ K by omega)
    (poleNeutralIndexLinearMap hL K u)
  have hd : ‖u‖ ≤ 2 * ‖poleNeutralIndexLinearMap hL K u‖ := by
    change ‖(poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)).symm
      ((poleNeutralIndexEquiv hL K (show 1 ≤ K by omega)) u)‖ ≤ _ at hc
    simpa only [LinearEquiv.symm_apply_apply] using hc
  have hs : ‖u‖^2 ≤ 4 * ‖poleNeutralIndexLinearMap hL K u‖^2 := by
    nlinarith [norm_nonneg u, norm_nonneg (poleNeutralIndexLinearMap hL K u)]
  have he := mul_le_mul_of_nonneg_left hs (le_of_lt (neg_pos.mpr hgneg))
  nlinarith only [he, hm]

/-- Negative literal cubic energy forces the whole actual even ground to
inject into the simple odd newborn ground. This removes the old even-simple
premise without asserting that the even side is its own newborn. -/
theorem actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (hgneg : (inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re < 0) :
    Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) = 1 := by
  have hK := s.cutoff_lower
  let lam := poleNeutralEvenRayleighBottom L K hL s.cutoff_lower
  let E := Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (lam : ℂ)
  let O := Module.End.eigenspace (poleNeutralOddCompressedCanonical L K) (lam : ℂ)
  have hmap (u : E) : poleNeutralIndexLinearMap hL K u.val ∈ O := by
    have hu := Module.End.mem_eigenspace_iff.mp u.property
    have hf := (actual_odd_newborn_tied_negative_cubic_energy_forces_kernel_visibility
      s htie u.val hu hgneg).1
    have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K (by omega) u.val
    change poleNeutralOddCompressedCanonical L K (poleNeutralIndexLinearMap hL K u.val) -
      poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u.val) = _ at hd
    rw [hu, map_smul, hf, zero_smul] at hd
    exact Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hd)
  let J : E →ₗ[ℂ] O :=
    { toFun := fun u => ⟨poleNeutralIndexLinearMap hL K u.val, hmap u⟩
      map_add' := by intro u v; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c u; apply Subtype.ext; exact map_smul _ _ _ }
  have hJ : Function.Injective J := by
    intro u v huv
    apply Subtype.ext
    apply poleNeutralIndexLinearMap_injective hL K
    exact congrArg Subtype.val huv
  have hdim := LinearMap.finrank_le_finrank_of_injective hJ
  have hn := newborn_bottom_le_normalized_energy .odd hL K s
  have hlam : lam < 0 := by simpa only [lam, htie] using lt_of_le_of_lt hn.1 hn.2
  have ho := nativeNewborn_negative_eigenspace_finrank_le_one .odd s lam hlam
  change Module.finrank ℂ O ≤ 1 at ho
  obtain ⟨u, hu0, hu⟩ := exists_eigenmode_at_poleNeutralEvenRayleighBottom hL K s.cutoff_lower
  have hp : 0 < Module.finrank ℂ E := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := E)).mpr
    refine ⟨⟨u, Module.End.mem_eigenspace_iff.mpr hu⟩, ?_⟩
    intro hz
    exact hu0 (congrArg Subtype.val hz)
  change Module.finrank ℂ E = 1
  omega

end Zeta23.OPICARound4
