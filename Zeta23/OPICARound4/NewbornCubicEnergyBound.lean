import Zeta23.OPICARound4.TiedCubicEnergy
import Zeta23.OPICARound4.NewbornSpectralVisibility
import Mathlib.Analysis.InnerProductSpace.Spectrum

noncomputable section
namespace Zeta23.OPICARound4
open CCM OPICARound3
open scoped BigOperators ComplexConjugate

private theorem newborn_spectral_energy_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (alpha beta : ℝ) (hb : beta < 0) (hab : alpha ≤ beta)
    (hneg : ∀ (lam : ℝ) (v : E), lam < 0 → v ≠ 0 →
      T v = (lam : ℂ) • v → lam = beta)
    (y g : E) (hy : T y - (alpha : ℂ) • y = g) :
    beta * (beta - alpha) * (inner ℂ g y).re ≤ (inner ℂ (T g) g).re := by
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℂ E = Module.finrank ℂ E)
  let ell := hT.eigenvalues (rfl : Module.finrank ℂ E = Module.finrank ℂ E)
  have he (i) : T (b i) = (ell i : ℂ) • b i := hT.apply_eigenvectorBasis rfl i
  have hg (i) : inner ℂ (b i) g = ((ell i - alpha : ℝ) : ℂ) * inner ℂ (b i) y := by
    rw [← hy, inner_sub_right, inner_smul_right, ← hT (b i) y, he,
      inner_smul_left, Complex.conj_ofReal]
    push_cast
    ring
  rw [← b.sum_inner_mul_inner g y, ← b.sum_inner_mul_inner (T g) g]
  simp only [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hs : ell i = beta ∨ 0 ≤ ell i := by
    by_cases hh : ell i < 0
    · exact Or.inl (hneg _ _ hh (hT.hasEigenvector_eigenvectorBasis rfl i).2 (he i))
    · exact Or.inr (le_of_not_gt hh)
  have hp : 0 ≤ (ell i - alpha) * (ell i - beta) * (ell i + beta - alpha) := by
    rcases hs with hh | hh
    · rw [hh]; simp
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hpz := mul_nonneg hp (Complex.normSq_nonneg (inner ℂ (b i) y))
  rw [hT g (b i), he, inner_smul_right]
  rw [← inner_conj_symm g (b i), hg]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, sub_zero, Complex.mul_im, add_zero,
    Complex.normSq_apply] at hpz ⊢
  nlinarith only [hpz]

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

/-- The literal cubic-source energy at an own odd birth controls the
source-normalized even fourth moment. The complete nonnegative complement
is retained; equality of the two bottoms is allowed. -/
theorem oddNewborn_normalized_even_moment_cubic_energy_bound
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL) (alpha : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (alpha : ℂ) • u)
    (hle : alpha ≤ poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (hf : poleNeutralCorrectedCubicSource L K u = 1) :
    poleNeutralOddRayleighBottom L K hL s.cutoff_lower *
      (poleNeutralOddRayleighBottom L K hL s.cutoff_lower - alpha) *
      (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤
      (inner ℂ (poleNeutralOddCompressedCanonical L K
        (poleNeutralCubicCompressionVector L K))
        (poleNeutralCubicCompressionVector L K)).re := by
  let g := poleNeutralCubicCompressionVector L K
  let y := poleNeutralIndexLinearMap hL K u
  have hy : poleNeutralOddCompressedCanonical L K y - (alpha : ℂ) • y = g := by
    have hd := poleNeutralCompressedIndexDefect_eq_correctedCubicSource hL K
      (Nat.le_trans (by decide : 2 ≤ 3) s.cutoff_lower) u
    change poleNeutralOddCompressedCanonical L K y -
      poleNeutralIndexLinearMap hL K (poleNeutralEvenCompressedCanonical L K u) = _ at hd
    rw [hu, map_smul, hf, one_smul] at hd
    exact hd
  have hn := newborn_bottom_le_normalized_energy .odd hL K s
  have hb := hn.1.trans_lt hn.2
  have hbound := @newborn_spectral_energy_lower (poleNeutralOddSubspace L K)
    inferInstance (poleNeutralOdd_innerProductSpace L K) inferInstance
    (poleNeutralOddCompressedCanonical L K) (poleNeutralOddCompressedCanonical_isSymmetric L K)
    alpha _ hb hle
    (fun lam v hlam hv0 hv => nativeNewborn_negative_eigenvalue_eq_ground .odd s lam hlam v hv0 hv)
    y g hy
  rw [congrArg Complex.re (poleNeutral_cubic_pairing_eq_momentFour hL K u)] at hbound
  exact hbound

/-- The exact adjoint counterpart uses the minus corrected Riesz source
and the adjoint index vector. It does not replace either by the distinct
reciprocal arithmetic input. -/
theorem evenNewborn_normalized_odd_corrected_energy_bound
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .even L K hL) (alpha : ℝ)
    (w : poleNeutralOddSubspace L K)
    (hw : poleNeutralOddCompressedCanonical L K w = (alpha : ℂ) • w)
    (hle : alpha ≤ poleNeutralEvenRayleighBottom L K hL s.cutoff_lower)
    (hc : poleNeutralCubicPairingFunctional L K w = 1) :
    poleNeutralEvenRayleighBottom L K hL s.cutoff_lower *
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower - alpha) *
      (-(poleNeutralCorrectedCubicSource L K
        (poleNeutralIndexAdjointEquiv hL K s.cutoff_lower w)).re) ≤
      (inner ℂ (poleNeutralEvenCompressedCanonical L K
        (poleNeutralCorrectedCubicRieszVector L K))
        (poleNeutralCorrectedCubicRieszVector L K)).re := by
  let h := poleNeutralCorrectedCubicRieszVector L K
  let y := poleNeutralIndexAdjointEquiv hL K s.cutoff_lower w
  have hy : poleNeutralEvenCompressedCanonical L K y - (alpha : ℂ) • y = -h := by
    have hd := native_odd_rank_one_unshifted hL K s.cutoff_lower w
    rw [hw, map_smul, hc, one_smul] at hd
    exact hd
  have hn := newborn_bottom_le_normalized_energy .even hL K s
  have hb := hn.1.trans_lt hn.2
  have hbound := @newborn_spectral_energy_lower (poleNeutralEvenSubspace L K)
    inferInstance (poleNeutralEven_innerProductSpace L K) inferInstance
    (poleNeutralEvenCompressedCanonical L K) (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    alpha _ hb hle
    (fun lam v hlam hv0 hv => nativeNewborn_negative_eigenvalue_eq_ground .even s lam hlam v hv0 hv)
    y (-h) hy
  have hm : (inner ℂ (-h) y).re = -(poleNeutralCorrectedCubicSource L K y).re := by
    change (inner ℂ (-h.val.val) y.val.val).re = _
    rw [inner_neg_left, Complex.neg_re]
    change -(inner ℂ h y).re = _
    rw [inner_poleNeutralCorrectedCubicRieszVector]
  have he : (inner ℂ (poleNeutralEvenCompressedCanonical L K (-h)) (-h)).re =
      (inner ℂ (poleNeutralEvenCompressedCanonical L K h) h).re := by
    rw [map_neg]
    change (inner ℂ (-(poleNeutralEvenCompressedCanonical L K h).val.val)
      (-h.val.val)).re = _
    rw [inner_neg_neg]
    rfl
  rw [hm, he] at hbound
  exact hbound

end Zeta23.OPICARound4
