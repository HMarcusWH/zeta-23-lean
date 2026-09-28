import Zeta23.CCM.DictionaryArchFiniteDensity
import Zeta23.CCM.SourceContractionLocalized
import Zeta23.CCM.CanonicalArchUpperBound
import Zeta23.CCM.CanonicalSmallApertureCoercivity
import Zeta23.CCM.DictionaryArchDiagonal
import Zeta23.GammaFacts.Mu
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators FourierTransform Interval

/-!
# Small-aperture arch-density closure

This file composes two theorem-backed views of the same production
`dictionaryTest`:

* the localized-autocorrelation/source-contraction bound; and
* the positive physical archimedean density representation.

The resulting scalar tail inequality closes the full-space archimedean
small-aperture bound and therefore the small-aperture canonical coercive base.

No RH premise, boundary-flat premise, project axiom, or placeholder proof is
used.
-/

/-- Source contraction bounds the real part of the production dictionary test
by coefficient norm-square at every physical shift. -/
theorem dictionaryTest_re_le_norm_sq
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {L : ℝ} (hL : 0 < L)
    (y : ℝ) :
    Complex.re
        (dictionaryTest K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L y) ≤
      ‖x‖ ^ 2 := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  by_cases hy : |y| ≤ L
  · have hdiv0 : 0 ≤ |y| / L := div_nonneg (abs_nonneg y) hL.le
    have hdiv1 : |y| / L ≤ 1 := (div_le_one hL).2 hy
    have hω0 : 0 ≤ 1 - |y| / L := sub_nonneg.mpr hdiv1
    have hω1 : 1 - |y| / L ≤ 1 := by linarith
    have hs :=
      sourceContractionBound_proved
        K (1 - |y| / L) hω0 hω1 x
    change
      |Complex.re
        (sourceContract K u (1 - |y| / L))| ≤
          2 * ‖x‖ ^ 2 at hs
    have hre :
        Complex.re (sourceContract K u (1 - |y| / L)) ≤
          2 * ‖x‖ ^ 2 :=
      (le_abs_self _).trans hs
    simp only [dictionaryTest, hy, if_pos, dictionaryKernel]
    norm_num [Complex.mul_re]
    nlinarith
  · have hylt : L < |y| := lt_of_not_ge hy
    rw [dictionaryTest_eq_zero_of_lt_abs K u L y hylt]
    simp

/-- The center value of the production dictionary is exactly Euclidean
coefficient norm-square after taking real parts. -/
theorem dictionaryTest_zero_re_eq_norm_sq
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {L : ℝ} (hL : 0 < L) :
    Complex.re
        (dictionaryTest K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L 0) =
      ‖x‖ ^ 2 := by
  rw [dictionaryTest_zero K
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) hL]
  exact coefficientMass_re_eq_norm_sq K x

/-- The physical defect entering the positive archimedean density is
pointwise nonnegative. -/
theorem dictionaryTest_defect_re_nonneg
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {L : ℝ} (hL : 0 < L)
    (y : ℝ) :
    0 ≤ ‖x‖ ^ 2 -
      Complex.re
        (dictionaryTest K
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L y) := by
  linarith [dictionaryTest_re_le_norm_sq K x hL y]

/-- Elementary head bound for the finite-part reference integrand.  It is
deliberately crude; the final scalar margin has ample slack. -/
theorem one_sub_exp_neg_half_mul_archDensity_le_one
    {y : ℝ} (hy : 0 < y) :
    (1 - Real.exp (-y / 2)) * archDensity y ≤ 1 := by
  unfold archDensity
  have hden : 0 < Real.exp y - Real.exp (-y) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  rw [show
    (1 - Real.exp (-y / 2)) *
        (Real.exp (y / 2) / (Real.exp y - Real.exp (-y))) =
      ((1 - Real.exp (-y / 2)) * Real.exp (y / 2)) /
        (Real.exp y - Real.exp (-y)) by ring]
  rw [div_le_iff₀ hden]
  have hcancel :
      Real.exp (-y / 2) * Real.exp (y / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hhalf : Real.exp (y / 2) ≤ Real.exp y :=
    Real.exp_le_exp.mpr (by linarith)
  have hneg : Real.exp (-y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

/-- The part of the finite-part reference integral removed by cutting at a
small aperture is at most the aperture length. -/
theorem integral_one_sub_exp_mul_archDensity_Ioc_le
    {L : ℝ} (hL : 0 < L) :
    (∫ y : ℝ in Ioc 0 L,
      (1 - Real.exp (-y / 2)) * archDensity y) ≤ L := by
  let f : ℝ → ℝ :=
    fun y => (1 - Real.exp (-y / 2)) * archDensity y
  have hf : IntegrableOn f (Ioc 0 L) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi.mono_set
      Ioc_subset_Ioi_self
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 L) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hmono :
      (∫ y : ℝ in Ioc 0 L, f y) ≤
        ∫ _y : ℝ in Ioc 0 L, (1 : ℝ) :=
    setIntegral_mono_on hf hconst measurableSet_Ioc fun y hy =>
      one_sub_exp_neg_half_mul_archDensity_le_one hy.1
  simpa [f, setIntegral_const, Real.volume_real_Ioc_of_le hL.le] using hmono

/-- The unweighted finite-part tail retains essentially the complete exact
reference integral in the tiny-aperture regime. -/
theorem integral_one_sub_exp_mul_archDensity_tail_lower
    {L : ℝ} (hL : 0 < L) :
    Real.pi / 4 + Real.log 2 / 2 - L ≤
      ∫ y : ℝ in Ioi L,
        (1 - Real.exp (-y / 2)) * archDensity y := by
  let f : ℝ → ℝ :=
    fun y => (1 - Real.exp (-y / 2)) * archDensity y
  have hfull : IntegrableOn f (Ioi 0) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi
  have hhead : IntegrableOn f (Ioc 0 L) :=
    hfull.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn f (Ioi L) :=
    hfull.mono_set (by
      intro y hy
      exact hL.trans hy)
  have hsplit :
      (∫ y : ℝ in Ioi 0, f y) =
        (∫ y : ℝ in Ioc 0 L, f y) +
          ∫ y : ℝ in Ioi L, f y := by
    rw [← Ioc_union_Ioi_eq_Ioi hL.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail
  have hheadLe :=
    integral_one_sub_exp_mul_archDensity_Ioc_le hL
  rw [integral_one_sub_exp_mul_archDensity_Ioi] at hsplit
  dsimp [f] at hsplit
  nlinarith

/-- The exponentially weighted tail is still logarithmically large at
`L <= 1/512`.  The proof uses only the repository's existing exact tail
integral and coarse certified transcendental bounds. -/
theorem integral_exp_neg_half_mul_archDensity_tail_lower
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512) :
    5 * Real.log 2 ≤
      ∫ y : ℝ in Ioi L,
        Real.exp (-y / 2) * archDensity y := by
  have hL2 : L < 2 := by linarith
  have hexp :=
    Real.exp_lt_two_add_div_two_sub hL hL2
  have htwoSub : 0 < 2 - L := by linarith
  have hcross :
      Real.exp L * (2 - L) < 2 + L :=
    (lt_div_iff₀ htwoSub).mp hexp
  have hexpm1 : 0 < Real.exp L - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr hL)
  have hratio :
      2 / L <
        (Real.exp L + 1) / (Real.exp L - 1) := by
    rw [div_lt_div_iff₀ hL hexpm1]
    nlinarith
  have h1024 : (1024 : ℝ) ≤ 2 / L := by
    rw [le_div_iff₀ hL]
    nlinarith
  have hratio1024 :
      (1024 : ℝ) <
        (Real.exp L + 1) / (Real.exp L - 1) :=
    lt_of_le_of_lt h1024 hratio
  have hlog :
      Real.log (1024 : ℝ) <
        Real.log ((Real.exp L + 1) / (Real.exp L - 1)) :=
    Real.log_lt_log (by norm_num) hratio1024
  have hlog1024 :
      Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [hlog1024] at hlog
  rw [integral_exp_neg_half_mul_archDensity_Ioi hL]
  nlinarith

/-- Split the positive archimedean density tail into the two integrable
finite-part pieces already evaluated in `DictionaryArchDiagonal`. -/
theorem integral_archDensity_Ioi_eq_reference_add_exp
    {L : ℝ} (hL : 0 < L) :
    (∫ y : ℝ in Ioi L, archDensity y) =
      (∫ y : ℝ in Ioi L,
        (1 - Real.exp (-y / 2)) * archDensity y) +
      ∫ y : ℝ in Ioi L,
        Real.exp (-y / 2) * archDensity y := by
  have hreference :
      IntegrableOn
        (fun y : ℝ =>
          (1 - Real.exp (-y / 2)) * archDensity y)
        (Ioi L) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi.mono_set
      (by
        intro y hy
        exact hL.trans hy)
  have hexp :
      IntegrableOn
        (fun y : ℝ => Real.exp (-y / 2) * archDensity y)
        (Ioi L) :=
    integrableOn_exp_neg_half_mul_archDensity_Ioi hL
  rw [← integral_add hreference hexp]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Scalar tail inequality that replaces the former matrix-level A1
archimedean obligation. -/
theorem smallAperture_archDensity_tail_margin
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512) :
    2 - L ≤
      2 * Real.pi * Zeta23.mu 0 +
        2 * (∫ y : ℝ in Ioi L, archDensity y) := by
  have href :=
    integral_one_sub_exp_mul_archDensity_tail_lower hL
  have hexp :=
    integral_exp_neg_half_mul_archDensity_tail_lower hL hsmall
  have hmu := Zeta23.MuFields.neg_one_lt_mu_zero
  have hmuScaled :
      -2 * Real.pi < 2 * Real.pi * Zeta23.mu 0 := by
    have hp : 0 < 2 * Real.pi := by positivity
    have hs := mul_lt_mul_of_pos_left hmu hp
    nlinarith
  have htail :
      (∫ y : ℝ in Ioi L, archDensity y) =
        (∫ y : ℝ in Ioi L,
          (1 - Real.exp (-y / 2)) * archDensity y) +
        ∫ y : ℝ in Ioi L,
          Real.exp (-y / 2) * archDensity y :=
    integral_archDensity_Ioi_eq_reference_add_exp hL
  have hrough :
      -(3 / 2 : ℝ) * Real.pi + 11 * Real.log 2 - 2 * L <
        2 * Real.pi * Zeta23.mu 0 +
          2 * (∫ y : ℝ in Ioi L, archDensity y) := by
    rw [htail]
    nlinarith
  have hnumeric :
      2 - L <
        -(3 / 2 : ℝ) * Real.pi + 11 * Real.log 2 - 2 * L := by
    nlinarith [Real.pi_lt_d2, Real.log_two_gt_d9]
  exact (lt_trans hnumeric hrough).le

/-- The real defect integral in the full-dictionary density representation
dominates the exterior density tail times coefficient norm-square.  Cancellation
at the singular origin is preserved: the complete defect is split only after
its integrability has been established. -/
theorem dictionaryTest_archDensity_defect_integral_lower
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    {L : ℝ} (hL : 0 < L) :
    ‖x‖ ^ 2 * (∫ y : ℝ in Ioi L, archDensity y) ≤
      ∫ y : ℝ in Ioi 0,
        (‖x‖ ^ 2 -
          Complex.re
            (dictionaryTest K
              ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L y)) *
          archDensity y := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  let k := dictionaryTest K u L
  let g : ℝ → ℝ :=
    fun y => (‖x‖ ^ 2 - Complex.re (k y)) * archDensity y
  have hk0 : Complex.re (k 0) = ‖x‖ ^ 2 := by
    simpa [k, u] using dictionaryTest_zero_re_eq_norm_sq K x hL
  have hk0' :
      Complex.re (dictionaryTest K u L 0) = ‖x‖ ^ 2 := by
    simpa [k] using hk0
  have hcomplex :=
    integrableOn_dictionaryTest_sub_mul_archDensity_Ioi K u hL
  have hg : IntegrableOn g (Ioi 0) := by
    have hre := hcomplex.re
    refine hre.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp [g, k]
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [hk0']
  have hgHead : IntegrableOn g (Ioc 0 L) :=
    hg.mono_set Ioc_subset_Ioi_self
  have hgTail : IntegrableOn g (Ioi L) :=
    hg.mono_set (by
      intro y hy
      exact hL.trans hy)
  have hsplit :
      (∫ y : ℝ in Ioi 0, g y) =
        (∫ y : ℝ in Ioc 0 L, g y) +
          ∫ y : ℝ in Ioi L, g y := by
    rw [← Ioc_union_Ioi_eq_Ioi hL.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hgHead hgTail
  have hhead : 0 ≤ ∫ y : ℝ in Ioc 0 L, g y := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hd :
        0 ≤ ‖x‖ ^ 2 - Complex.re (k y) := by
      simpa [k, u] using dictionaryTest_defect_re_nonneg K x hL y
    exact mul_nonneg hd (archDensity_pos_of_pos hy.1).le
  have htailEq :
      (∫ y : ℝ in Ioi L, g y) =
        ‖x‖ ^ 2 * (∫ y : ℝ in Ioi L, archDensity y) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hL.trans hy
    have habs : L < |y| := by
      simpa [abs_of_pos hy0] using hy
    have hkzero :
        dictionaryTest K u L y = 0 :=
      dictionaryTest_eq_zero_of_lt_abs K u L y habs
    simp [g, k, hkzero]
  dsimp [g] at hsplit ⊢
  rw [htailEq] at hsplit
  nlinarith

/-- Full-space lower bound for the dictionary archimedean functional on the
frozen tiny-aperture range. -/
theorem dictionaryArchRHS_dictionaryTest_smallAperture_lower
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (2 - L) * ‖x‖ ^ 2 ≤
      Complex.re
        (dictionaryArchRHS
          (dictionaryTest K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) L)) := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  have hk0 :
      Complex.re (dictionaryTest K u L 0) = ‖x‖ ^ 2 := by
    simpa [u] using dictionaryTest_zero_re_eq_norm_sq K x hL
  have hcomplex :=
    integrableOn_dictionaryTest_sub_mul_archDensity_Ioi K u hL
  have hreIntegral :
      Complex.re
          (∫ y : ℝ in Ioi 0,
            (dictionaryTest K u L 0 - dictionaryTest K u L y) *
              (archDensity y : ℂ)) =
        ∫ y : ℝ in Ioi 0,
          (‖x‖ ^ 2 - Complex.re (dictionaryTest K u L y)) *
            archDensity y := by
    rw [← integral_re hcomplex]
    apply integral_congr_ae
    filter_upwards with y
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [hk0]
  have hformula :=
    dictionaryArchRHS_dictionaryTest_eq_mu_zero_add_archDensity_integral
      K u hL
  have harch :
      Complex.re (dictionaryArchRHS (dictionaryTest K u L)) =
        (2 * Real.pi * Zeta23.mu 0) * ‖x‖ ^ 2 +
          2 * (∫ y : ℝ in Ioi 0,
            (‖x‖ ^ 2 - Complex.re (dictionaryTest K u L y)) *
              archDensity y) := by
    rw [hformula]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
    norm_num
    rw [hk0, hreIntegral]
    ring
  have hdefect :=
    dictionaryTest_archDensity_defect_integral_lower K x hL
  have hscalar :=
    smallAperture_archDensity_tail_margin hL hsmall
  have hscale :=
    mul_le_mul_of_nonneg_right hscalar (sq_nonneg ‖x‖)
  change
    (2 - L) * ‖x‖ ^ 2 ≤
      Complex.re (dictionaryArchRHS (dictionaryTest K u L))
  rw [harch]
  nlinarith

/-- The former OPEN dictionary lower-bound interface is now discharged, and in
fact the proof is full-space rather than merely boundary-flat. -/
theorem canonicalBoundaryFlatDictionaryArchLowerBound_proved :
    CanonicalBoundaryFlatDictionaryArchLowerBound := by
  intro L hL hsmall K x _hflat
  exact dictionaryArchRHS_dictionaryTest_smallAperture_lower
    hL hsmall K x

/-- Full-space canonical archimedean upper bound on the frozen tiny-aperture
range. -/
theorem canonicalArchSmallApertureUpperBound_proved :
    CanonicalArchSmallApertureUpperBound := by
  intro L hL hsmall K x
  have hd :=
    dictionaryArchRHS_dictionaryTest_smallAperture_lower
      hL hsmall K x
  rw [matrixRealEnergy_canonicalArchMatrix_eq_neg_re_dictionaryArchRHS
    hL K x]
  linarith

/-- Critical-path boundary-flat archimedean bound, inherited from the stronger
full-space theorem. -/
theorem canonicalBoundaryFlatArchSmallApertureUpperBound_proved :
    CanonicalBoundaryFlatArchSmallApertureUpperBound :=
  canonicalBoundaryFlatArchSmallApertureUpperBound_of_full
    canonicalArchSmallApertureUpperBound_proved

/-- The complete full-space small-aperture canonical coercive base is now
unconditional. -/
theorem canonicalSmallApertureCoercivity_proved :
    CanonicalSmallApertureCoercivity :=
  canonicalSmallApertureCoercivity_of_source_arch
    ⟨sourceContractionBound_proved,
      canonicalArchSmallApertureUpperBound_proved⟩

/-- The exact legal boundary-flat base required by Track A follows immediately
from the stronger full-space result. -/
theorem canonicalBoundaryFlatSmallApertureCoercivity_proved :
    CanonicalBoundaryFlatSmallApertureCoercivity :=
  canonicalBoundaryFlatSmallApertureCoercivity_of_full
    canonicalSmallApertureCoercivity_proved

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTest_re_le_norm_sq
#print axioms Zeta23.CCM.smallAperture_archDensity_tail_margin
#print axioms Zeta23.CCM.dictionaryArchRHS_dictionaryTest_smallAperture_lower
#print axioms Zeta23.CCM.canonicalArchSmallApertureUpperBound_proved
#print axioms Zeta23.CCM.canonicalSmallApertureCoercivity_proved
#print axioms Zeta23.CCM.canonicalBoundaryFlatSmallApertureCoercivity_proved
