import Zeta23.CCM.UniversalSincSourceComplexTransform
import Zeta23.CCM.UniversalSincSourceSymmetry

/-!
# Public names and exact support of the original source

This facade exposes the manifest's real source names. Its complex kernels
are the literal differential expressions `k = Pq`, `j = P²q`, and the
native real source is the real part of the latter. Every support and mass
statement concerns these constructed functions. No zeta-zero, phase-depth,
or global native-field membership premise occurs here.
-/

noncomputable section

open Set MeasureTheory Complex
open scoped Topology

namespace Zeta23.CCM

/-- The literal original infinite-convolution density at scale `s`. -/
def universalSincSource (s : ℝ) : ℝ → ℝ :=
  UniversalSinc.originalDensityCandidate s

theorem universalSincSource_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 ≤ universalSincSource s x := UniversalSinc.originalDensityCandidate_nonneg hs x

theorem universalSincSource_integral_one {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, universalSincSource s x) = 1 :=
  UniversalSinc.integral_originalDensityCandidate hs

theorem universalSincSource_support {s : ℝ} (hs : 0 < s) :
    tsupport (universalSincSource s) ⊆ Icc (-s) s := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  apply hx
  exact UniversalSinc.originalDensityCandidate_zero_of_abs_gt hs
    (lt_of_not_ge (fun h => hnot (abs_le.mp h)))

theorem universalSincSource_contDiff {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (universalSincSource s) :=
  UniversalSinc.contDiff_originalDensityCandidate hs

theorem universalSincSource_even {s : ℝ} (hs : 0 < s) :
    Function.Even (universalSincSource s) := UniversalSinc.originalDensityCandidate_even hs

theorem paperFT_universalSincSource {s : ℝ} (hs : 0 < s) :
    Zeta23.paperFT (fun x : ℝ => (universalSincSource s x : ℂ)) =
      UniversalSinc.product s := UniversalSinc.paperFT_originalDensityComplex hs

/-- The native differential expression `P = ∂² - 1/4`. -/
def universalSincDifferential (q : ℝ → ℂ) : ℝ → ℂ :=
  fun x => deriv (deriv q) x - (1 / 4 : ℂ) * q x

/-- The literal original complex kernel `k_s = P q_s`. -/
def universalSincKernel (s : ℝ) : ℝ → ℂ :=
  universalSincDifferential (UniversalSinc.originalDensityComplex s)

/-- The literal original complex kernel `j_s = P² q_s`. -/
def universalSincSecondKernel (s : ℝ) : ℝ → ℂ :=
  universalSincDifferential (universalSincKernel s)

/-- The real native arithmetic source extracted from the literal `P²q`. -/
def universalSincSecondSource (s x : ℝ) : ℝ := (universalSincSecondKernel s x).re

private theorem contDiff_originalComplex {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (UniversalSinc.originalDensityComplex s) := by
  rw [← UniversalSinc.inverseCandidate_eq_originalDensityComplex hs]
  exact UniversalSinc.contDiff_inverseCandidate hs

private theorem contDiff_differential {q : ℝ → ℂ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ContDiff ℝ (⊤ : ℕ∞) (universalSincDifferential q) := by
  have hd := (contDiff_infty_iff_deriv.mp hq).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact hdd.sub (contDiff_const.mul hq)

theorem universalSincKernel_contDiff {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (universalSincKernel s) :=
  contDiff_differential (contDiff_originalComplex hs)

theorem universalSincSecondKernel_contDiff {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (universalSincSecondKernel s) :=
  contDiff_differential (universalSincKernel_contDiff hs)

theorem universalSincSecondSource_contDiff {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (universalSincSecondSource s) := by
  exact Complex.reCLM.contDiff.comp (universalSincSecondKernel_contDiff hs)

private theorem differential_zero_outside {s : ℝ} {q : ℝ → ℂ}
    (hq : tsupport q ⊆ Icc (-s) s) {x : ℝ} (hx : x ∉ Icc (-s) s) :
    universalSincDifferential q x = 0 := by
  have hxq : x ∉ tsupport q := fun h => hx (hq h)
  have hxd : x ∉ tsupport (deriv q) := fun h => hxq (tsupport_deriv_subset h)
  rw [universalSincDifferential, deriv_of_notMem_tsupport hxd,
    image_eq_zero_of_notMem_tsupport hxq, mul_zero, sub_zero]

private theorem differential_support {s : ℝ} {q : ℝ → ℂ}
    (hq : tsupport q ⊆ Icc (-s) s) :
    tsupport (universalSincDifferential q) ⊆ Icc (-s) s := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (differential_zero_outside hq hnot)

private theorem originalComplex_support {s : ℝ} (hs : 0 < s) :
    tsupport (UniversalSinc.originalDensityComplex s) ⊆ Icc (-s) s := by
  apply Zeta23.tsupport_subset_of_support_subset_abs
  intro x hx
  by_contra hnot
  apply hx
  have hzero := UniversalSinc.originalDensityCandidate_zero_of_abs_gt hs (lt_of_not_ge hnot)
  simp only [UniversalSinc.originalDensityComplex, hzero, Complex.ofReal_zero]

theorem universalSincKernel_support {s : ℝ} (hs : 0 < s) :
    tsupport (universalSincKernel s) ⊆ Icc (-s) s :=
  differential_support (originalComplex_support hs)

theorem universalSincSecondKernel_support {s : ℝ} (hs : 0 < s) :
    tsupport (universalSincSecondKernel s) ⊆ Icc (-s) s :=
  differential_support (universalSincKernel_support hs)

theorem universalSincKernel_zero_outside {s : ℝ} (hs : 0 < s) {x : ℝ}
    (hx : x ∉ Icc (-s) s) : universalSincKernel s x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (universalSincKernel_support hs h))

theorem universalSincSecondKernel_zero_outside {s : ℝ} (hs : 0 < s) {x : ℝ}
    (hx : x ∉ Icc (-s) s) : universalSincSecondKernel s x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (universalSincSecondKernel_support hs h))

theorem universalSincSecondSource_zero_outside {s : ℝ} (hs : 0 < s) {x : ℝ}
    (hx : x ∉ Icc (-s) s) : universalSincSecondSource s x = 0 := by
  rw [universalSincSecondSource, universalSincSecondKernel_zero_outside hs hx, Complex.zero_re]

theorem universalSincSecondSource_support {s : ℝ} (hs : 0 < s) :
    tsupport (universalSincSecondSource s) ⊆ Icc (-s) s := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (universalSincSecondSource_zero_outside hs hnot)

private theorem differential_hasCompactSupport {q : ℝ → ℂ} (hq : HasCompactSupport q) :
    HasCompactSupport (universalSincDifferential q) :=
  hq.deriv.deriv.sub hq.mul_left

theorem universalSincKernel_hasCompactSupport {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (universalSincKernel s) :=
  differential_hasCompactSupport (UniversalSinc.originalDensityComplex_hasCompactSupport hs)

theorem universalSincSecondKernel_hasCompactSupport {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (universalSincSecondKernel s) :=
  differential_hasCompactSupport (universalSincKernel_hasCompactSupport hs)

private theorem paperFT_differential {q : ℝ → ℂ}
    (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q) (z : ℂ) :
    Zeta23.paperFT (universalSincDifferential q) z =
      -(z ^ 2 + 1 / 4) * Zeta23.paperFT q z := by
  have hd2 : Continuous (deriv (deriv q)) := hq.deriv'.continuous_deriv le_rfl
  have hmul : Continuous (fun x : ℝ => (1 / 4 : ℂ) * q x) := continuous_const.mul hq.continuous
  rw [show universalSincDifferential q =
      deriv (deriv q) - (fun x : ℝ => (1 / 4 : ℂ) * q x) by rfl,
    Zeta23.paperFT_sub hd2 hmul hqc.deriv.deriv hqc.mul_left,
    Zeta23.paperFT_deriv_deriv hq hqc]
  have hconst : Zeta23.paperFT (fun x : ℝ => (1 / 4 : ℂ) * q x) z =
      (1 / 4 : ℂ) * Zeta23.paperFT q z := by
    rw [Zeta23.paperFT_def, Zeta23.paperFT_def, ← Zeta23.integral_const_mul_C]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hconst]
  ring

theorem paperFT_universalSincKernel {s : ℝ} (hs : 0 < s) (z : ℂ) :
    Zeta23.paperFT (universalSincKernel s) z =
      -(z ^ 2 + 1 / 4) * UniversalSinc.product s z := by
  rw [universalSincKernel,
    paperFT_differential ((contDiff_originalComplex hs).of_le (by norm_num))
      (UniversalSinc.originalDensityComplex_hasCompactSupport hs),
    UniversalSinc.paperFT_originalDensityComplex hs]

theorem paperFT_universalSincSecondKernel {s : ℝ} (hs : 0 < s) (z : ℂ) :
    Zeta23.paperFT (universalSincSecondKernel s) z =
      (z ^ 2 + 1 / 4) ^ 2 * UniversalSinc.product s z := by
  rw [universalSincSecondKernel,
    paperFT_differential ((universalSincKernel_contDiff hs).of_le (by norm_num))
      (universalSincKernel_hasCompactSupport hs), paperFT_universalSincKernel hs]
  ring

/-- Mass of the actual twice pole-killed complex kernel, computed at
frequency zero. No off-line-zero hypothesis is needed. -/
theorem universalSincSecondKernel_integral {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, universalSincSecondKernel s x) = (1 / 16 : ℂ) := by
  have h := paperFT_universalSincSecondKernel hs 0
  rw [Zeta23.paperFT_def] at h
  norm_num [UniversalSinc.product_zero] at h
  exact h

theorem universalSincSecondKernel_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (universalSincSecondKernel s) :=
  (universalSincSecondKernel_contDiff hs).continuous.integrable_of_hasCompactSupport
    (universalSincSecondKernel_hasCompactSupport hs)

private theorem integral_re_complex {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, (f x).re) = (∫ x : ℝ, f x).re := integral_re hf

theorem universalSincSecondSource_integral {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, universalSincSecondSource s x) = (1 / 16 : ℝ) := by
  rw [universalSincSecondSource,
    integral_re_complex (universalSincSecondKernel_integrable hs),
    universalSincSecondKernel_integral hs]
  norm_num

end Zeta23.CCM

#print axioms Zeta23.CCM.universalSincSource_integral_one
#print axioms Zeta23.CCM.paperFT_universalSincSource
#print axioms Zeta23.CCM.universalSincKernel_support
#print axioms Zeta23.CCM.universalSincSecondKernel_support
#print axioms Zeta23.CCM.universalSincSecondSource_integral
