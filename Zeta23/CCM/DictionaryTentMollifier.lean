import Zeta23.CCM.DictionaryTent
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution Topology

/-!
# Canonical mollifier family for the dictionary tent

This is the Route-M adapter around the already-canonical nonsmooth tent.  The
target remains `dictionaryTent` / `dictionaryApertureCoord`; no clipped or
renormalized substitute is introduced.

The mollifier is a normalized `ContDiffBump` with outer radius
`1 / (n + 1)`.  Its convolution with the real tent is then complexified for
use by the existing `paperFT` interface.

This module is deliberately local to CCM and does not weaken or modify the
central `WeilEF` `ContDiff ℝ 2` interface.
-/

/-- Shrinking positive outer radius used by the canonical Route-M mollifier. -/
def dictionaryTentMollifierRadius (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

@[simp] theorem dictionaryTentMollifierRadius_pos (n : ℕ) :
    0 < dictionaryTentMollifierRadius n := by
  simp [dictionaryTentMollifierRadius]
  positivity

/-- Canonical normalized bump before dividing by its integral.  The inner
radius is half the outer radius, matching the already compiler-tested
`ContDiffBump` pattern used by the exceptional-zero detector family. -/
def dictionaryTentMollifierBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨dictionaryTentMollifierRadius n / 2,
    dictionaryTentMollifierRadius n,
    by
      have hr := dictionaryTentMollifierRadius_pos n
      linarith,
    by
      have hr := dictionaryTentMollifierRadius_pos n
      linarith⟩

@[simp] theorem dictionaryTentMollifierBump_rOut (n : ℕ) :
    (dictionaryTentMollifierBump n).rOut = dictionaryTentMollifierRadius n := rfl

/-- The canonical mollifier radii tend to zero. -/
theorem dictionaryTentMollifierRadius_tendsto_zero :
    Tendsto dictionaryTentMollifierRadius atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Equivalent `rOut` form consumed by Mathlib's approximate-identity theorem. -/
theorem dictionaryTentMollifierBump_rOut_tendsto_zero :
    Tendsto (fun n : ℕ => (dictionaryTentMollifierBump n).rOut) atTop (𝓝 0) := by
  simpa [dictionaryTentMollifierBump] using dictionaryTentMollifierRadius_tendsto_zero

/-- Real normalized mollifier. -/
def dictionaryTentMollifier (n : ℕ) : ℝ → ℝ :=
  (dictionaryTentMollifierBump n).normed volume

/-- Real mollified tent.  Convolution is taken before complexification so the
pinned Mathlib normalized-bump approximate-identity theorem applies directly. -/
def dictionaryTentMollifiedReal (L : ℝ) (n : ℕ) : ℝ → ℝ :=
  dictionaryTentMollifier n ⋆[lsmul ℝ ℝ, volume] dictionaryApertureCoord L

/-- Complex wrapper in the codomain used by `paperFT`. -/
def dictionaryTentMollified (L : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun y => (dictionaryTentMollifiedReal L n y : ℂ)

/-- The real canonical tent has compact support for positive aperture. -/
theorem dictionaryApertureCoord_hasCompactSupport
    {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (dictionaryApertureCoord L) := by
  refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
  intro y hy
  by_contra hzero
  have htent : dictionaryTent L y ≠ 0 := by
    simpa [dictionaryTent] using hzero
  exact hy (dictionaryTent_support_subset_Icc hL htent)

/-- Every normalized mollifier is smooth. -/
theorem contDiff_dictionaryTentMollifier (n : ℕ) (k : ℕ∞) :
    ContDiff ℝ k (dictionaryTentMollifier n) := by
  simpa [dictionaryTentMollifier] using
    (dictionaryTentMollifierBump n).contDiff_normed (μ := volume) (n := k)

/-- Every normalized mollifier has compact support. -/
theorem dictionaryTentMollifier_hasCompactSupport (n : ℕ) :
    HasCompactSupport (dictionaryTentMollifier n) := by
  simpa [dictionaryTentMollifier] using
    (dictionaryTentMollifierBump n).hasCompactSupport_normed (μ := volume)

/-- M0: convolution with the smooth compactly supported mollifier upgrades the
real tent to a `C²` function without changing the target object. -/
theorem contDiff_two_dictionaryTentMollifiedReal
    (L : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (dictionaryTentMollifiedReal L n) := by
  have hloc : LocallyIntegrable (dictionaryApertureCoord L) volume :=
    (continuous_dictionaryApertureCoord L).locallyIntegrable
  exact (dictionaryTentMollifier_hasCompactSupport n).contDiff_convolution_left
    (lsmul ℝ ℝ) (contDiff_dictionaryTentMollifier n 2) hloc

/-- M0, complex wrapper form used by the existing explicit-formula interface. -/
theorem contDiff_two_dictionaryTentMollified
    (L : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (dictionaryTentMollified L n) := by
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_two_dictionaryTentMollifiedReal L n)

/-- M0: the real mollified tent remains compactly supported. -/
theorem dictionaryTentMollifiedReal_hasCompactSupport
    {L : ℝ} (hL : 0 < L) (n : ℕ) :
    HasCompactSupport (dictionaryTentMollifiedReal L n) := by
  exact (dictionaryTentMollifier_hasCompactSupport n).convolution
    (lsmul ℝ ℝ) (dictionaryApertureCoord_hasCompactSupport hL)

/-- M0, complex wrapper compact-support form. -/
theorem dictionaryTentMollified_hasCompactSupport
    {L : ℝ} (hL : 0 < L) (n : ℕ) :
    HasCompactSupport (dictionaryTentMollified L n) := by
  exact (dictionaryTentMollifiedReal_hasCompactSupport hL n).comp_left
    (g := Complex.ofReal) Complex.ofReal_zero

/-- M1: at every physical-space point, the real mollified tent converges to the
literal canonical aperture coordinate. -/
theorem dictionaryTentMollifiedReal_tendsto
    (L y : ℝ) :
    Tendsto (fun n : ℕ => dictionaryTentMollifiedReal L n y) atTop
      (𝓝 (dictionaryApertureCoord L y)) := by
  simpa [dictionaryTentMollifiedReal, dictionaryTentMollifier] using
    (ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume)
      (φ := dictionaryTentMollifierBump)
      (g := dictionaryApertureCoord L)
      dictionaryTentMollifierBump_rOut_tendsto_zero
      (continuous_dictionaryApertureCoord L)
      y)

end Zeta23.CCM

#print axioms Zeta23.CCM.contDiff_two_dictionaryTentMollified
#print axioms Zeta23.CCM.dictionaryTentMollified_hasCompactSupport
#print axioms Zeta23.CCM.dictionaryTentMollifiedReal_tendsto
