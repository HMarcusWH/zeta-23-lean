import Zeta23.ExceptionalZero.FilteredLaplaceSubexp
import Zeta23.ExceptionalZero.FilteredResolventMeromorphic
import Zeta23.ExceptionalZero.MeromorphicIdentity
import Mathlib.Analysis.Complex.Convex

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Metric Set Filter Topology

/-- The open right half-plane, the analytic-continuation domain of the exceptional-zero
detector. -/
def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- **Generic exposed-pole theorem.**  Fix an absolutely summable spectral zero filter and the
critical-line center.  If some zeta zero lies strictly to the right of the critical line and its
multiplicity-weighted filter coefficient does not vanish, then the filtered zero family cannot be
subexponential in the aperture.

The proof is the Laplace-pole contradiction: subexponential growth makes the Laplace transform
holomorphic on all of `Re z > 0`; the safe half-plane `Re z > 1` identity plus meromorphic
identity propagation force the transform to agree with the filtered resolvent near the target
pole `2(ρ₀ - c)`, whose principal part has the nonzero limit `zeroFilterCoeff φ ρ₀`; but a
holomorphic function annihilates `(z - z₁)·(·)` in the punctured limit.  No pointwise
exponential lower bound is asserted. -/
theorem not_subexponential_filteredZeroFamily_of_right_zero
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (ρ₀ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ₀ : ℂ).re)
    (hcoeff : zeroFilterCoeff φ ρ₀ ≠ 0) :
    ¬ Subexponential (fun a => ‖filteredZeroFamily φ c a‖) := by
  intro hsub
  -- the target pole lies in the open right half-plane
  have hz₁re : 0 < (filteredPolePoint c ρ₀).re := by
    have hre : (filteredPolePoint c ρ₀).re = 2 * ((ρ₀ : ℂ).re - c.re) := by
      simp [filteredPolePoint, Complex.mul_re]
    rw [hre, hc]
    linarith
  -- the Laplace transform is holomorphic, hence meromorphic, on the right half-plane
  have hL : DifferentiableOn ℂ (filteredLaplaceTransform φ c) rightHalfPlane :=
    fun z hz =>
      (differentiableAt_filteredLaplaceTransform hφ hc hsub hz).differentiableWithinAt
  have hLmero : MeromorphicOn (filteredLaplaceTransform φ c) rightHalfPlane :=
    (hL.analyticOnNhd isOpen_rightHalfPlane).meromorphicOn
  have hRmero : MeromorphicOn (filteredResolvent φ c) rightHalfPlane :=
    meromorphicOn_filteredResolvent hφ c rightHalfPlane
  -- seed equality on a genuine neighborhood of z = 2 inside the safe half-plane
  have h2re : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hseed : filteredLaplaceTransform φ c =ᶠ[𝓝 (2 : ℂ)] filteredResolvent φ c := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h2re] with z hz
    exact filteredLaplaceTransform_eq_resolvent_safe hφ hc hz
  have h2mem : (2 : ℂ) ∈ rightHalfPlane := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hz₁mem : filteredPolePoint c ρ₀ ∈ rightHalfPlane := hz₁re
  -- propagate equality to a punctured neighborhood of the target pole
  have hprop := meromorphic_eventuallyEq_nhdsNE_of_isPreconnected
    hLmero hRmero isPreconnected_rightHalfPlane h2mem hseed
    (filteredPolePoint c ρ₀) hz₁mem
  -- the resolvent's exact principal part at the target
  obtain ⟨r, hr, hiso⟩ := exists_zero_isolation_radius ρ₀
  have hRlim := filteredResolvent_principalPart_limit (φ := φ) hφ (c := c)
    (ρ₀ := ρ₀) hr hiso
  -- holomorphy kills the same product for the Laplace transform
  have hLcont : ContinuousAt (filteredLaplaceTransform φ c) (filteredPolePoint c ρ₀) :=
    (differentiableAt_filteredLaplaceTransform hφ hc hsub hz₁re).continuousAt
  have hLlim : Tendsto
      (fun z : ℂ => (z - filteredPolePoint c ρ₀) * filteredLaplaceTransform φ c z)
      (𝓝[≠] filteredPolePoint c ρ₀) (𝓝 0) := by
    have hsub_cont : ContinuousAt (fun z : ℂ => z - filteredPolePoint c ρ₀)
        (filteredPolePoint c ρ₀) :=
      continuousAt_id.sub
        (continuousAt_const : ContinuousAt (fun _ : ℂ => filteredPolePoint c ρ₀)
          (filteredPolePoint c ρ₀))
    have hsub_tend : Tendsto (fun z : ℂ => z - filteredPolePoint c ρ₀)
        (𝓝 (filteredPolePoint c ρ₀)) (𝓝 0) := by
      simpa using hsub_cont.tendsto
    have hmul := hsub_tend.mul hLcont.tendsto
    simpa using hmul.mono_left nhdsWithin_le_nhds
  -- transfer through the propagated equality
  have hEq : (fun z : ℂ =>
        (z - filteredPolePoint c ρ₀) * filteredLaplaceTransform φ c z)
      =ᶠ[𝓝[≠] filteredPolePoint c ρ₀]
      (fun z : ℂ => (z - filteredPolePoint c ρ₀) * filteredResolvent φ c z) := by
    filter_upwards [hprop] with z hz
    rw [hz]
  have hRlim0 : Tendsto
      (fun z : ℂ => (z - filteredPolePoint c ρ₀) * filteredResolvent φ c z)
      (𝓝[≠] filteredPolePoint c ρ₀) (𝓝 0) := (tendsto_congr' hEq).mp hLlim
  have hzero : zeroFilterCoeff φ ρ₀ = 0 := tendsto_nhds_unique hRlim hRlim0
  exact hcoeff hzero

end Zeta23.ExceptionalZero
