import Zeta23.CCM.UniversalSincSourceDensityIdentification
import Zeta23.WeilEF.VerticalLine

/-!
# Complex physical transform of the exact original source density

The compact continuous density has an entire paper transform by the
repository's proved differentiation-under-integral theorem. Its real-axis
identity with the entire product accumulates at zero and the analytic
identity principle supplies the full complex-frequency identity. No
complex visibility or source-Fourier bridge is supplied as an assumption.
-/

noncomputable section

open Filter Set MeasureTheory Complex
open scoped Topology

namespace Zeta23.CCM.UniversalSinc

theorem originalDensityComplex_hasCompactSupport {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (originalDensityComplex s) :=
  (originalDensityCandidate_hasCompactSupport hs).comp_left
    (g := Complex.ofReal) Complex.ofReal_zero

theorem analyticOnNhd_paperFT_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (Zeta23.paperFT (originalDensityComplex s)) univ := by
  intro z _
  exact (Zeta23.WeilEF.differentiable_paperFT
    (continuous_originalDensityComplex hs) (originalDensityComplex_hasCompactSupport hs)).analyticAt z

/-- The exact physical density has the exact original normally convergent
complex product transform at every complex frequency. -/
theorem paperFT_originalDensityComplex {s : ℝ} (hs : 0 < s) :
    Zeta23.paperFT (originalDensityComplex s) = product s := by
  have hseq0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).ofReal
  have hseq : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hseq0, Filter.Eventually.of_forall ?_⟩
    intro n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hn : (1 / ((n : ℝ) + 1) : ℝ) ≠ 0 := by positivity
    exact_mod_cast hn
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      Zeta23.paperFT (originalDensityComplex s) z = product s z := by
    apply hseq.frequently
    exact Filter.Frequently.of_forall fun n => paperFT_originalDensityCandidate_ofReal hs _
  exact (analyticOnNhd_paperFT_originalDensityComplex hs).eq_of_frequently_eq
    (fun z _ => analyticAt_product hs.le z) hfreq

theorem fixed_paperFT_originalDensityComplex :
    Zeta23.paperFT (originalDensityComplex fixedScale) = product fixedScale :=
  paperFT_originalDensityComplex fixedScale_pos

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.paperFT_originalDensityComplex
#print axioms Zeta23.CCM.UniversalSinc.fixed_paperFT_originalDensityComplex
