import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

namespace Zeta23.OPICA
open Set Metric

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem annihilator_vanishes_on_rangeClosure (A : E →L[𝕜] F) (l : F →L[𝕜] 𝕜)
    (h : ∀ x, l (A x) = 0) {z : F} (hz : z ∈ closure (Set.range A)) : l z = 0 := by
  have hs : Set.range A ⊆ {z | l z = 0} := by rintro _ ⟨x, rfl⟩; exact h x
  exact (closure_minimal hs (isClosed_eq l.continuous continuous_const)) hz

theorem not_mem_rangeClosure_of_annihilator (A : E →L[𝕜] F) (l : F →L[𝕜] 𝕜)
    (h : ∀ x, l (A x) = 0) {Y : F} (hY : l Y ≠ 0) :
    Y ∉ closure (Set.range A) := by
  intro hy
  exact hY (annihilator_vanishes_on_rangeClosure A l h hy)

theorem range_distance_of_annihilator (A : E →L[𝕜] F) (l : F →L[𝕜] 𝕜)
    (h : ∀ x, l (A x) = 0) {Y : F} (hY : l Y ≠ 0) :
    0 < ‖l Y‖ / ‖l‖ ∧
      ‖l Y‖ / ‖l‖ ≤ infDist Y (closure (Set.range A)) := by
  have hl : l ≠ 0 := by intro hl; apply hY; simp [hl]
  have hp : 0 < ‖l‖ := norm_pos_iff.mpr hl
  refine ⟨div_pos (norm_pos_iff.mpr hY) hp, ?_⟩
  have hn : (closure (Set.range A)).Nonempty := ⟨0, subset_closure ⟨0, map_zero A⟩⟩
  apply (le_infDist hn).mpr
  intro z hz
  have hz' := annihilator_vanishes_on_rangeClosure A l h hz
  have hb := l.le_opNorm (Y - z)
  rw [map_sub, hz', sub_zero] at hb
  rw [div_le_iff₀ hp, dist_eq_norm]
  nlinarith

end Zeta23.OPICA
