import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic

noncomputable section

namespace Zeta23.CCM

/-!
# A scalar functional separates an eigenline

The actual mathematical input is that an eigenvector killed by the scalar
functional must be zero. No inner product, isometry, resolvent, positivity,
or finite-dimensional ambient space is needed for this algebraic lemma.
-/

/-- A scalar functional with trivial kernel on an eigenspace determines every
vector in that eigenspace from one nonzero eigenvector. -/
theorem eigenmode_eq_smul_of_functional_kernel
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (T : V →ₗ[𝕜] V) (a : 𝕜) (S : V →ₗ[𝕜] 𝕜)
    (hker : ∀ x : V, T x = a • x → S x = 0 → x = 0)
    {v : V} (hv : T v = a • v) (hvne : v ≠ 0)
    (w : V) (hw : T w = a • w) :
    ∃ c : 𝕜, c • v = w := by
  have hSv : S v ≠ 0 := fun hz => hvne (hker v hv hz)
  let c : 𝕜 := S w / S v
  have heig : T (w - c • v) = a • (w - c • v) := by
    simp only [map_sub, map_smul, hw, hv, smul_sub, smul_smul]
    rw [mul_comm c a]
  have hzero : S (w - c • v) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    dsimp [c]
    rw [div_mul_cancel₀ _ hSv, sub_self]
  exact ⟨c, (sub_eq_zero.mp (hker _ heig hzero)).symm⟩

/-- With a nonzero eigenvector, the preceding kernel condition gives dimension
exactly one, not merely a selected or numerically simple eigenvector. -/
theorem eigenspace_finrank_eq_one_of_functional_kernel
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (T : V →ₗ[𝕜] V) (a : 𝕜) (S : V →ₗ[𝕜] 𝕜)
    (hker : ∀ x : V, T x = a • x → S x = 0 → x = 0)
    (hex : ∃ v : V, v ≠ 0 ∧ T v = a • v) :
    Module.finrank 𝕜 (Module.End.eigenspace T a) = 1 := by
  obtain ⟨v, hvne, hv⟩ := hex
  let v' : Module.End.eigenspace T a := ⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩
  apply finrank_eq_one_iff'.mpr
  refine ⟨v', ?_, ?_⟩
  · intro hz
    exact hvne (congrArg Subtype.val hz)
  · intro w
    obtain ⟨c, hc⟩ := eigenmode_eq_smul_of_functional_kernel
      T a S hker hv hvne (w : V)
      (Module.End.mem_eigenspace_iff.mp w.property)
    exact ⟨c, Subtype.ext hc⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.eigenmode_eq_smul_of_functional_kernel
#print axioms Zeta23.CCM.eigenspace_finrank_eq_one_of_functional_kernel
