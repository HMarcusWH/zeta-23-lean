import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Permansson v0.1.6: measurable-space core

This file formalizes the measurable-space content of Theorem 3.1
(`Joint-process well-posedness`) from *Permansson Regimes: Strategic Dynamics Beyond Equilibrium*
v0.1.6.

The paper's parenthesized input `S × X × A × X` is represented as
`(S × X) × (A × X)`, which is measurably equivalent and matches mathlib's
composition-product API.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Permansson

universe uS uX uA

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]

/-- The induced joint one-step kernel obtained by the typed order
`action selection α → world transition P → strategic update U`, then dropping the realized action.

Types:
* `α : Kernel (S × X) A`
* `P : Kernel ((S × X) × A) X`
* `U : Kernel ((S × X) × (A × X)) S`
* output: `Kernel (S × X) (S × X)`.
-/
noncomputable def jointKernel
    (α : Kernel (S × X) A)
    (P : Kernel ((S × X) × A) X)
    (U : Kernel ((S × X) × (A × X)) S) :
    Kernel (S × X) (S × X) :=
  (((α ⊗ₖ P) ⊗ₖ U).map (fun z : (A × X) × S => (z.2, z.1.2)))

/-- The induced joint kernel is Markov whenever the three typed component kernels are Markov. -/
theorem jointKernel_isMarkov
    (α : Kernel (S × X) A)
    (P : Kernel ((S × X) × A) X)
    (U : Kernel ((S × X) × (A × X)) S)
    [IsMarkovKernel α] [IsMarkovKernel P] [IsMarkovKernel U] :
    IsMarkovKernel (jointKernel α P U) := by
  unfold jointKernel
  haveI : IsMarkovKernel (α ⊗ₖ P) := inferInstance
  haveI : IsMarkovKernel ((α ⊗ₖ P) ⊗ₖ U) := inferInstance
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The stationary one-step kernel lifted to a kernel on finite histories by reading only
    the most recent coordinate. -/
noncomputable def stationaryHistoryKernel
    (K : Kernel (S × X) (S × X)) (n : ℕ) :
    Kernel ((i : Iic n) → (S × X)) (S × X) :=
  K.comap (fun h => h ⟨n, mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance stationaryHistoryKernel_isMarkov
    (K : Kernel (S × X) (S × X)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (stationaryHistoryKernel K n) := by
  unfold stationaryHistoryKernel
  infer_instance

/-- The canonical path law obtained from Ionescu--Tulcea by iterating the induced stationary kernel. -/
noncomputable def pathLaw
    (λ₀ : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure λ₀] [IsMarkovKernel K] :
    Measure (ℕ → (S × X)) :=
  Kernel.trajMeasure λ₀ (fun n => stationaryHistoryKernel K n)

instance pathLaw_isProbability
    (λ₀ : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure λ₀] [IsMarkovKernel K] :
    IsProbabilityMeasure (pathLaw λ₀ K) := by
  unfold pathLaw
  infer_instance

#check Kernel.trajMeasure
#check Kernel.condDistrib_trajMeasure
#check Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
#check Kernel.traj_map_frestrictLe
#check Kernel.traj_map_frestrictLe_of_le
#check MeasureTheory.isProjectiveLimit_nat_iff
#check ProbabilityTheory.isProjectiveLimit_map
#check ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd

end Permansson
