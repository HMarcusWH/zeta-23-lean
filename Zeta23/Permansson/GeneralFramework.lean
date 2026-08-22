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
  letI : IsMarkovKernel (α ⊗ₖ P) := inferInstance
  letI : IsMarkovKernel ((α ⊗ₖ P) ⊗ₖ U) := inferInstance
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
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] :
    Measure (ℕ → (S × X)) :=
  Kernel.trajMeasure mu0 (fun n => stationaryHistoryKernel K n)

instance pathLaw_isProbability
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] :
    IsProbabilityMeasure (pathLaw mu0 K) := by
  unfold pathLaw
  infer_instance

/-- Under the canonical path law, the regular conditional distribution of the next
joint state given the whole finite history is the stationary one-step kernel evaluated
at the most recent state.  This is the Markov transition statement in Theorem 3.1. -/
theorem pathLaw_has_transition
    [StandardBorelSpace S] [StandardBorelSpace X] [Nonempty S] [Nonempty X]
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] (n : ℕ) :
    condDistrib (fun w : ℕ → (S × X) => w (n + 1)) (Preorder.frestrictLe n) (pathLaw mu0 K)
      =ᵐ[(pathLaw mu0 K).map (Preorder.frestrictLe n)] stationaryHistoryKernel K n := by
  simpa [pathLaw] using
    (Kernel.condDistrib_trajMeasure
      (mu0 := mu0) (κ := fun k => stationaryHistoryKernel K k) (a := n))

end Permansson
