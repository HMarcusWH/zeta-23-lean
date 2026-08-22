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

/-- Finite-history transition identity: the joint law of the history through `n` and the
next state is obtained by composing the history marginal with the stationary history kernel. -/
def HasTransitionPair
    (mu : Measure (ℕ → (S × X)))
    (K : Kernel (S × X) (S × X)) : Prop :=
  ∀ n : ℕ,
    (mu.map (Preorder.frestrictLe n)) ⊗ₘ stationaryHistoryKernel K n =
      mu.map (fun w : ℕ → (S × X) => (Preorder.frestrictLe n w, w (n + 1)))

/-- The Ionescu--Tulcea path law satisfies the finite-history transition identity. -/
theorem pathLaw_has_transition_pair
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] :
    HasTransitionPair (pathLaw mu0 K) K := by
  intro n
  simpa [pathLaw] using
    (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => S × X)
      (κ := fun k => stationaryHistoryKernel K k) (μ₀ := mu0) (a := n))

/-- The zeroth finite-history marginal of the canonical path law is exactly the initial law,
written in the singleton-product representation used by Ionescu--Tulcea. -/
theorem pathLaw_prefix_zero
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] :
    (pathLaw mu0 K).map (Preorder.frestrictLe 0) =
      mu0.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => S × X)).symm := by
  unfold pathLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_frestrictLe 0)]
  rw [Kernel.traj_map_frestrictLe]
  simp

/-- Under the canonical path law, the regular conditional distribution of the next
joint state given the whole finite history is the stationary one-step kernel evaluated
at the most recent state. This is the Markov transition statement in Theorem 3.1. -/
theorem pathLaw_has_transition
    [StandardBorelSpace S] [StandardBorelSpace X] [Nonempty S] [Nonempty X]
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] (n : ℕ) :
    condDistrib (fun w : ℕ → (S × X) => w (n + 1)) (Preorder.frestrictLe n) (pathLaw mu0 K)
      =ᵐ[(pathLaw mu0 K).map (Preorder.frestrictLe n)] stationaryHistoryKernel K n := by
  simpa [pathLaw] using
    (Kernel.condDistrib_trajMeasure
      (X := fun _ : ℕ => S × X)
      (κ := fun k => stationaryHistoryKernel K k) (μ₀ := mu0) (a := n))

end Permansson
