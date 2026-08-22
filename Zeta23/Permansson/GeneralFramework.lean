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
  rw [Measure.map_comp _ _ (by fun_prop)]
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

/-!
## Theorem 3.1: existence and uniqueness of the joint path law

The transition-law condition is encoded by `HasTransitionPair`, the finite-history
joint-law identity equivalent (on standard Borel state spaces) to saying that the
canonical coordinate process has one-step transition kernel `K`.
-/

/-- Append one new state to a finite path prefix. -/
def appendPrefix (n : ℕ)
    (z : ((i : Iic n) → (S × X)) × (S × X)) :
    (i : Iic (n + 1)) → (S × X) :=
  fun i => if h : i.1 ≤ n then z.1 ⟨i.1, mem_Iic.mpr h⟩ else z.2

theorem measurable_appendPrefix (n : ℕ) :
    Measurable (appendPrefix (S := S) (X := X) n) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.1 ≤ n
  · simpa [appendPrefix, h] using
      (measurable_pi_apply (⟨i.1, mem_Iic.mpr h⟩ : Iic n)).comp measurable_fst
  · simpa [appendPrefix, h] using
      (measurable_snd : Measurable
        (fun z : ((i : Iic n) → (S × X)) × (S × X) => z.2))

/-- Appending the `(n+1)`-st coordinate to the prefix through `n` recovers the
prefix through `n+1`. -/
theorem appendPrefix_pair (n : ℕ) (w : ℕ → (S × X)) :
    appendPrefix (S := S) (X := X) n
        (Preorder.frestrictLe n w, w (n + 1)) =
      Preorder.frestrictLe (n + 1) w := by
  funext i
  by_cases h : i.1 ≤ n
  · simp [appendPrefix, h]
  · have hi : i.1 = n + 1 := by
      have hle : i.1 ≤ n + 1 := mem_Iic.mp i.2
      omega
    simp [appendPrefix, h, hi]

/-- Two laws with the same zeroth prefix and the same transition-pair identities
have the same finite-prefix law at every time. -/
theorem prefix_maps_eq_of_initial_and_transition
    {mu nu : Measure (ℕ → (S × X))}
    (K : Kernel (S × X) (S × X))
    (h0 : mu.map (Preorder.frestrictLe 0) = nu.map (Preorder.frestrictLe 0))
    (hmu : HasTransitionPair mu K)
    (hnu : HasTransitionPair nu K) :
    ∀ n : ℕ, mu.map (Preorder.frestrictLe n) = nu.map (Preorder.frestrictLe n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      have hpair :
          mu.map (fun w : ℕ → (S × X) => (Preorder.frestrictLe n w, w (n + 1))) =
            nu.map (fun w : ℕ → (S × X) => (Preorder.frestrictLe n w, w (n + 1))) := by
        rw [← hmu n, ← hnu n, ih]
      calc
        mu.map (Preorder.frestrictLe (n + 1)) =
            (mu.map (fun w : ℕ → (S × X) =>
              (Preorder.frestrictLe n w, w (n + 1)))).map
                (appendPrefix (S := S) (X := X) n) := by
          rw [Measure.map_map (by fun_prop) (measurable_appendPrefix (S := S) (X := X) n)]
          apply Measure.map_congr
          filter_upwards [] with w
          exact (appendPrefix_pair (S := S) (X := X) n w).symm
        _ = (nu.map (fun w : ℕ → (S × X) =>
              (Preorder.frestrictLe n w, w (n + 1)))).map
                (appendPrefix (S := S) (X := X) n) := by rw [hpair]
        _ = nu.map (Preorder.frestrictLe (n + 1)) := by
          rw [Measure.map_map (by fun_prop) (measurable_appendPrefix (S := S) (X := X) n)]
          apply Measure.map_congr
          filter_upwards [] with w
          exact appendPrefix_pair (S := S) (X := X) n w

/-- Equality of all initial-segment laws determines a probability law on the countable
trajectory space. -/
theorem measure_eq_of_prefix_maps_eq
    (mu nu : Measure (ℕ → (S × X)))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : ∀ n : ℕ,
      mu.map (Preorder.frestrictLe n) = nu.map (Preorder.frestrictLe n)) :
    mu = nu := by
  let fam : (I : Finset ℕ) → Measure ((i : I) → (S × X)) :=
    fun I => mu.map (fun w : ℕ → (S × X) => I.restrict w)
  have hfam : IsProjectiveMeasureFamily fam := by
    dsimp [fam]
    apply ProbabilityTheory.isProjectiveMeasureFamily_map_restrict
    intro t
    fun_prop
  have hmu : IsProjectiveLimit mu fam := by
    intro I
    rfl
  have hnu : IsProjectiveLimit nu fam := by
    rw [MeasureTheory.isProjectiveLimit_nat_iff hfam]
    intro n
    change nu.map (Preorder.frestrictLe n) = mu.map (Preorder.frestrictLe n)
    exact (h n).symm
  haveI (I : Finset ℕ) : IsFiniteMeasure (fam I) := by
    dsimp [fam]
    infer_instance
  exact hmu.unique hnu

/-- Exact machine-level specification of the probability law in Theorem 3.1. The
zeroth-prefix equality is the singleton-product representation of the initial law used
by mathlib's Ionescu--Tulcea theorem. -/
def MarkovPathLawSpec
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    (mu : Measure (ℕ → (S × X))) : Prop :=
  IsProbabilityMeasure mu ∧
    mu.map (Preorder.frestrictLe 0) =
      mu0.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => S × X)).symm ∧
    HasTransitionPair mu K

/-- The canonical Ionescu--Tulcea construction satisfies the exact path-law spec. -/
theorem pathLaw_spec
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] :
    MarkovPathLawSpec mu0 K (pathLaw mu0 K) := by
  exact ⟨inferInstance, pathLaw_prefix_zero mu0 K, pathLaw_has_transition_pair mu0 K⟩

/-- For a Markov kernel and an initial probability law there is exactly one trajectory
probability law satisfying the initial-prefix and transition identities. -/
theorem pathLaw_existsUnique
    (mu0 : Measure (S × X))
    (K : Kernel (S × X) (S × X))
    [IsProbabilityMeasure mu0] [IsMarkovKernel K] :
    ∃! mu : Measure (ℕ → (S × X)), MarkovPathLawSpec mu0 K mu := by
  refine ⟨pathLaw mu0 K, pathLaw_spec mu0 K, ?_⟩
  intro nu hnu
  letI : IsProbabilityMeasure nu := hnu.1
  apply measure_eq_of_prefix_maps_eq (pathLaw mu0 K) nu
  apply prefix_maps_eq_of_initial_and_transition K
  · exact (pathLaw_prefix_zero mu0 K).trans hnu.2.1.symm
  · exact pathLaw_has_transition_pair mu0 K
  · exact hnu.2.2

/-- Theorem 3.1, machine form: the typed composition `α → P → U` induces a
Markov kernel, and every initial probability law induces one and only one probability
law on infinite joint-state trajectories. -/
theorem joint_process_well_posed
    {A : Type*} [MeasurableSpace A]
    (alpha : Kernel (S × X) A)
    (P : Kernel ((S × X) × A) X)
    (U : Kernel ((S × X) × (A × X)) S)
    [IsMarkovKernel alpha] [IsMarkovKernel P] [IsMarkovKernel U]
    (mu0 : Measure (S × X)) [IsProbabilityMeasure mu0] :
    IsMarkovKernel (jointKernel alpha P U) ∧
      ∃! mu : Measure (ℕ → (S × X)),
        MarkovPathLawSpec mu0 (jointKernel alpha P U) mu := by
  have hK : IsMarkovKernel (jointKernel alpha P U) :=
    jointKernel_isMarkov alpha P U
  letI : IsMarkovKernel (jointKernel alpha P U) := hK
  exact ⟨hK, pathLaw_existsUnique mu0 (jointKernel alpha P U)⟩

end Permansson
