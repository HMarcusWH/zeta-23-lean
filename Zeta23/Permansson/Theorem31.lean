import Zeta23.Permansson.GeneralFramework

/-!
# Permansson v0.1.6 — Theorem 3.1

Machine formalization of the existence-and-uniqueness part of the paper's
`Joint-process well-posedness` theorem.  The transition-law condition is encoded by
`HasTransitionPair`, the finite-history joint-law identity equivalent (on standard
Borel state spaces) to saying that the canonical coordinate process has one-step
transition kernel `K`.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Permansson

universe uS uX

variable {S : Type uS} {X : Type uX}
variable [MeasurableSpace S] [MeasurableSpace X]

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

/-- Exact machine-level specification of the probability law in Theorem 3.1.  The
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
