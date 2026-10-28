/-! Independently specified finite targets for the general bounded proposer.
These are protocol controls, not arithmetic research results. Their definitions
do not contain proofs or authorize an answer constant in the proposer menu. -/
namespace Zeta23.RHRC.OpicaComposition.SearchExamples

def ChainTarget : Prop :=
  ∀ P Q R : Prop, P → (P → Q) → (Q → R) → R

def DependentChainTarget : Prop :=
  ∀ (α : Type) (P Q R : α → Prop) (x : α),
    P x → (∀ y, P y → Q y) → (∀ y, Q y → R y) → R x

def ExistentialChainTarget : Prop :=
  ∀ (α : Type) (P : α → Prop) (R : Prop),
    (∃ x, P x) → (∀ x, P x → R) → R

def DisjunctiveChainTarget : Prop :=
  ∀ P Q R : Prop, (P ∨ Q) → (P → R) → (Q → R) → R

def MismatchedWitnessTarget : Prop :=
  ∀ (α : Type) (P Q : α → Prop) (x y : α),
    P x → (∀ z, P z → Q z) → Q y

end Zeta23.RHRC.OpicaComposition.SearchExamples
