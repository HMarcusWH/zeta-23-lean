/-! Evaluator-owned finite logic qualifications. These are not RH evidence,
and the target definitions and gold terms are excluded from proposer tables. -/
namespace Zeta23.RHRC.OpicaComposition.FiniteWorlds

def IdentityTarget : Prop := ∀ (p : Prop), p → p
def ConvertibleTarget : Prop := ∀ (p : Prop), (let q := p; q) → p
def TransportTarget : Prop := ∀ (p q : Prop), p = q → p → q
def SeparateWitnessTarget : Prop := ∀ (P : Nat → Prop) (a b : Nat), P a → P b
def ExistsTarget : Prop := ∀ (P : Nat → Prop), (∃ n, P n) → ∃ n, P n
def ForgedGoalTarget : Prop := ∀ (p : Prop), p
def PacketTarget : Prop := ∀ (p q : Prop), p ∧ q → p ∧ q
def EmptyTarget : Prop := True
def FalseTarget : Prop := False
def InstanceTarget : Prop := ∀ (α : Type) (a b : α), a = b → a = b
def ClassObligationTarget : Prop := ∀ (α : Type), True
def AuthorizedClassTarget : Prop := ∀ (α : Type) [Inhabited α], True

/-- The following explicit argument leaves no permission to invent an instance
when the evaluator target supplies only the rigid type alpha. -/
theorem instanceCarrier (α : Type) [Inhabited α] (_h : True) : True := True.intro

/-- PUnit at a fresh universe leaves u unresolved; the identical application
to Nat fixes u=0. Both applications have result type True before kernel entry. -/
theorem universeCarrier.{u} (_α : Type u) : True := True.intro

theorem identityGold : IdentityTarget := fun _ h => h
theorem transportGold : TransportTarget := fun _ _ h hp => h ▸ hp
theorem packetGold : PacketTarget := fun _ _ h => h

end Zeta23.RHRC.OpicaComposition.FiniteWorlds
