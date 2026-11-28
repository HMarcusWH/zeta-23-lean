/-! Deliberately invalid audit fixtures, isolated from the terminal proof.
Production audits reject this module's origin. Never import it in a proof root.
-/
namespace New
theorem grh : True := True.intro
end New

-- Isolated mock target for the semantic-alias control. This Init-only fixture
-- must never be imported with Mathlib or by a production proof/audit root.
def RiemannHypothesis : Prop := ∀ n : Nat, n = n

namespace DirectWindowFixtures
abbrev AliasTarget := RiemannHypothesis
theorem aliasEndpoint : AliasTarget := fun _ => rfl
theorem hiddenRH : AliasTarget ∧ True := ⟨aliasEndpoint, True.intro⟩
axiom forbidden : True
theorem extraAxiom : True := forbidden
theorem admitted : True := by sorry
def hidden : True := New.grh
theorem hiddenEndpoint : True := hidden
theorem typeOnly (_h : New.grh = True.intro) : True := True.intro
inductive Branch where
  | good
  | bad (_h : New.grh = True.intro)
def structuralEndpoint : Branch := Branch.good
theorem good : True := True.intro
end DirectWindowFixtures
