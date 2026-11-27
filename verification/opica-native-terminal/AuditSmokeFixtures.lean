/-! Deliberately bad proofs: only the isolated audit smoke job imports this module.
It is not a claim-bearing library and its origin is rejected by production audits. -/
namespace New
theorem grh : True := True.intro
def zeros_on_line : Prop := True
end New

namespace OPICAAuditFixtures
axiom forbidden : True
theorem badAxiom : True := forbidden
theorem badSorry : True := by sorry
def hiddenEndpoint : True := New.grh
theorem usesHiddenEndpoint : True := hiddenEndpoint
theorem typeOnly (_h : New.zeros_on_line) : True := True.intro
inductive Branch where
  | left
  | right
def picked : Branch := Branch.left
theorem good : True := True.intro
end OPICAAuditFixtures
