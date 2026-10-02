import Zeta23.CCM.FirstCrossingStructuralCompatibility
import Zeta23.CCM.FirstCrossingSourceCertificate

noncomputable section

namespace Zeta23.CCM

structure FirstCrossingRelationSystem
    (α ιStruct ιSource : Type*) where
  structural : ιStruct → α → ℝ
  source : ιSource → α → ℝ

def FirstCrossingRelationSystem.StructuralCompatible
    {α ιStruct ιSource : Type*}
    (R : FirstCrossingRelationSystem α ιStruct ιSource)
    (x : α) : Prop :=
  ∀ i, R.structural i x = 0

def FirstCrossingRelationSystem.SourceCompatible
    {α ιStruct ιSource : Type*}
    (R : FirstCrossingRelationSystem α ιStruct ιSource)
    (x : α) : Prop :=
  ∀ i, R.source i x = 0

def FirstCrossingRelationSystem.combined
    {α ιStruct ιSource : Type*}
    (R : FirstCrossingRelationSystem α ιStruct ιSource) :
    Sum ιStruct ιSource → α → ℝ
  | Sum.inl i => R.structural i
  | Sum.inr i => R.source i

theorem target_eq_zero_of_structural_source_certificate
    {α ιStruct ιSource : Type*}
    [Fintype ιStruct] [Fintype ιSource]
    (R : FirstCrossingRelationSystem α ιStruct ιSource)
    (target : α → ℝ)
    (hcert : ExactSourceCertificate R.combined target)
    (x : α)
    (hstruct : R.StructuralCompatible x)
    (hsource : R.SourceCompatible x) :
    target x = 0 := by
  apply target_eq_zero_of_exactSourceCertificate hcert x
  intro i
  rcases i with i | i
  · exact hstruct i
  · exact hsource i

end Zeta23.CCM

#print axioms Zeta23.CCM.target_eq_zero_of_structural_source_certificate
