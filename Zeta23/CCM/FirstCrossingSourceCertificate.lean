import Zeta23.CCM.FirstCrossingArithmeticCompatibility

noncomputable section

namespace Zeta23.CCM

open scoped BigOperators

def ExactSourceCertificate
    {ι α : Type*} [Fintype ι]
    (relation : ι → α → ℝ)
    (target : α → ℝ) : Prop :=
  ∃ coeff : ι → ℝ,
    ∀ x : α,
      target x = ∑ i, coeff i * relation i x

theorem target_eq_zero_of_exactSourceCertificate
    {ι α : Type*} [Fintype ι]
    {relation : ι → α → ℝ}
    {target : α → ℝ}
    (hcert : ExactSourceCertificate relation target)
    (x : α)
    (hzero : ∀ i, relation i x = 0) :
    target x = 0 := by
  rcases hcert with ⟨coeff, hcoeff⟩
  rw [hcoeff x]
  simp [hzero]

end Zeta23.CCM

#print axioms Zeta23.CCM.target_eq_zero_of_exactSourceCertificate
