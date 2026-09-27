import Zeta23.CCM.CanonicalOneStepDomination

noncomputable section

namespace Zeta23.CCM

/-! # Closure campaign B1: singular-safe canonical Schur interface -/

abbrev CanonicalSchurCertificateAt
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop :=
  canonicalOneStepDomination p L N

theorem not_canonicalSchurCertificateAt_iff
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    ¬ CanonicalSchurCertificateAt p L N ↔
      cubicShellRealEnergy p L N < 0 ∨
        ∃ w : intrinsicParityPredecessorSubspace p N,
          cubicOneStepDeterminant p L N w < 0 := by
  exact not_canonicalOneStepDomination_iff p L N

end Zeta23.CCM

#print axioms Zeta23.CCM.not_canonicalSchurCertificateAt_iff
