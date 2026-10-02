import Zeta23.CCM.FirstCrossingBranchBridge
import Zeta23.CCM.FirstCrossingLiftedFeatures
import Zeta23.CCM.FirstCrossingContactEquations

noncomputable section

namespace Zeta23.CCM

def FirstCrossingStructuralCompatibility
    (c : CanonicalParityFirstCrossingShell) : Prop :=
  cubicCouplingKernelPart c.p c.Lstar c.k = 0 ∧
    ∃ x₀ : intrinsicParityPredecessorSubspace c.p c.k,
      intrinsicPredecessorBlock c.p c.Lstar c.k x₀ =
        intrinsicShellToPredecessor c.p c.Lstar c.k
          (intrinsicCubicShellPart c.p c.k)

theorem canonicalFirstCrossingStructuralCompatibility
    (c : CanonicalParityFirstCrossingShell) :
    FirstCrossingStructuralCompatibility c := by
  exact ⟨
    c.contact_cubicCouplingKernelPart_eq_zero,
    c.exists_contact_zeroShiftPreimage
  ⟩

def RegularEndpointEnergyCompatibility
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) : Prop :=
  (regularEndpointLiftedFeatures p L N hreg).endpointRe =
    (regularEndpointLiftedFeatures p L N hreg).shellEnergy -
      (regularEndpointLiftedFeatures p L N hreg).predecessorEnergy

theorem canonicalRegularEndpointEnergyCompatibility
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    RegularEndpointEnergyCompatibility p L N hreg :=
  regularEndpointLiftedFeatures_relation p L N hreg

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalFirstCrossingStructuralCompatibility
#print axioms Zeta23.CCM.canonicalRegularEndpointEnergyCompatibility
