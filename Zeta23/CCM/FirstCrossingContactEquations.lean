import Zeta23.CCM.FirstCrossingContactRegime
import Zeta23.CCM.GoodSectorKernelAnnihilation
import Zeta23.CCM.ZeroShiftSchurClassification

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#278 first-crossing contact equations

The contact successor has parity bottom exactly zero, hence it is a good
successor sector. Existing good-sector kernel annihilation can therefore be
specialized at the canonical first-crossing contact.

This is a specialization layer, not a new generic kernel theorem. Its purpose
is to expose the exact equations available at the counterexample-generated
contact before aperture differentiation.
-/

theorem CanonicalParityFirstCrossingShell.contact_not_parityBad
    (c : CanonicalParityFirstCrossingShell) :
    ¬ ParityBad c.p c.Lstar (c.k + 1) := by
  intro hbad
  have hneg := parityRayleighBottom_neg_of_parityBad hbad
  have hzero :
      paritySuccessorGround c.p c.k c.Lstar = 0 :=
    c.plateau_zero c.k c.n_le_k c.k_le_N
  change paritySuccessorGround c.p c.k c.Lstar < 0 at hneg
  rw [hzero] at hneg
  exact (lt_irrefl 0) hneg

theorem CanonicalParityFirstCrossingShell.contact_cubicCoupling_zero_on_kernel
    (c : CanonicalParityFirstCrossingShell)
    (z : intrinsicParityPredecessorSubspace c.p c.k)
    (hz : intrinsicPredecessorBlock c.p c.Lstar c.k z = 0) :
    inner ℂ
        (z : euclideanParityBoundaryFlatSubspace c.p (c.k + 1))
        ((intrinsicShellToPredecessor c.p c.Lstar c.k
            (intrinsicCubicShellPart c.p c.k) :
          intrinsicParityPredecessorSubspace c.p c.k) :
          euclideanParityBoundaryFlatSubspace c.p (c.k + 1)) = 0 := by
  have hk1 : 1 ≤ c.k := le_trans c.one_le_n c.n_le_k
  exact
    cubicCoupling_zero_on_intrinsicPredecessorBlock_kernel_of_not_parityBad
      c.p c.Lstar c.k hk1 c.contact_not_parityBad z hz

theorem CanonicalParityFirstCrossingShell.contact_cubicCouplingKernelPart_eq_zero
    (c : CanonicalParityFirstCrossingShell) :
    cubicCouplingKernelPart c.p c.Lstar c.k = 0 := by
  have hk1 : 1 ≤ c.k := le_trans c.one_le_n c.n_le_k
  exact
    cubicCouplingKernelPart_eq_zero_of_not_parityBad
      c.p c.Lstar c.k hk1 c.contact_not_parityBad

theorem CanonicalParityFirstCrossingShell.exists_contact_zeroShiftPreimage
    (c : CanonicalParityFirstCrossingShell) :
    ∃ x₀ : intrinsicParityPredecessorSubspace c.p c.k,
      intrinsicPredecessorBlock c.p c.Lstar c.k x₀ =
        intrinsicShellToPredecessor c.p c.Lstar c.k
          (intrinsicCubicShellPart c.p c.k) := by
  exact
    (cubicCouplingKernelPart_eq_zero_iff_exists_zeroShiftPreimage
      c.p c.Lstar c.k).1 c.contact_cubicCouplingKernelPart_eq_zero

end Zeta23.CCM

#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.contact_not_parityBad
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.contact_cubicCoupling_zero_on_kernel
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.contact_cubicCouplingKernelPart_eq_zero
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.exists_contact_zeroShiftPreimage
