import Zeta23.CCM.CrossParitySecularTransferCore

noncomputable section

namespace Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A3c: cross-parity secular transfer

The implementation is split into three compiler-facing layers:

* `CrossParityQuotientTransport` — quotient/shell transport and exact
  predecessor corrections;
* `CrossParityTrialReconstruction` — transported residual, predecessor forcing,
  and safe-resolvent reconstruction;
* `CrossParitySecularTransferCore` — scalar transfer, overlap representation,
  and source-explicit specialization.

The mathematical interface is unchanged.  D remains algebraic only; no
unitary/isometric transport, coefficient sign/nonzeroness, branch exclusion,
negative-root exclusion, positivity closure, finite-to-infinite closure, or RH
claim is introduced.
-/

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicCubicQuotientCoordinate_evenIndex
#print axioms Zeta23.CCM.cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
#print axioms Zeta23.CCM.cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
#print axioms Zeta23.CCM.cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
#print axioms Zeta23.CCM.crossParitySecularGamma_eq_trial_cubic_overlap_div
#print axioms Zeta23.CCM.cubicSecularScalar_crossParity_source_transfer
#print axioms Zeta23.CCM.cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
