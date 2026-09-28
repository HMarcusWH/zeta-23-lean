import Zeta23.CCM.ParityGroundPerturbation
import Zeta23.CCM.ParityRayleighPerturbation
import Zeta23.CCM.CanonicalApertureRegularityScaffold

namespace Zeta23.CCM

/-!
# Closure campaign A2: seam-ground transfer

The entering prime-power atom is exactly zero at its seam.  A complete seam
proof still needs a quantitative whole-form perturbation estimate: the fixed
cell background and the entering atom must be bounded separately.  Once those
two parity perturbation bounds are supplied, the legal global ground transfer
is now an actual theorem and is multiplicity-safe.
-/

structure CanonicalSeamGroundTransferData where
  q : ℕ
  K : ℕ
  branch : GroundBranchKind
  leadingOrder : ℕ
  coefficient : ℝ
  remainderConstant : ℝ
  remainder_nonnegative : 0 ≤ remainderConstant

/-- The source atom entering at q vanishes exactly at L = log q. -/
theorem canonicalSeamSourceAtom_eq_zero
    (q K : ℕ) (hq : 2 ≤ q) :
    sourceMatrix (primeSourceCoordinate q (Real.log q)) K = 0 :=
  sourceMatrix_primeSourceCoordinate_log_self q K hq

/-- Whole-form seam envelope.  This is deliberately phrased in terms of the
actual parity quadratic forms, not a chosen ground eigenvector. -/
def CanonicalSeamPerturbationEnvelope
    (L₁ L₂ εeven εodd : ℝ) (N : ℕ) : Prop :=
  ParityRayleighPerturbationBound .even L₁ L₂ (N + 1) εeven ∧
    ParityRayleighPerturbationBound .odd L₁ L₂ (N + 1) εodd

/-- Multiplicity-safe seam transfer for the actual legal successor ground. -/
theorem abs_globalParitySuccessorBottom_sub_le_of_seamEnvelope
    (L₁ L₂ εeven εodd : ℝ)
    (N : ℕ) (hN : 1 ≤ N)
    (h : CanonicalSeamPerturbationEnvelope L₁ L₂ εeven εodd N) :
    |globalParitySuccessorBottom L₁ N -
      globalParitySuccessorBottom L₂ N| ≤ max εeven εodd :=
  abs_globalParitySuccessorBottom_sub_le_of_parity_bounds
    L₁ L₂ εeven εodd N hN h.1 h.2

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSeamSourceAtom_eq_zero
#print axioms Zeta23.CCM.abs_globalParitySuccessorBottom_sub_le_of_seamEnvelope
