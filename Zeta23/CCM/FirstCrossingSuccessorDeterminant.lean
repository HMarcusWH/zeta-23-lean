import Zeta23.CCM.FirstCrossingContactEquations
import Mathlib.LinearAlgebra.Determinant

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 inverse-free successor determinant

The regular zero-shift endpoint is useful at nearby regular states, but the
chosen preimage should not be differentiated through a potentially singular
contact. The full finite successor determinant is inverse-free and is therefore
a safe scalar across both contact regimes.

This file proves only the exact contact zero forced by the kernel tower. A
regular-point factorization and a production sign germ remain separate theorem
targets.
-/

noncomputable def paritySuccessorDet
    (p : ReversalParity) (L : ℝ) (N : ℕ) : ℂ :=
  LinearMap.det (parityCompressedCanonical p L (N + 1))

theorem CanonicalParityFirstCrossingShell.contactKernelVector_ne_zero
    (c : CanonicalParityFirstCrossingShell) :
    parityPlateauExtend c.p c.n_le_k c.seed ≠ 0 := by
  exact
    parityPlateauExtend_ne_zero
      c.p c.n_le_k c.seed c.seed_ne

theorem CanonicalParityFirstCrossingShell.paritySuccessorDet_contact_eq_zero
    (c : CanonicalParityFirstCrossingShell) :
    paritySuccessorDet c.p c.Lstar c.k = 0 := by
  let v : euclideanParityBoundaryFlatSubspace c.p (c.k + 1) :=
    parityPlateauExtend c.p c.n_le_k c.seed
  have hvne : v ≠ 0 := by
    simpa [v] using c.contactKernelVector_ne_zero
  have hvker :
      parityCompressedCanonical c.p c.Lstar (c.k + 1) v = 0 := by
    simpa [v] using
      c.extended_kernel c.k c.n_le_k c.k_le_N
  have hkerne :
      LinearMap.ker
          (parityCompressedCanonical c.p c.Lstar (c.k + 1)) ≠ ⊥ := by
    intro hbot
    have hvMem :
        v ∈ LinearMap.ker
          (parityCompressedCanonical c.p c.Lstar (c.k + 1)) := by
      exact hvker
    rw [hbot] at hvMem
    have hv0 : v = 0 := by
      simpa using hvMem
    exact hvne hv0
  unfold paritySuccessorDet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hkerne

end Zeta23.CCM

#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.contactKernelVector_ne_zero
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.paritySuccessorDet_contact_eq_zero
