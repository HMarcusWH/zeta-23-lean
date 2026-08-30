import Zeta23.CCM.DictionaryZeroSideTentDefect
import Zeta23.CCM.DictionaryTentEFExtension

noncomputable section

namespace Zeta23.CCM

open Matrix

/-!
# Exact finite zero-side CCM bridge

PR #62 consumes the two already-proved ingredients that formalization exposed as
the shortest production route:

* H2+ (#57): the exact finite bridge is equivalent to vanishing of the
  N-independent literal-tent defect;
* M8 (#61): the literal canonical tent zero side equals its deterministic
  literature explicit-formula RHS.

No new analytic limit, zero-counting input, positivity claim, or finite-to-
infinite argument is introduced here.
-/

/-- The M8 literal-tent explicit formula kills the universal H2+ defect. -/
theorem dictionaryTentDefect_eq_zero
    (hs : ZetaSeam)
    {L : ℝ} (hL : 0 < L) :
    dictionaryTentDefect hs L = 0 := by
  unfold dictionaryTentDefect
  rw [dictionaryTent_zero_sum_eq_literatureRHS hs hL]
  simp

/-- Production finite zero-side bridge: for every finite dictionary size, the
actual zeta zero-side matrix is exactly the deterministic dictionary matrix. -/
theorem zeroSideMatrix_eq_dictionaryMatrix
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideMatrix hs N L = dictionaryMatrix L N := by
  exact
    (zeroSideMatrix_eq_dictionaryMatrix_iff_tentDefect_eq_zero
      hs N hL).2
      (dictionaryTentDefect_eq_zero hs hL)

/-- The complete H2+/M8 finite discrepancy now vanishes identically. -/
theorem zeroSideDiscrepancy_eq_zero
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideDiscrepancy hs N L = 0 := by
  rw [zeroSideDiscrepancy_eq_tentDefect_smul_ones hs N hL,
    dictionaryTentDefect_eq_zero hs hL]
  simp

/-- Registry-facing production normalization of the exact finite bridge. -/
theorem zeroSideMatrix_eq_finiteMatrix_add_correction
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    zeroSideMatrix hs N L =
      finiteMatrix L N +
        ((2 * cCorrection L : ℝ) : ℂ) •
          (1 : Matrix
            (Fin (2 * N + 1))
            (Fin (2 * N + 1)) ℂ) := by
  simpa [dictionaryMatrix] using
    zeroSideMatrix_eq_dictionaryMatrix hs N hL

end Zeta23.CCM

#print axioms Zeta23.CCM.dictionaryTentDefect_eq_zero
#print axioms Zeta23.CCM.zeroSideMatrix_eq_dictionaryMatrix
#print axioms Zeta23.CCM.zeroSideDiscrepancy_eq_zero
#print axioms Zeta23.CCM.zeroSideMatrix_eq_finiteMatrix_add_correction
