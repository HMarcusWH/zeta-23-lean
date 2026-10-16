import Zeta23.CCM.CanonicalPrimeSeamTaylor
import Zeta23.CCM.KernelAnalysis

noncomputable section

namespace Zeta23.CCM

/-- The entering prime-power source atom is at omega=0 at its actual
logarithmic seam. This is the endpoint cancellation used by the padded
fixed-Q interval checker, not the different omega=1 matrix. -/
theorem step123_enteringPrimeSourceMatrix_zero (q K : ℕ)
    (hq : 1 < q) : sourceMatrix (primeSourceCoordinate q (Real.log q)) K = 0 := by
  have hlog : Real.log (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hq))
  have hcoord : primeSourceCoordinate q (Real.log q) = 0 := by
    simpa using primeSourceCoordinate_log_add q 0 (by simpa using hlog)
  rw [hcoord, sourceMatrix_zero]

theorem step123_qBasis_logSeam_zero (q : ℕ) (hq : 1 < q) (n m : ℤ) :
    qBasis n m (Real.log q) (Real.log q) = 0 := by
  exact qBasis_aperture_eq_zero
    (ne_of_gt (Real.log_pos (by exact_mod_cast hq))) n m

end Zeta23.CCM

#print axioms Zeta23.CCM.step123_enteringPrimeSourceMatrix_zero
#print axioms Zeta23.CCM.step123_qBasis_logSeam_zero
