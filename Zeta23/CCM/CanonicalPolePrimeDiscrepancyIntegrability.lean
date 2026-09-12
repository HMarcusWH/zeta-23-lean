import Zeta23.CCM.CanonicalPolePrimeDiscrepancy

noncomputable section

namespace Zeta23.CCM

open MeasureTheory Set
open scoped BigOperators ArithmeticFunction

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB03: discrepancy integrability seam

FB-02 intentionally kept its step-function integration helpers private.  FB-03
needs a public interval-integrability theorem for the exact finite cumulative
pole-prime discrepancy before taking anchored primitives.  This file exposes
only that analytic seam; it does not smooth by differentiating the prime
staircase.
-/

private theorem primeLog_mem_aperture_fb03
    {L : ℝ} {q : ℕ}
    (hq : q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊) :
    0 ≤ Real.log q ∧ Real.log q ≤ L := by
  have hqmem := Finset.mem_Icc.mp hq
  have hqposNat : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 2) hqmem.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have hqexp : (q : ℝ) ≤ Real.exp L :=
    (Nat.le_floor_iff (Real.exp_pos L).le).mp hqmem.2
  exact ⟨Real.log_natCast_nonneg q,
    (by rw [← Real.log_exp L]; exact Real.log_le_log hqpos hqexp)⟩

private theorem intervalIntegrable_step_constant_fb03
    {a L c : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L) :
    IntervalIntegrable
      (fun t : ℝ => if a ≤ t then c else 0) volume 0 L := by
  let h : ℝ → ℝ := fun t => if a ≤ t then c else 0
  have hleft : IntervalIntegrable h volume 0 a := by
    have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a :=
      continuous_const.intervalIntegrable 0 a
    apply hz.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) a := by
      simpa [uIoo_of_le ha0] using ht
    simp [h, not_le.mpr ht'.2]
  have hright : IntervalIntegrable h volume a L := by
    have hc : IntervalIntegrable (fun _ : ℝ => c) volume a L :=
      continuous_const.intervalIntegrable a L
    apply hc.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo a L := by
      simpa [uIoo_of_le haL] using ht
    simp [h, le_of_lt ht'.1]
  exact hleft.trans hright

/-- The finite prime cumulative staircase is interval-integrable on its
physical aperture.  No continuity is claimed at prime-log thresholds. -/
theorem intervalIntegrable_canonicalPrimeCumulativeWeight
    {L : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (canonicalPrimeCumulativeWeight L) volume 0 L := by
  unfold canonicalPrimeCumulativeWeight
  let S : Finset ℕ := Finset.Icc 2 ⌊Real.exp L⌋₊
  let f : ℕ → ℝ → ℝ := fun q t =>
    if Real.log q ≤ t then Λ q / Real.sqrt q else 0
  have hsum :
      IntervalIntegrable (∑ q ∈ S, f q) volume 0 L := by
    apply IntervalIntegrable.sum
    intro q hq
    obtain ⟨hlog0, hlogL⟩ := primeLog_mem_aperture_fb03 hq
    exact intervalIntegrable_step_constant_fb03 hlog0 hlogL
  have hfun :
      (∑ q ∈ S, f q) = (fun t : ℝ => ∑ q ∈ S, f q t) := by
    funext t
    simp
  rw [hfun] at hsum
  simpa [S, f] using hsum

/-- The smooth pole cumulative weight is interval-integrable on every positive
physical aperture. -/
theorem intervalIntegrable_canonicalPoleCumulativeWeight
    {L : ℝ} (_hL : 0 < L) :
    IntervalIntegrable canonicalPoleCumulativeWeight volume 0 L := by
  have hcont : Continuous canonicalPoleCumulativeWeight := by
    unfold canonicalPoleCumulativeWeight
    fun_prop
  exact hcont.intervalIntegrable 0 L

/-- Public FB-02 -> FB-03 seam: the exact cancellation-preserving finite
pole-prime discrepancy is interval-integrable. -/
theorem intervalIntegrable_canonicalPolePrimeDiscrepancy
    {L : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (canonicalPolePrimeDiscrepancy L) volume 0 L := by
  unfold canonicalPolePrimeDiscrepancy
  exact
    (intervalIntegrable_canonicalPoleCumulativeWeight hL).sub
      (intervalIntegrable_canonicalPrimeCumulativeWeight hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.intervalIntegrable_canonicalPrimeCumulativeWeight
#print axioms Zeta23.CCM.intervalIntegrable_canonicalPolePrimeDiscrepancy
