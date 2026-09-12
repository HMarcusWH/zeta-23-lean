import Zeta23.CCM.CanonicalPolePrimeDiscrepancy

noncomputable section

namespace Zeta23.CCM

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ArithmeticFunction Interval

/-!
# FB-02 closure: discrepancy subtraction and canonical normal form

This small closure layer composes the separately compiler-audited pole and prime
integral identities.  It introduces no new arithmetic object: it only proves
that their difference is exactly the previously defined cumulative discrepancy
energy, then substitutes that difference into the production canonical channel
split.

No discrepancy sign, positivity theorem, negative-root exclusion,
finite-to-infinite closure, or RH theorem is asserted here.
-/

private theorem prime_log_mem_aperture_closure
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

private theorem intervalIntegrable_step_mul_continuous_closure
    {a L c : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L)
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable
      (fun t : ℝ => (if a ≤ t then c else 0) * f t) volume 0 L := by
  let h : ℝ → ℝ := fun t => (if a ≤ t then c else 0) * f t
  have hleft : IntervalIntegrable h volume 0 a := by
    have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a :=
      continuous_const.intervalIntegrable 0 a
    apply hz.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) a := by
      simpa [uIoo_of_le ha0] using ht
    simp [h, not_le.mpr ht'.2]
  have hright : IntervalIntegrable h volume a L := by
    have hc : Continuous (fun t : ℝ => c * f t) := continuous_const.mul hf
    have hi := hc.intervalIntegrable a L
    apply hi.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo a L := by
      simpa [uIoo_of_le haL] using ht
    simp [h, le_of_lt ht'.1]
  exact hleft.trans hright

private theorem intervalIntegrable_poleCumulative_deriv
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    IntervalIntegrable
      (fun t : ℝ =>
        canonicalPoleCumulativeWeight t *
          deriv (sourceAtomRealEnergy K x) (1 - t / L)) volume 0 L := by
  have hsmooth : ContDiff ℝ ∞ (sourceAtomRealEnergy K x) := by
    simpa using contDiff_sourceAtomRealEnergy K x
  have hD : Continuous (fun t : ℝ =>
      deriv (sourceAtomRealEnergy K x) (1 - t / L)) := by
    have hd := hsmooth.continuous_deriv (by simp)
    fun_prop
  have hA : Continuous canonicalPoleCumulativeWeight := by
    unfold canonicalPoleCumulativeWeight
    fun_prop
  exact (hA.mul hD).intervalIntegrable 0 L

private theorem intervalIntegrable_primeCumulative_deriv
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    IntervalIntegrable
      (fun t : ℝ =>
        canonicalPrimeCumulativeWeight L t *
          deriv (sourceAtomRealEnergy K x) (1 - t / L)) volume 0 L := by
  let D : ℝ → ℝ := fun t =>
    deriv (sourceAtomRealEnergy K x) (1 - t / L)
  have hDcont : Continuous D := by
    have hsmooth : ContDiff ℝ ∞ (sourceAtomRealEnergy K x) := by
      simpa using contDiff_sourceAtomRealEnergy K x
    have hd := hsmooth.continuous_deriv (by simp)
    dsimp [D]
    fun_prop
  unfold canonicalPrimeCumulativeWeight
  have hfun :
      (fun t : ℝ =>
        (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          if Real.log q ≤ t then Λ q / Real.sqrt q else 0) * D t) =
      fun t =>
        ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
          (if Real.log q ≤ t then (Λ q / Real.sqrt q : ℝ) else 0) * D t := by
    funext t
    rw [Finset.sum_mul]
  rw [hfun]
  apply intervalIntegral.intervalIntegrable_finsetSum
  intro q hq
  obtain ⟨hlog0, hlogL⟩ := prime_log_mem_aperture_closure hq
  exact intervalIntegrable_step_mul_continuous_closure
    hlog0 hlogL hDcont

/-- Headline FB-02 identity: exact pole energy minus exact finite prime energy is
precisely the cumulative pole-prime discrepancy tested against the derivative
of the elementary source-atom energy. -/
theorem matrixRealEnergy_pole_sub_prime_eq_discrepancy
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPoleMatrix L K) x -
        matrixRealEnergy (canonicalPrimeMatrix L K) x =
      canonicalPolePrimeDiscrepancyEnergy L K x := by
  rw [matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral hL K x,
    matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral hL K x]
  unfold canonicalPolePrimeDiscrepancyEnergy canonicalPolePrimeDiscrepancy
  have hpole := intervalIntegrable_poleCumulative_deriv hL K x
  have hprime := intervalIntegrable_primeCumulative_deriv hL K x
  have hfun :
      (fun t : ℝ =>
        (canonicalPoleCumulativeWeight t - canonicalPrimeCumulativeWeight L t) *
          deriv (sourceAtomRealEnergy K x) (1 - t / L)) =
      fun t =>
        canonicalPoleCumulativeWeight t *
            deriv (sourceAtomRealEnergy K x) (1 - t / L) -
          canonicalPrimeCumulativeWeight L t *
            deriv (sourceAtomRealEnergy K x) (1 - t / L) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_sub hpole hprime]
  ring

/-- The complete production canonical source-channel energy with the separately
large pole and prime terms eliminated in favor of their exact discrepancy. -/
theorem canonicalSourceChannelEnergy_eq_discrepancy
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalSourceChannelEnergy L K x =
      canonicalPolePrimeDiscrepancyEnergy L K x
        - matrixRealEnergy
            (reducedCanonicalArchDiagonalMatrix L K) x
        - matrixRealEnergy
            (reducedCanonicalArchOffDiagonalMatrix L K) x
        - canonicalArchScalarCorrection L * ‖x‖ ^ 2 := by
  calc
    canonicalSourceChannelEnergy L K x =
        (matrixRealEnergy (canonicalPoleMatrix L K) x -
          matrixRealEnergy (canonicalPrimeMatrix L K) x) -
          matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x -
          matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x -
          canonicalArchScalarCorrection L * ‖x‖ ^ 2 := by
            unfold canonicalSourceChannelEnergy
            rw [matrixRealEnergy_canonicalPrimeMatrix_eq_sum_sourceMatrix L K x]
            ring
    _ = _ := by
      rw [matrixRealEnergy_pole_sub_prime_eq_discrepancy hL K x]

end Zeta23.CCM

#print axioms Zeta23.CCM.matrixRealEnergy_pole_sub_prime_eq_discrepancy
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_eq_discrepancy
