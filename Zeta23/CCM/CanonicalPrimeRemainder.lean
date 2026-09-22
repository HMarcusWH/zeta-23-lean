import Zeta23.CCM.CanonicalPolePrimeDiscrepancy

noncomputable section

namespace Zeta23.CCM

open MeasureTheory Set
open scoped BigOperators ArithmeticFunction Interval

/-!
# Canonical prime remainder: the pole-prime discrepancy in classical form

`CanonicalPolePrimeDiscrepancy` rewrites the pole-minus-prime part of the
canonical source energy as the finite cumulative discrepancy

```text
canonicalPoleCumulativeWeight t - canonicalPrimeCumulativeWeight L t
```

tested against the derivative of the exact source-atom energy.  The prime
staircase there is indexed by the aperture horizon `q ≤ exp L` together with
the cutoff `log q ≤ t`.  This module removes that aperture dependence and
identifies the discrepancy with the classical remainder of the weighted
Chebyshev sum used by `Zeta23.ChebyshevMertens.cheb1b`:

```text
R(x) := ∑_{n ≤ x} Λ(n)/√n - 2√x,
canonicalPolePrimeDiscrepancy L t = -2 e^{-t/2} - R(e^t)      (t ≤ L).
```

Consequently the complete canonical source energy splits into exactly one
prime-dependent term, the energy of `R(e^t)`, and a prime-free budget made of
the exponentially small pole tail and the reduced archimedean channels.

Everything here is unconditional finite algebra plus one interval-integral
split.  No sign of `R`, no positivity, no terminal gate, and no statement
about zeta zeros is used or proved.  This module deliberately imports nothing
from the terminal `ExceptionalZero` layer.
-/

/-! ## Classical weighted Chebyshev sum -/

/-- The classical weighted Chebyshev sum `∑_{n ≤ x} Λ(n)/√n`, in exactly the
notation of `Zeta23.ChebyshevMertens.cheb1b`. -/
def weightedVonMangoldtSqrtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n

/-- Remainder of the weighted Chebyshev sum after its prime-number-theorem
main term `2√x`. -/
def weightedVonMangoldtSqrtRemainder (x : ℝ) : ℝ :=
  weightedVonMangoldtSqrtSum x - 2 * Real.sqrt x

/-- The `n = 1` term vanishes, so the weighted sum may start at `2`, matching
the index set of the canonical prime channel. -/
theorem weightedVonMangoldtSqrtSum_eq_sum_Icc_two (x : ℝ) :
    weightedVonMangoldtSqrtSum x =
      ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, Λ n / Real.sqrt n := by
  unfold weightedVonMangoldtSqrtSum
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc]
    omega
  · intro n hn hn'
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc] at hn'
    have h1 : n = 1 := by omega
    subst h1
    simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- The weighted Chebyshev sum is monotone. -/
theorem weightedVonMangoldtSqrtSum_monotone :
    Monotone weightedVonMangoldtSqrtSum := by
  intro a b hab
  unfold weightedVonMangoldtSqrtSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc_right (Nat.floor_mono hab)
  · intro n _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-! ## Horizon collapse -/

/-- **Horizon collapse.**  Below the aperture, the canonical cumulative prime
staircase does not depend on the aperture: it is the classical weighted
Chebyshev sum at `x = e^t`. -/
theorem canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum
    {L t : ℝ} (htL : t ≤ L) :
    canonicalPrimeCumulativeWeight L t =
      weightedVonMangoldtSqrtSum (Real.exp t) := by
  rw [weightedVonMangoldtSqrtSum_eq_sum_Icc_two]
  unfold canonicalPrimeCumulativeWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h2, _⟩, hlog⟩
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) h2
    exact ⟨h2, Nat.le_floor ((Real.log_le_iff_le_exp hqpos).mp hlog)⟩
  · rintro ⟨h2, hq⟩
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) h2
    have hqexp : (q : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).mp hq
    exact ⟨⟨h2, Nat.le_floor (hqexp.trans (Real.exp_le_exp.mpr htL))⟩,
      (Real.log_le_iff_le_exp hqpos).mpr hqexp⟩

/-! ## Pole main term -/

private theorem sqrt_exp_eq_exp_half_cpr (t : ℝ) :
    Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  have h : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- The pole primitive is the PNT main term `2√x` at `x = e^t`, minus an
exponentially small tail. -/
theorem canonicalPoleCumulativeWeight_eq_two_sqrt_exp_sub_tail (t : ℝ) :
    canonicalPoleCumulativeWeight t =
      2 * Real.sqrt (Real.exp t) - 2 * Real.exp (-(t / 2)) := by
  rw [sqrt_exp_eq_exp_half_cpr]
  unfold canonicalPoleCumulativeWeight
  rw [Real.sinh_eq]
  ring

/-- **Exact discrepancy normal form.**  On the physical range the canonical
pole-prime discrepancy is minus the classical weighted-Chebyshev remainder,
up to the exponentially small pole tail. -/
theorem canonicalPolePrimeDiscrepancy_eq_neg_tail_sub_remainder
    {L t : ℝ} (htL : t ≤ L) :
    canonicalPolePrimeDiscrepancy L t =
      -(2 * Real.exp (-(t / 2))) -
        weightedVonMangoldtSqrtRemainder (Real.exp t) := by
  unfold canonicalPolePrimeDiscrepancy weightedVonMangoldtSqrtRemainder
  rw [canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum htL,
    canonicalPoleCumulativeWeight_eq_two_sqrt_exp_sub_tail]
  ring

/-! ## Energy split -/

/-- Energy of the classical weighted-Chebyshev remainder against the exact
source-atom derivative.  This is the only prime-dependent term of the complete
canonical source energy. -/
def canonicalPrimeRemainderEnergy
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / L) *
    ∫ t in (0 : ℝ)..L,
      weightedVonMangoldtSqrtRemainder (Real.exp t) *
        deriv (sourceAtomRealEnergy K x) (1 - t / L)

/-- Energy of the exponentially small pole tail `2 e^{-t/2}`. -/
def canonicalPoleTailEnergy
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  (1 / L) *
    ∫ t in (0 : ℝ)..L,
      2 * Real.exp (-(t / 2)) *
        deriv (sourceAtomRealEnergy K x) (1 - t / L)

/-- Every prime-free term of the complete canonical source energy: the pole
tail, the reduced archimedean diagonal and off-diagonal channels, and the
archimedean scalar normalization. -/
def canonicalPrimeFreeBudget
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  canonicalPoleTailEnergy L K x
    + matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x
    + matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x
    + canonicalArchScalarCorrection L * ‖x‖ ^ 2

private theorem continuous_sourceAtomDeriv_cpr
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    Continuous (fun t : ℝ => deriv (sourceAtomRealEnergy K x) (1 - t / L)) := by
  have hsmooth : ContDiff ℝ ⊤ (sourceAtomRealEnergy K x) :=
    contDiff_sourceAtomRealEnergy K x
  have hd := hsmooth.continuous_deriv (by simp)
  fun_prop

/-- The pole-prime discrepancy energy splits exactly into the pole-tail energy
and the classical prime-remainder energy. -/
theorem canonicalPolePrimeDiscrepancyEnergy_eq_neg_tail_sub_remainder
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalPolePrimeDiscrepancyEnergy L K x =
      -canonicalPoleTailEnergy L K x - canonicalPrimeRemainderEnergy L K x := by
  let D : ℝ → ℝ := fun t => deriv (sourceAtomRealEnergy K x) (1 - t / L)
  have hDcont : Continuous D := continuous_sourceAtomDeriv_cpr L K x
  have htailInt : IntervalIntegrable
      (fun t : ℝ => 2 * Real.exp (-(t / 2)) * D t) volume 0 L := by
    have hexp : Continuous (fun t : ℝ => 2 * Real.exp (-(t / 2))) := by
      fun_prop
    exact (hexp.mul hDcont).intervalIntegrable 0 L
  have hremInt : IntervalIntegrable
      (fun t : ℝ => weightedVonMangoldtSqrtRemainder (Real.exp t) * D t)
      volume 0 L := by
    have hsumInt : IntervalIntegrable
        (fun t : ℝ => weightedVonMangoldtSqrtSum (Real.exp t)) volume 0 L :=
      (weightedVonMangoldtSqrtSum_monotone.comp
        Real.exp_monotone).intervalIntegrable
    have hsqrtInt : IntervalIntegrable
        (fun t : ℝ => 2 * Real.sqrt (Real.exp t)) volume 0 L := by
      have hc : Continuous (fun t : ℝ => 2 * Real.sqrt (Real.exp t)) :=
        continuous_const.mul (Real.continuous_sqrt.comp Real.continuous_exp)
      exact hc.intervalIntegrable 0 L
    have hR : IntervalIntegrable
        (fun t : ℝ => weightedVonMangoldtSqrtRemainder (Real.exp t))
        volume 0 L := by
      unfold weightedVonMangoldtSqrtRemainder
      exact hsumInt.sub hsqrtInt
    exact hR.mul_continuousOn hDcont.continuousOn
  have hcongr :
      (∫ t in (0 : ℝ)..L, canonicalPolePrimeDiscrepancy L t * D t) =
        ∫ t in (0 : ℝ)..L,
          -(2 * Real.exp (-(t / 2)) * D t) -
            weightedVonMangoldtSqrtRemainder (Real.exp t) * D t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htL : t ≤ L := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith
    show canonicalPolePrimeDiscrepancy L t * D t =
      -(2 * Real.exp (-(t / 2)) * D t) -
        weightedVonMangoldtSqrtRemainder (Real.exp t) * D t
    rw [canonicalPolePrimeDiscrepancy_eq_neg_tail_sub_remainder htL]
    ring
  have hsplit :
      (∫ t in (0 : ℝ)..L,
          -(2 * Real.exp (-(t / 2)) * D t) -
            weightedVonMangoldtSqrtRemainder (Real.exp t) * D t) =
        -(∫ t in (0 : ℝ)..L, 2 * Real.exp (-(t / 2)) * D t) -
          ∫ t in (0 : ℝ)..L,
            weightedVonMangoldtSqrtRemainder (Real.exp t) * D t := by
    have htailNegInt : IntervalIntegrable
        (fun t : ℝ => -(2 * Real.exp (-(t / 2)) * D t)) volume 0 L :=
      htailInt.neg
    have hneg :
        (∫ t in (0 : ℝ)..L, -(2 * Real.exp (-(t / 2)) * D t)) =
          -(∫ t in (0 : ℝ)..L, 2 * Real.exp (-(t / 2)) * D t) :=
      intervalIntegral.integral_neg
    rw [← hneg]
    exact intervalIntegral.integral_sub htailNegInt hremInt
  unfold canonicalPolePrimeDiscrepancyEnergy canonicalPoleTailEnergy
    canonicalPrimeRemainderEnergy
  change
    (1 / L) * (∫ t in (0 : ℝ)..L, canonicalPolePrimeDiscrepancy L t * D t) =
      -((1 / L) * ∫ t in (0 : ℝ)..L, 2 * Real.exp (-(t / 2)) * D t) -
        (1 / L) *
          ∫ t in (0 : ℝ)..L,
            weightedVonMangoldtSqrtRemainder (Real.exp t) * D t
  rw [hcongr, hsplit]
  ring

/-- **Arithmetic normal form of the complete canonical source energy.**

The complete canonical source energy is minus the classical prime-remainder
energy minus a prime-free budget.  No sign of either side is asserted. -/
theorem canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalSourceChannelEnergy L K x =
      -canonicalPrimeRemainderEnergy L K x - canonicalPrimeFreeBudget L K x := by
  rw [canonicalSourceChannelEnergy_eq_discrepancy hL K x,
    canonicalPolePrimeDiscrepancyEnergy_eq_neg_tail_sub_remainder hL K x]
  unfold canonicalPrimeFreeBudget
  ring

/-- Nonnegativity of the complete canonical source energy is exactly the
dominance of the prime-free budget by minus the prime-remainder energy. -/
theorem canonicalSourceChannelEnergy_nonneg_iff_budget_le
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    0 ≤ canonicalSourceChannelEnergy L K x ↔
      canonicalPrimeFreeBudget L K x ≤ -canonicalPrimeRemainderEnergy L K x := by
  rw [canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget hL K x]
  constructor <;> intro h <;> linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.weightedVonMangoldtSqrtSum_eq_sum_Icc_two
#print axioms Zeta23.CCM.canonicalPrimeCumulativeWeight_eq_weightedVonMangoldtSqrtSum
#print axioms Zeta23.CCM.canonicalPoleCumulativeWeight_eq_two_sqrt_exp_sub_tail
#print axioms Zeta23.CCM.canonicalPolePrimeDiscrepancy_eq_neg_tail_sub_remainder
#print axioms Zeta23.CCM.canonicalPolePrimeDiscrepancyEnergy_eq_neg_tail_sub_remainder
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_nonneg_iff_budget_le
