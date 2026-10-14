import Zeta23.CCM.OriginalDetectorFourierPrerequisites
import Zeta23.CCM.OriginalDetectorWindowBounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Derivative bounds for the literal divided original lobe

The function is the actual source `q_s(x-c) / sin^8(πx/L)`. The inverse
window is used only where the source can be nonzero. Outside the compact
lobe support, the quotient is locally zero even at the window zeros.
Leibniz combines the source-derived Gevrey bound and the half-unit Cauchy
bound, giving the explicit derivative scale `A_s + 2`.

This module is a prerequisite for the mandated Fourier truncation, not a
finite-image construction or a normalized detector estimate.
-/

noncomputable section

open Set Metric Complex

namespace Zeta23.CCM

/-- The literal positive original lobe divided by the degree-four window. -/
def originalDetectorDividedLobe (s L c x : ℝ) : ℂ :=
  originalDetectorLobe s c x /
    (Complex.sin ((Real.pi : ℂ) * (x : ℂ) / (L : ℂ)) ^ 8)

theorem originalDetectorDividedLobe_eq_mul (s L c : ℝ) :
    originalDetectorDividedLobe s L c = originalDetectorLobe s c *
      (fun x : ℝ => originalDetectorWindowReciprocal L (x : ℂ)) := by
  funext x
  simp only [originalDetectorDividedLobe, originalDetectorWindowReciprocal,
    Pi.mul_apply, div_eq_mul_inv]

/-- Dividing by the window cannot enlarge the support of the actual lobe,
including at the zeros where Lean's quotient is zero. -/
theorem originalDetectorDividedLobe_support {s : ℝ} (hs : 0 < s) (L c : ℝ) :
    tsupport (originalDetectorDividedLobe s L c) ⊆ Icc (c - s) (c + s) := by
  rw [originalDetectorDividedLobe_eq_mul]
  exact tsupport_mul_subset_left.trans (originalDetectorLobe_support hs c)

private theorem dividedLobe_eventually_zero_of_outside_collar
    {s L c x : ℝ} (hs : 0 < s) (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (hx : x ∉ Icc 1 (L - 1)) :
    originalDetectorDividedLobe s L c =ᶠ[𝓝 x] (fun _ => 0) := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro h
  have hh := originalDetectorDividedLobe_support hs L c h
  exact hx ⟨by linarith [hh.1], hh.2.trans hright⟩

/-- Global smoothness comes from the reciprocal on the collar and the
locally zero source outside it. It does not assume global smoothness of
the reciprocal window. -/
theorem originalDetectorDividedLobe_contDiff
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) :
    ContDiff ℝ (⊤ : ℕ∞) (originalDetectorDividedLobe s L c) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Icc 1 (L - 1)
  · rw [originalDetectorDividedLobe_eq_mul]
    exact (originalDetectorLobe_contDiff hs c).contDiffAt.mul
      (originalDetectorWindowReciprocal_real_contDiffAt hL hx.1 hx.2 _)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (dividedLobe_eventually_zero_of_outside_collar hs hleft hright hx)

private theorem factorial_product_le_square {m k : ℕ} (hk : k ≤ m) :
    (Nat.factorial k : ℝ) ^ 2 * (Nat.factorial (m - k) : ℝ) ≤
      (Nat.factorial m : ℝ) ^ 2 := by
  have hkfac : (Nat.factorial k : ℝ) ≤ (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_le hk
  have hprod : (Nat.factorial k : ℝ) * (Nat.factorial (m - k) : ℝ) ≤
      (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos m)
      (Nat.factorial_mul_factorial_dvd_factorial hk)
  calc
    _ = (Nat.factorial k : ℝ) *
        ((Nat.factorial k : ℝ) * (Nat.factorial (m - k) : ℝ)) := by ring
    _ ≤ (Nat.factorial m : ℝ) * (Nat.factorial m : ℝ) :=
      mul_le_mul hkfac hprod (by positivity) (by positivity)
    _ = _ := by ring

/-- The divided lobe's actual source-defined budget. -/
def originalDetectorDividedLobeJetBudget (s L : ℝ) (m : ℕ) : ℝ :=
  (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) * L ^ 8 *
    (12 / (UniversalSinc.gevreyMomentScale s) ^ 2 + 2) ^ m *
    (Nat.factorial m : ℝ) ^ 2

private theorem dividedLobe_iteratedDeriv_le_on_collar
    {s L c x : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hxlo : 1 ≤ x) (hxhi : x ≤ L - 1) (m : ℕ) :
    ‖iteratedDeriv m (originalDetectorDividedLobe s L c) x‖ ≤
      originalDetectorDividedLobeJetBudget s L m := by
  let C : ℝ := 4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)
  let A : ℝ := 12 / (UniversalSinc.gevreyMomentScale s) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hLnonneg : 0 ≤ L := by linarith
  have hmOrder : (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)
  have hq : ContDiffAt ℝ m (originalDetectorLobe s c) x :=
    ((originalDetectorLobe_contDiff hs c).of_le hmOrder).contDiffAt
  have hg := originalDetectorWindowReciprocal_real_contDiffAt hL hxlo hxhi
    (m : WithTop ℕ∞)
  rw [originalDetectorDividedLobe_eq_mul, iteratedDeriv_mul hq hg]
  calc
    _ ≤ ∑ k ∈ Finset.range (m + 1),
        ‖(m.choose k : ℂ) * iteratedDeriv k (originalDetectorLobe s c) x *
          iteratedDeriv (m - k)
            (fun y : ℝ => originalDetectorWindowReciprocal L (y : ℂ)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1),
        C * L ^ 8 * (Nat.factorial m : ℝ) ^ 2 *
          (A ^ k * 2 ^ (m - k) * (m.choose k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
      have hqb : ‖iteratedDeriv k (originalDetectorLobe s c) x‖ ≤
          C * A ^ k * (Nat.factorial k : ℝ) ^ 2 :=
        originalDetectorLobe_iteratedDeriv_le_gevrey hs k c x
      have hgb := originalDetectorWindowReciprocal_real_iteratedDeriv_le hL hxlo hxhi
        (m - k)
      have hfac := factorial_product_le_square hkm
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (m.choose k : ℝ) * (C * A ^ k * (Nat.factorial k : ℝ) ^ 2) *
            (L ^ 8 * 2 ^ (m - k) * (Nat.factorial (m - k) : ℝ)) := by
          gcongr
        _ = (C * L ^ 8 * (A ^ k * 2 ^ (m - k) * (m.choose k : ℝ))) *
            ((Nat.factorial k : ℝ) ^ 2 * (Nat.factorial (m - k) : ℝ)) := by ring
        _ ≤ (C * L ^ 8 * (A ^ k * 2 ^ (m - k) * (m.choose k : ℝ))) *
            (Nat.factorial m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = _ := by ring
    _ = C * L ^ 8 * (A + 2) ^ m * (Nat.factorial m : ℝ) ^ 2 := by
      rw [← Finset.mul_sum, ← add_pow]
      ring
    _ = originalDetectorDividedLobeJetBudget s L m := rfl

/-- Every real jet of the literal divided lobe has the Gevrey-order-two
budget derived from the original source and the actual sine reciprocal.
No estimate is supplied by the caller. -/
theorem originalDetectorDividedLobe_iteratedDeriv_le_gevrey
    {s L c : ℝ} (hs : 0 < s) (hL : 2 ≤ L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (m : ℕ) (x : ℝ) :
    ‖iteratedDeriv m (originalDetectorDividedLobe s L c) x‖ ≤
      originalDetectorDividedLobeJetBudget s L m := by
  by_cases hx : x ∈ Icc 1 (L - 1)
  · exact dividedLobe_iteratedDeriv_le_on_collar hs hL hx.1 hx.2 m
  · have heq := dividedLobe_eventually_zero_of_outside_collar hs hleft hright hx
    rw [heq.iteratedDeriv_eq m]
    simp only [iteratedDeriv_const, ite_self, norm_zero]
    unfold originalDetectorDividedLobeJetBudget
    positivity

/-- Compact support and the unit endpoint collars kill all endpoint jets
of the actual quotient, including at both zeros of the multiplier. -/
theorem originalDetectorDividedLobe_endpoint_jets
    {s L c : ℝ} (hs : 0 < s) (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (m : ℕ) :
    iteratedDeriv m (originalDetectorDividedLobe s L c) 0 = 0 ∧
      iteratedDeriv m (originalDetectorDividedLobe s L c) L = 0 := by
  constructor
  · have hx : (0 : ℝ) ∉ Icc 1 (L - 1) := by simp
    have heq := dividedLobe_eventually_zero_of_outside_collar hs hleft hright hx
    simpa only [iteratedDeriv_const, ite_self] using heq.iteratedDeriv_eq m
  · have hx : L ∉ Icc 1 (L - 1) := by intro h; linarith [h.2]
    have heq := dividedLobe_eventually_zero_of_outside_collar hs hleft hright hx
    simpa only [iteratedDeriv_const, ite_self] using heq.iteratedDeriv_eq m

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorDividedLobe_support
#print axioms Zeta23.CCM.originalDetectorDividedLobe_contDiff
#print axioms Zeta23.CCM.originalDetectorDividedLobe_iteratedDeriv_le_gevrey
#print axioms Zeta23.CCM.originalDetectorDividedLobe_endpoint_jets
