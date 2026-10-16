import Zeta23.CCM.OriginalDetectorPaddedFiniteWindowBoundaryFlat

/-! # Higher endpoint flatness of the literal degree-four window -/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

/-- The exact `sin^8` window kills every jet below its order-eight zero. -/
theorem originalDetectorPaddedFiniteWindow_endpoint_jets_lt_eight
    {L : ℝ} (hL : 0 < L) {r : ℕ} (hr : r < 8) :
    iteratedDeriv r (originalDetectorPaddedFiniteWindow L) 0 = 0 ∧
      iteratedDeriv r (originalDetectorPaddedFiniteWindow L) L = 0 := by
  rw [originalDetectorPaddedFiniteWindow_iteratedDeriv hL]
  constructor <;> interval_cases r <;>
    simp only [originalDetectorPaddedFiniteWindowJet, originalDetectorPaddedFiniteWindowCoeff,
      originalDetectorFourierFrequency, AddCircle.coe_zero, AddCircle.coe_period,
      fourier_eval_zero, mul_one] <;>
    norm_num [Finset.sum_range_succ, Nat.choose] <;> ring

/-- The same single finite image inherits the exact first eight zero jets. -/
theorem originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight
    (s c : ℝ) {L : ℝ} (hL : 0 < L) {r : ℕ} (hr : r < 8) :
    iteratedDeriv r (originalDetectorPaddedFiniteWindowImage s L c hL) 0 = 0 ∧
      iteratedDeriv r (originalDetectorPaddedFiniteWindowImage s L c hL) L = 0 := by
  have hw : ContDiff ℝ r (originalDetectorPaddedFiniteWindow L) :=
    (originalDetectorPaddedFiniteWindow_contDiff L).of_le (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  have hp : ContDiff ℝ r (originalDetectorPaddedRawFourierPartialJet s L c hL 0) :=
    (originalDetectorPaddedRawFourierPartialSum_contDiff s L c hL).of_le
      (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  have heq : originalDetectorPaddedFiniteWindowImage s L c hL =
      originalDetectorPaddedFiniteWindow L * originalDetectorPaddedRawFourierPartialJet s L c hL 0 := rfl
  rw [heq]
  constructor
  · rw [iteratedDeriv_mul hw.contDiffAt hp.contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≤ r := by simp only [Finset.mem_range] at hi; omega
    rw [(originalDetectorPaddedFiniteWindow_endpoint_jets_lt_eight hL (hir.trans_lt hr)).1]
    simp
  · rw [iteratedDeriv_mul hw.contDiffAt hp.contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≤ r := by simp only [Finset.mem_range] at hi; omega
    rw [(originalDetectorPaddedFiniteWindow_endpoint_jets_lt_eight hL (hir.trans_lt hr)).2]
    simp

/-- Finite-order hard-window gluing from the actual endpoint jets.
The zero-extension derivatives are established before the induction on
regularity, rather than assumed as a formula-level interface. -/
theorem padded_contDiff_nat_indicator_Icc_of_iteratedDeriv_endpoint_zero
    {L : ℝ} (hL : 0 < L) (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ n f)
    (hjets : ∀ r ≤ n, iteratedDeriv r f 0 = 0 ∧ iteratedDeriv r f L = 0) :
    ContDiff ℝ n ((Icc (0 : ℝ) L).indicator f) := by
  induction n generalizing f with
  | zero =>
    change ContDiff ℝ 0 ((Icc (0 : ℝ) L).indicator f)
    rw [contDiff_zero]
    exact continuous_indicator_Icc_of_endpoint_zero hL hf.continuous
      (hjets 0 le_rfl).1 (hjets 0 le_rfl).2
  | succ n ih =>
    have hd : ContDiff ℝ n (deriv f) := hf.deriv'
    have hzero : f 0 = 0 ∧ f L = 0 := hjets 0 (by omega)
    have hone : deriv f 0 = 0 ∧ deriv f L = 0 := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hjets 1 (by omega)
    have hderiv (x : ℝ) : HasDerivAt ((Icc (0 : ℝ) L).indicator f)
        ((Icc (0 : ℝ) L).indicator (deriv f) x) x :=
      hasDerivAt_indicator_Icc_of_endpoint_jets_zero hL
        (fun y => (hf.differentiable (by simp) y).hasDerivAt)
        hzero.1 hzero.2 hone.1 hone.2
    have heq : deriv ((Icc (0 : ℝ) L).indicator f) =
        (Icc (0 : ℝ) L).indicator (deriv f) := deriv_eq hderiv
    change ContDiff ℝ (n + 1) ((Icc (0 : ℝ) L).indicator f)
    refine contDiff_succ_iff_deriv.2 ⟨fun x => (hderiv x).differentiableAt, by simp, ?_⟩
    rw [heq]
    apply ih hd
    intro r hr
    simpa only [← iteratedDeriv_succ'] using hjets (r + 1) (by omega)

/-- The actual finite image is globally `C^n` after hard extension for
every `n≤7`; in particular it meets the genuine `C⁴` pole-killer premise. -/
theorem originalDetectorPaddedFiniteWindowImageCoefficients_hardWindow_contDiff_of_lt_eight
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) {n : ℕ} (hn : n < 8) :
    ContDiff ℝ n (localizedFiniteVector L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFiniteWindowImageCoefficients s L c (by linarith))) := by
  have hLp : 0 < L := by linarith
  rw [localizedFiniteVector_eq_indicator]
  have hfun : localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFiniteWindowImageCoefficients s L c hLp) =
        originalDetectorPaddedFiniteWindowImage s L c hLp := by
    funext x
    exact localizedFiniteFunction_originalDetectorPaddedFiniteWindowImageCoefficients s c hL x
  rw [hfun]
  apply padded_contDiff_nat_indicator_Icc_of_iteratedDeriv_endpoint_zero hLp n
  · exact ((originalDetectorPaddedFiniteWindow_contDiff L).mul
      (originalDetectorPaddedRawFourierPartialSum_contDiff s L c hLp)).of_le
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  · intro r hr
    exact originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight s c hLp (hr.trans_lt hn)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindow_endpoint_jets_lt_eight
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight
#print axioms Zeta23.CCM.padded_contDiff_nat_indicator_Icc_of_iteratedDeriv_endpoint_zero
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImageCoefficients_hardWindow_contDiff_of_lt_eight
