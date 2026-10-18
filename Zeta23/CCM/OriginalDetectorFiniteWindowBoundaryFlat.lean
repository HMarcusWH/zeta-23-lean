import Zeta23.CCM.OriginalDetectorFiniteWindowImageJets

/-!
# Exact hard-window legality of the original finite image

The literal sine window kills the endpoint jets. Consequently its actual
centered Fourier coordinates satisfy the boundary-flat moment equations,
and their hard zero extension is globally `C²`.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

/-- The literal multiplier kills the first three jets at both seams. -/
theorem originalDetectorFiniteWindow_endpoint_jets
    {L : ℝ} (hL : 0 < L) {r : ℕ} (hr : r ≤ 2) :
    iteratedDeriv r (originalDetectorFiniteWindow L) 0 = 0 ∧
      iteratedDeriv r (originalDetectorFiniteWindow L) L = 0 := by
  rw [originalDetectorFiniteWindow_iteratedDeriv hL]
  constructor <;> interval_cases r <;>
    simp only [originalDetectorFiniteWindowJet, originalDetectorFiniteWindowCoeff,
      originalDetectorFourierFrequency, AddCircle.coe_zero, AddCircle.coe_period,
      fourier_eval_zero, mul_one] <;>
    norm_num [Finset.sum_range_succ, Nat.choose] <;> ring

/-- The single actual finite image has the required endpoint jets;
these are derived from its window, not assumed as coefficient constraints. -/
theorem originalDetectorFiniteWindowImage_endpoint_jets
    (s c : ℝ) {L : ℝ} (hL : 0 < L) {r : ℕ} (hr : r ≤ 2) :
    iteratedDeriv r (originalDetectorFiniteWindowImage s L c hL) 0 = 0 ∧
      iteratedDeriv r (originalDetectorFiniteWindowImage s L c hL) L = 0 := by
  have hw : ContDiff ℝ r (originalDetectorFiniteWindow L) :=
    (originalDetectorFiniteWindow_contDiff L).of_le (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  have hp : ContDiff ℝ r (originalDetectorDividedLobeFourierPartialJet s L c hL 0) :=
    (originalDetectorDividedLobeFourierPartialSum_contDiff s L c hL).of_le
      (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  have heq : originalDetectorFiniteWindowImage s L c hL =
      originalDetectorFiniteWindow L * originalDetectorDividedLobeFourierPartialJet s L c hL 0 := rfl
  rw [heq]
  constructor
  · rw [iteratedDeriv_mul hw.contDiffAt hp.contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≤ r := by simp only [Finset.mem_range] at hi; omega
    rw [(originalDetectorFiniteWindow_endpoint_jets hL (hir.trans hr)).1]
    simp
  · rw [iteratedDeriv_mul hw.contDiffAt hp.contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≤ r := by simp only [Finset.mem_range] at hi; omega
    rw [(originalDetectorFiniteWindow_endpoint_jets hL (hir.trans hr)).2]
    simp

/-- Reverse direction of the finite moment/endpoint bridge. -/
theorem boundaryFlatCoefficients_of_left_endpoint_jets
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (h0 : localizedFiniteFunction L N u 0 = 0)
    (h1 : localizedFiniteFirstJet L N u 0 = 0)
    (h2 : localizedFiniteSecondJet L N u 0 = 0) :
    BoundaryFlatCoefficients N u := by
  let a : ℂ := ((1 / Real.sqrt L : ℝ) : ℂ)
  let b : ℂ := localizedBaseFrequency L
  have ha : a ≠ 0 := by
    dsimp [a]
    exact Complex.ofReal_ne_zero.mpr (one_div_ne_zero (Real.sqrt_ne_zero'.mpr hL))
  have hb : b ≠ 0 := by
    dsimp [b, localizedBaseFrequency]
    apply mul_ne_zero Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL.ne')
  have hm0 : a * centeredMoment N 0 u = localizedFiniteFunction L N u 0 := by
    simp only [centeredMoment, pow_zero, one_mul, localizedFiniteFunction, localizedMode_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a]
    ring
  have hm1 : (b * a) * centeredMoment N 1 u = localizedFiniteFirstJet L N u 0 := by
    simp only [centeredMoment, pow_one, localizedFiniteFirstJet, localizedMode_zero,
      localizedFrequency]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a, b]
    ring
  have hm2 : (b ^ 2 * a) * centeredMoment N 2 u = localizedFiniteSecondJet L N u 0 := by
    simp only [centeredMoment, localizedFiniteSecondJet, localizedMode_zero, localizedFrequency]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a, b]
    ring
  exact ⟨(mul_eq_zero.mp (hm0.trans h0)).resolve_left ha,
    (mul_eq_zero.mp (hm1.trans h1)).resolve_left (mul_ne_zero hb ha),
    (mul_eq_zero.mp (hm2.trans h2)).resolve_left (mul_ne_zero (pow_ne_zero 2 hb) ha)⟩

/-- The actual output vector satisfies the exact finite boundary-flat
moment equations, without a subsequent projection. -/
theorem originalDetectorFiniteWindowImageCoefficients_boundaryFlat
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    BoundaryFlatCoefficients (originalDetectorQuarticCutoff L)
      (originalDetectorFiniteWindowImageCoefficients s L c (by linarith)) := by
  have hLp : 0 < L := by linarith
  let N := originalDetectorQuarticCutoff L
  let u := originalDetectorFiniteWindowImageCoefficients s L c hLp
  have hfun : localizedFiniteFunction L N u = originalDetectorFiniteWindowImage s L c hLp := by
    funext x
    exact localizedFiniteFunction_originalDetectorFiniteWindowImageCoefficients s c hL x
  have hfirst : localizedFiniteFirstJet L N u = deriv (originalDetectorFiniteWindowImage s L c hLp) := by
    rw [← hfun]
    funext x
    exact (hasDerivAt_localizedFiniteFunction L N u x).deriv.symm
  have hsecond : localizedFiniteSecondJet L N u =
      deriv (deriv (originalDetectorFiniteWindowImage s L c hLp)) := by
    rw [← hfirst]
    funext x
    exact (hasDerivAt_localizedFiniteFirstJet L N u x).deriv.symm
  apply boundaryFlatCoefficients_of_left_endpoint_jets hLp
  · rw [hfun]
    exact (originalDetectorFiniteWindowImage_endpoint_jets s c hLp (r := 0) (by norm_num)).1
  · rw [hfirst]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (originalDetectorFiniteWindowImage_endpoint_jets s c hLp (r := 1) (by norm_num)).1
  · rw [hsecond]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (originalDetectorFiniteWindowImage_endpoint_jets s c hLp (r := 2) (by norm_num)).1

/-- The actual hard-windowed finite image is a globally legal compact
`C²` test in the existing localized finite space. -/
theorem originalDetectorFiniteWindowImageCoefficients_hardWindow_contDiff
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ContDiff ℝ 2 (localizedFiniteVector L (originalDetectorQuarticCutoff L)
      (originalDetectorFiniteWindowImageCoefficients s L c (by linarith))) :=
  contDiff_localizedFiniteVector_of_boundaryFlat _ _ (by linarith)
    (originalDetectorFiniteWindowImageCoefficients_boundaryFlat s c hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFiniteWindow_endpoint_jets
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImage_endpoint_jets
#print axioms Zeta23.CCM.boundaryFlatCoefficients_of_left_endpoint_jets
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImageCoefficients_boundaryFlat
#print axioms Zeta23.CCM.originalDetectorFiniteWindowImageCoefficients_hardWindow_contDiff
