import Zeta23.CCM.UniversalSincInverseGevreyBounds
import Zeta23.CCM.UniversalSincSourceDensityIdentification
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Original-source prerequisites for the fixed quartic Fourier image

The detector cutoff is the literal specification `ceil(L^4)`; its raw
Fourier degree is exactly `ceil(L^4)-4`, with natural subtraction accounted
for at large aperture. The translated lobe below is the constructed original
infinite-convolution density. Its derivative estimate is transported from
the actual inverse integral, and compact support kills every endpoint jet.

These are prerequisites for the divided-lobe `q / sin^8(πx/L)` construction.
No error estimate or finite-image approximation is assumed here.
-/

noncomputable section

open Set MeasureTheory Complex

namespace Zeta23.CCM

/-- The mandated core detector degree, with natural ceiling. -/
def originalDetectorQuarticCutoff (L : ℝ) : ℕ := Nat.ceil (L ^ 4)

/-- Exactly four Fourier degrees are reserved for `sin^8(πx/L)`. -/
def originalDetectorRawCutoff (L : ℝ) : ℕ := originalDetectorQuarticCutoff L - 4

private theorem sixteen_le_fourth_pow {L : ℝ} (hL : 2 ≤ L) : 16 ≤ L ^ 4 := by
  have hsq : 4 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 2)]
  have hpow : L ^ 4 = (L ^ 2) ^ 2 := by ring
  rw [hpow]
  nlinarith [sq_nonneg (L ^ 2 - 4)]

theorem originalDetectorQuarticCutoff_ge_sixteen {L : ℝ} (hL : 2 ≤ L) :
    16 ≤ originalDetectorQuarticCutoff L := by
  have hc := Nat.le_ceil (L ^ 4)
  have hh : (16 : ℝ) ≤ (Nat.ceil (L ^ 4) : ℝ) :=
    (sixteen_le_fourth_pow hL).trans hc
  change 16 ≤ Nat.ceil (L ^ 4)
  exact_mod_cast hh

theorem originalDetectorRawCutoff_add_four {L : ℝ} (hL : 2 ≤ L) :
    originalDetectorRawCutoff L + 4 = originalDetectorQuarticCutoff L :=
  Nat.sub_add_cancel ((by norm_num : (4 : ℕ) ≤ 16).trans
    (originalDetectorQuarticCutoff_ge_sixteen hL))

theorem originalDetectorRawCutoff_ge_twelve {L : ℝ} (hL : 2 ≤ L) :
    12 ≤ originalDetectorRawCutoff L := by
  have hc := originalDetectorQuarticCutoff_ge_sixteen hL
  have ha := originalDetectorRawCutoff_add_four hL
  omega

/-- The lower real bound retains the four reserved degrees. -/
theorem originalDetectorRawCutoff_lower {L : ℝ} (hL : 2 ≤ L) :
    L ^ 4 - 4 ≤ (originalDetectorRawCutoff L : ℝ) := by
  have hc := Nat.le_ceil (L ^ 4)
  have ha : (originalDetectorRawCutoff L : ℝ) + 4 =
      (originalDetectorQuarticCutoff L : ℝ) := by
    exact_mod_cast originalDetectorRawCutoff_add_four hL
  unfold originalDetectorQuarticCutoff at ha
  linarith

/-- The ceiling is less than one above its argument, so the raw degree is
strictly below `L^4-3`. -/
theorem originalDetectorRawCutoff_upper {L : ℝ} (hL : 2 ≤ L) :
    (originalDetectorRawCutoff L : ℝ) < L ^ 4 - 3 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ L ^ 4 from pow_nonneg (by linarith) _)
  have ha : (originalDetectorRawCutoff L : ℝ) + 4 =
      (originalDetectorQuarticCutoff L : ℝ) := by
    exact_mod_cast originalDetectorRawCutoff_add_four hL
  unfold originalDetectorQuarticCutoff at ha
  linarith

/-- A quantitative frequency-scale bound for the exact prescribed cutoff. -/
theorem originalDetectorRawCutoff_div_lower {L : ℝ} (hL : 2 ≤ L) :
    L ^ 3 / 2 ≤ (originalDetectorRawCutoff L : ℝ) / L := by
  have hp := sixteen_le_fourth_pow hL
  have hc := originalDetectorRawCutoff_lower hL
  apply (le_div_iff₀ (show 0 < L by linarith)).mpr
  nlinarith

theorem originalDetectorRawCutoff_sqrt_lower {L : ℝ} (hL : 2 ≤ L) :
    Real.sqrt (L ^ 3 / 2) ≤ Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L) :=
  Real.sqrt_le_sqrt (originalDetectorRawCutoff_div_lower hL)

/-- One positive detector lobe is a literal translation of the original density. -/
def originalDetectorLobe (s c x : ℝ) : ℂ :=
  UniversalSinc.originalDensityComplex s (x - c)

theorem originalDetectorLobe_contDiff {s : ℝ} (hs : 0 < s) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (originalDetectorLobe s c) := by
  have hq := UniversalSinc.contDiff_inverseCandidate hs
  rw [UniversalSinc.inverseCandidate_eq_originalDensityComplex hs] at hq
  exact hq.comp (contDiff_id.sub contDiff_const)

/-- The quantitative bound concerns the constructed original density, uniformly
over translations and evaluation points. -/
theorem originalDetectorLobe_iteratedDeriv_le_gevrey
    {s : ℝ} (hs : 0 < s) (m : ℕ) (c x : ℝ) :
    ‖iteratedDeriv m (originalDetectorLobe s c) x‖ ≤
      (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) *
        (12 / (UniversalSinc.gevreyMomentScale s) ^ 2) ^ m * (Nat.factorial m : ℝ) ^ 2 := by
  unfold originalDetectorLobe
  rw [iteratedDeriv_comp_sub_const,
    ← UniversalSinc.inverseCandidate_eq_originalDensityComplex hs]
  exact UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_gevrey hs m (x - c)

theorem originalDetectorLobe_support {s : ℝ} (hs : 0 < s) (c : ℝ) :
    tsupport (originalDetectorLobe s c) ⊆ Icc (c - s) (c + s) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  have habs : s < |x - c| := by
    apply lt_of_not_ge
    intro h
    have hh := abs_le.mp h
    exact hnot ⟨by linarith [hh.1], by linarith [hh.2]⟩
  apply hx
  simp only [originalDetectorLobe, UniversalSinc.originalDensityComplex,
    UniversalSinc.originalDensityCandidate_zero_of_abs_gt hs habs, Complex.ofReal_zero]

private theorem tsupport_iteratedDeriv_subset_original (m : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp only [iteratedDeriv_zero]; exact Subset.rfl
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- Unit endpoint collars kill every jet of the actual translated lobe. -/
theorem originalDetectorLobe_endpoint_jets
    {s L c : ℝ} (hs : 0 < s) (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    (m : ℕ) :
    iteratedDeriv m (originalDetectorLobe s c) 0 = 0 ∧
      iteratedDeriv m (originalDetectorLobe s c) L = 0 := by
  have ht := (tsupport_iteratedDeriv_subset_original m (originalDetectorLobe s c)).trans
    (originalDetectorLobe_support hs c)
  constructor
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := (ht h).1
    linarith
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := (ht h).2
    linarith

/-- Exact integration by parts for every original-lobe jet and every nonzero
mode. The seams vanish by the proved unit collars. -/
theorem originalDetectorLobe_fourierCoeff_jet_step
    {s L c : ℝ} (hs : 0 < s) (hL : 0 < L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1) (m : ℕ)
    {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn hL (iteratedDeriv m (originalDetectorLobe s c)) n =
      ((L : ℂ) / (2 * Real.pi * Complex.I * (n : ℂ))) *
        fourierCoeffOn hL (iteratedDeriv (m + 1) (originalDetectorLobe s c)) n := by
  have hsmooth := originalDetectorLobe_contDiff hs c
  have hmOrder : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show ((m + 1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)
  have hd : Differentiable ℝ (iteratedDeriv m (originalDetectorLobe s c)) :=
    (hsmooth.of_le hmOrder).differentiable_iteratedDeriv' m
  have hc : Continuous (iteratedDeriv (m + 1) (originalDetectorLobe s c)) :=
    (hsmooth.of_le hmOrder).continuous_iteratedDeriv' (m + 1)
  have hj := originalDetectorLobe_endpoint_jets hs hleft hright m
  have hraw := fourierCoeffOn_of_hasDerivAt hL hn
    (f := iteratedDeriv m (originalDetectorLobe s c))
    (f' := iteratedDeriv (m + 1) (originalDetectorLobe s c))
    (fun x _ => by rw [iteratedDeriv_succ]; exact (hd x).hasDerivAt)
    (hc.intervalIntegrable 0 L)
  rw [hj.1, hj.2] at hraw
  simp only [Complex.ofReal_zero, sub_zero, sub_self, mul_zero, zero_sub] at hraw
  rw [hraw]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero, hn] <;> ring

/-- Repeated integration by parts uses the actual jets, without an externally
supplied approximation or derivative estimate. -/
theorem originalDetectorLobe_fourierCoeff_eq_jet
    {s L c : ℝ} (hs : 0 < s) (hL : 0 < L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) (m : ℕ) :
    fourierCoeffOn hL (originalDetectorLobe s c) n =
      ((L : ℂ) / (2 * Real.pi * Complex.I * (n : ℂ))) ^ m *
        fourierCoeffOn hL (iteratedDeriv m (originalDetectorLobe s c)) n := by
  induction m with
  | zero => simp only [pow_zero, one_mul, iteratedDeriv_zero]
  | succ m ih =>
    rw [ih, originalDetectorLobe_fourierCoeff_jet_step hs hL hleft hright m hn,
      pow_succ]
    ring

/-- The derivative budget is fixed by the actual source scale. -/
def originalDetectorLobeJetBudget (s : ℝ) (m : ℕ) : ℝ :=
  (4 / (Real.pi * (UniversalSinc.gevreyMomentScale s) ^ 2)) *
    (12 / (UniversalSinc.gevreyMomentScale s) ^ 2) ^ m * (Nat.factorial m : ℝ) ^ 2

/-- The normalized coefficient of each actual jet is bounded by its proved
uniform derivative budget. -/
theorem norm_originalDetectorLobe_jet_fourierCoeff_le
    {s L : ℝ} (hs : 0 < s) (hL : 0 < L) (c : ℝ) (m : ℕ) (n : ℤ) :
    ‖fourierCoeffOn hL (iteratedDeriv m (originalDetectorLobe s c)) n‖ ≤
      originalDetectorLobeJetBudget s m := by
  letI : Fact (0 < L - 0) := ⟨by simpa only [sub_zero] using hL⟩
  have hi : ‖∫ x : ℝ in (0 : ℝ)..L,
      fourier (-n) (x : AddCircle (L - 0)) •
        iteratedDeriv m (originalDetectorLobe s c) x‖ ≤
      originalDetectorLobeJetBudget s m * L := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := L) (C := originalDetectorLobeJetBudget s m)
      (f := fun x : ℝ =>
        fourier (-n) (x : AddCircle (L - 0)) • iteratedDeriv m (originalDetectorLobe s c) x)
      (fun x _ => by
        rw [norm_smul,
          show ‖fourier (-n) (x : AddCircle (L - 0))‖ = 1 from Circle.norm_coe _,
          one_mul]
        exact originalDetectorLobe_iteratedDeriv_le_gevrey hs m c x)
    simpa only [sub_zero, abs_of_pos hL] using hraw
  rw [fourierCoeffOn_eq_integral]
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (show 0 < L - 0 by simpa only [sub_zero] using hL))]
  calc
    _ ≤ (1 / (L - 0)) * (originalDetectorLobeJetBudget s m * L) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = originalDetectorLobeJetBudget s m * (L / L) := by rw [sub_zero]; ring
    _ = originalDetectorLobeJetBudget s m := by rw [div_self hL.ne', mul_one]

/-- Quantitative coefficient decay for the actual compact source. This is
valid at every derivative order; optimizing the order and treating the
`sin^8` divisor are separate next steps. -/
theorem norm_originalDetectorLobe_fourierCoeff_le_gevrey_order
    {s L c : ℝ} (hs : 0 < s) (hL : 0 < L)
    (hleft : 1 + s ≤ c) (hright : c + s ≤ L - 1)
    {n : ℤ} (hn : n ≠ 0) (m : ℕ) :
    ‖fourierCoeffOn hL (originalDetectorLobe s c) n‖ ≤
      (L / (2 * Real.pi * |(n : ℝ)|)) ^ m * originalDetectorLobeJetBudget s m := by
  have hfreq : ‖(L : ℂ) / (2 * Real.pi * Complex.I * (n : ℂ))‖ =
      L / (2 * Real.pi * |(n : ℝ)|) := by
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hL, abs_of_pos Real.pi_pos, Complex.norm_I,
      Complex.norm_two, Complex.norm_intCast, mul_one]
  rw [originalDetectorLobe_fourierCoeff_eq_jet hs hL hleft hright hn m,
    norm_mul, norm_pow, hfreq]
  exact mul_le_mul_of_nonneg_left
    (norm_originalDetectorLobe_jet_fourierCoeff_le hs hL c m n) (by positivity)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorRawCutoff_add_four
#print axioms Zeta23.CCM.originalDetectorRawCutoff_lower
#print axioms Zeta23.CCM.originalDetectorRawCutoff_upper
#print axioms Zeta23.CCM.originalDetectorRawCutoff_div_lower
#print axioms Zeta23.CCM.originalDetectorLobe_iteratedDeriv_le_gevrey
#print axioms Zeta23.CCM.originalDetectorLobe_endpoint_jets
#print axioms Zeta23.CCM.originalDetectorLobe_fourierCoeff_jet_step
#print axioms Zeta23.CCM.originalDetectorLobe_fourierCoeff_eq_jet
#print axioms Zeta23.CCM.norm_originalDetectorLobe_jet_fourierCoeff_le
#print axioms Zeta23.CCM.norm_originalDetectorLobe_fourierCoeff_le_gevrey_order
