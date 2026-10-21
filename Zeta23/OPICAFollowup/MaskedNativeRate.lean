import Zeta23.OPICAFollowup.LogSlackBalance
import Zeta23.OPICAFollowup.NormFirstTransfer
import Zeta23.OPICA.DivisorMask

/-!
Native mask supporting continuation. The actual finite mask bounds and exact
regrouping are supporting lemmas. Neither of this module's full primary roots
is claimed: the scheduled logarithmic-budget and L2/rate consumers remain
unfinished. In particular there is no Theta hypothesis here. Convolution
powers are explicitly typed as arithmetic functions before coercing to fields.
-/

set_option maxHeartbeats 800000

noncomputable section
open Finset Set MeasureTheory Filter
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA Zeta23.CCM

/-- Actual global bound, including the negative half-line via the positive
native causal gap. This is selected from the proved source theorem. -/
theorem forwardKernel_actual_bounded (d ell : ℕ) (hd : ell ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, |forwardKernel d ell t| ≤ A := by
  obtain ⟨A,c,hA,hc,hdecay⟩ := forwardKernel_double_exp_decay d ell 0 hd
  refine ⟨A,hA,fun t => ?_⟩
  by_cases ht : 0 ≤ t
  · have he : Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hc.le) (Real.exp_nonneg _))
    calc
      _ ≤ A*Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) := by
        simpa only [iteratedDeriv_zero] using hdecay t ht
      _ ≤ A := mul_le_of_le_one_right hA.le he
  · rw [forwardKernel_zero_before d ell (by linarith [nativeCausalGap_pos]),abs_zero]
    exact hA.le

def nativeForwardBoundedDrive (d ell : ℕ) (hd : ell ≤ d) : BoundedCausalDrive where
  toFun := forwardKernel d ell
  continuous := (forwardKernel_contDiff d ell).continuous
  gap := nativeCausalGap
  gap_pos := nativeCausalGap_pos
  zero_before := fun _ ht => forwardKernel_zero_before d ell ht
  bound := Classical.choose (forwardKernel_actual_bounded d ell hd)
  bound_nonneg := (Classical.choose_spec (forwardKernel_actual_bounded d ell hd)).1.le
  abs_le := (Classical.choose_spec (forwardKernel_actual_bounded d ell hd)).2

@[simp] theorem nativeForwardBoundedDrive_apply (d ell : ℕ) (hd : ell ≤ d) (t : ℝ) :
    nativeForwardBoundedDrive d ell hd t = forwardKernel d ell t := rfl

/-- Each iteration retains the actual divisor palette, including its complete
absolute mass. The index j will be 1 on the raw side and r on the absorbed side. -/
def nativePaletteDriveIterate (U : BoundedCausalDrive) (Q : ℕ) : ℕ → BoundedCausalDrive
  | 0 => U
  | j+1 => squarefreePaletteDrive (nativePaletteDriveIterate U Q j) Q

theorem nativePaletteDriveIterate_apply (U : BoundedCausalDrive) (Q j : ℕ) (t : ℝ) :
    nativePaletteDriveIterate U Q j t =
      finiteLogTranslateIterate Q.divisors moebiusPaletteCoefficient j U t := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    change (∑ n ∈ Q.divisors, moebiusPaletteCoefficient n*
      nativePaletteDriveIterate U Q j (t-Real.log n)) = _
    simp_rw [ih]
    rfl

theorem nativePaletteDriveIterate_bound (U : BoundedCausalDrive) (Q j : ℕ) :
    (nativePaletteDriveIterate U Q j).bound ≤ (Q:ℝ)^j * U.bound := by
  induction j with
  | zero => simp [nativePaletteDriveIterate]
  | succ j ih =>
    change (∑ n ∈ Q.divisors, |moebiusPaletteCoefficient n|) *
      (nativePaletteDriveIterate U Q j).bound ≤ (Q:ℝ)^(j+1)*U.bound
    calc
      _ ≤ (Q:ℝ)*((Q:ℝ)^j*U.bound) := mul_le_mul
        (palette_absolute_mass_le Q) ih
        (nativePaletteDriveIterate U Q j).bound_nonneg (Nat.cast_nonneg Q)
      _ = _ := by rw [pow_succ]; ring

def nativeRawPaletteDrive (d Q : ℕ) : BoundedCausalDrive :=
  nativePaletteDriveIterate (nativeForwardBoundedDrive d 0 (Nat.zero_le d)) Q 1

def nativeAbsorbedPaletteDrive (d r Q : ℕ) (hd : r-1 ≤ d) : BoundedCausalDrive :=
  nativePaletteDriveIterate (nativeForwardBoundedDrive d (r-1) hd) Q r

theorem nativeRawPaletteDrive_apply (d Q : ℕ) (hQ : 0 < Q) (t : ℝ) :
    nativeRawPaletteDrive d Q t = nativePaletteDrive d Q t := by
  rw [nativeRawPaletteDrive,nativePaletteDriveIterate_apply]
  rw [nativePaletteDrive,arithmeticHistoryAction_palette_finite Q hQ]
  rfl

theorem nativeAbsorbedPaletteDrive_apply (d r Q : ℕ) (hr : 1 ≤ r)
    (hd : r-1 ≤ d) (hQ : 0 < Q) (t : ℝ) :
    nativeAbsorbedPaletteDrive d r Q hd t = paletteForwardKernel d (r-1) Q t := by
  rw [nativeAbsorbedPaletteDrive,nativePaletteDriveIterate_apply,paletteForwardKernel,
    arithmeticHistoryAction_palette_power_iterate Q hQ
      (fun u hu => forwardKernel_zero_before d (r-1) hu),
    show r-1+1=r by omega]
  rfl

/-- Absorbed coefficients have their own actual r-fold divisor envelope.
This uses the public tuple identity, not inaccessible private helpers. -/
theorem nativeLargeCoefficients_power_abs_le_divisor (Q r n : ℕ) (Y : ℝ) :
    |((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) n| ≤ (divisorCount r n : ℝ) := by
  have habs (j : ℕ) : |nativeLargeCoefficients Q Y j| ≤ 1 := by
    change |if Y < (j:ℝ) then nativeInverseCoefficients Q j else 0| ≤ 1
    split_ifs with hj
    · change |if Nat.Coprime j Q then (ArithmeticFunction.moebius j:ℝ) else 0| ≤ 1
      split_ifs <;> try norm_num
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j)
    · norm_num
  rw [dirichlet_power_tuple_expansion]
  calc
    _ ≤ ∑ w ∈ Nat.finMulAntidiag r n, |∏ i, nativeLargeCoefficients Q Y (w i)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ Nat.finMulAntidiag r n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro w _
      rw [Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun i _ => abs_nonneg _)
        (fun i _ => habs (w i))
    _ = _ := by simp [divisorCount]

/-- The finite observation is precisely the native arithmetic history on the
whole horizon, including index zero and the real log delays. -/
theorem arithmeticHistoryAction_eq_finiteDrive (a : ArithmeticFunction ℝ)
    (U : BoundedCausalDrive) {T t : ℝ} (ht : t ≤ T) :
    arithmeticHistoryAction a U t = finiteDriveField U (driveIndexBound T) a t := by
  have he : arithmeticHistoryAction a U t = ∑' n : ℕ, a n*translatedDrive U n t := by
    apply tsum_congr
    intro n
    dsimp [translatedDrive]
    ring
  rw [he,drive_sum_eq_finite U a ht]
  rfl

theorem native_balanced_two_realizations (r d Q : ℕ) (hr : 2 ≤ r)
    (hd : r-1 ≤ d) (hQ : 0 < Q) (Y : ℝ) {T t : ℝ} (ht : t ≤ T) :
    finiteDriveField (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) t = balancedField d r Q Y t ∧
    finiteDriveField (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) t = balancedField d r Q Y t := by
  constructor
  · rw [←arithmeticHistoryAction_eq_finiteDrive _ _ ht]
    change arithmeticHistoryAction (balancedInverseCoefficients Q Y r)
      (fun u => nativeRawPaletteDrive d Q u) t = _
    simp_rw [nativeRawPaletteDrive_apply d Q hQ]
    rfl
  · rw [←arithmeticHistoryAction_eq_finiteDrive _ _ ht,
      balancedField_absorbed d r Q Y t]
    congr 1
    funext u
    exact nativeAbsorbedPaletteDrive_apply d r Q (by omega) hd hQ u

def nativeMovingPrimitiveCutoff (t : ℝ) : ℝ := Real.exp (Real.sqrt t)

theorem nativeMovingPrimitiveCutoff_measurable : Measurable nativeMovingPrimitiveCutoff := by
  unfold nativeMovingPrimitiveCutoff
  fun_prop

theorem nativeMovingPrimitiveCutoff_le {t T : ℝ} (ht : t ≤ T) :
    nativeMovingPrimitiveCutoff t ≤ Real.exp (Real.sqrt T) :=
  Real.exp_le_exp.mpr (Real.sqrt_le_sqrt ht)

/-- Two source-specific low-form inequalities, derived separately. They retain
all real cutoffs, actual gcd masks (including the diagonal), and full palette
mass. No equality between the two low masks is asserted. -/
theorem native_balanced_low_masks_explicit (r d Q : ℕ) (hr : 2 ≤ r)
    (hd : r-1 ≤ d) (Y H T : ℝ) (hY : 1 ≤ Y) (hT : 0 ≤ T) (hHT : H ≤ T) :
    (IntegrableOn (finiteLowPair (nativeRawPaletteDrive d Q) (driveIndexBound T)
      (balancedInverseCoefficients Q Y r) (balancedInverseCoefficients Q Y r)
      nativeMovingPrimitiveCutoff) (Icc H T) ∧
     |lowPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
       (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T)| ≤
       4*(T-H)*((Q:ℝ)*(nativeForwardBoundedDrive d 0 (Nat.zero_le d)).bound)^2 *
       Real.exp (Real.sqrt T)*(1+Real.sqrt T)^(2*(2*r-1)-2)*(1+T)^((2*r-1)*(2*r-1))) ∧
    (IntegrableOn (finiteLowPair (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
      ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ))
      nativeMovingPrimitiveCutoff) (Icc H T) ∧
     |lowPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
       ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T)| ≤
       4*(T-H)*((Q:ℝ)^r*(nativeForwardBoundedDrive d (r-1) hd).bound)^2 *
       Real.exp (Real.sqrt T)*(1+Real.sqrt T)^(2*r-2)*(1+T)^(r*r)) := by
  have hB : 1 ≤ Real.exp (Real.sqrt T) := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg T)
  have hmask : ∀ t ∈ Icc H T, nativeMovingPrimitiveCutoff t ≤ Real.exp (Real.sqrt T) :=
    fun t ht => nativeMovingPrimitiveCutoff_le ht.2
  have hx (n : ℕ) (_hn : 0 < n) :
      |balancedInverseCoefficients Q Y r n| ≤ 1*(divisorCount (2*r-1) n : ℝ) := by
    simpa only [one_mul] using (balanced_coeff_divisor_bound Q Y hY r hr n).1
  have hy (n : ℕ) (_hn : 0 < n) :
      |((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) n| ≤ 1*(divisorCount r n : ℝ) := by
    simpa only [one_mul] using nativeLargeCoefficients_power_abs_le_divisor Q r n Y
  have hU := nativePaletteDriveIterate_bound (nativeForwardBoundedDrive d 0 (Nat.zero_le d)) Q 1
  have hV := nativePaletteDriveIterate_bound (nativeForwardBoundedDrive d (r-1) hd) Q r
  simp only [pow_one] at hU
  constructor
  · constructor
    · exact finiteLowPair_integrableOn _ (2*r-1) (by omega) _ _ 1 1 _ H T
        (by norm_num) (by norm_num) hB hT hx hx _ nativeMovingPrimitiveCutoff_measurable hmask
    · have h := low_primitive_bilinear_bound (nativeRawPaletteDrive d Q)
        (2*r-1) (by omega) _ _ 1 1 _ H T (by norm_num) (by norm_num)
        hB hT hHT hx hx _ hmask
      simp only [one_mul,Real.log_exp] at h
      apply h.trans
      gcongr
      · exact (nativeRawPaletteDrive d Q).bound_nonneg
      · exact hU
  · constructor
    · exact finiteLowPair_integrableOn _ r (by omega) _ _ 1 1 _ H T
        (by norm_num) (by norm_num) hB hT hy hy _ nativeMovingPrimitiveCutoff_measurable hmask
    · have h := low_primitive_bilinear_bound (nativeAbsorbedPaletteDrive d r Q hd)
        r (by omega) _ _ 1 1 _ H T (by norm_num) (by norm_num)
        hB hT hHT hy hy _ hmask
      simp only [one_mul,Real.log_exp] at h
      apply h.trans
      gcongr
      · exact (nativeAbsorbedPaletteDrive d r Q hd).bound_nonneg
      · exact hV

/-- Exact error allocation between the two different high masks. The premise
identifying their scalar fields is discharged from the actual native actions. -/
theorem native_balanced_mask_regrouping (r d Q : ℕ) (hr : 2 ≤ r)
    (hd : r-1 ≤ d) (hQ : 0 < Q) (Y H T : ℝ)
    (hY : 1 ≤ Y) (hT : 0 ≤ T) (hHT : H ≤ T) :
    highPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T) -
      highPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T) =
    lowPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T) -
      lowPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T) := by
  obtain ⟨⟨hUL,_⟩,⟨hVL,_⟩⟩ := native_balanced_low_masks_explicit r d Q hr hd Y H T hY hT hHT
  apply mask_regrouping_difference _ _ _ _ _ _ _ _ _ measurableSet_Icc ?_
    hUL (finiteHighPair_integrableOn _ _ _ _ _ H T hUL)
    hVL (finiteHighPair_integrableOn _ _ _ _ _ H T hVL)
  intro t ht
  obtain ⟨hU,hV⟩ := native_balanced_two_realizations r d Q hr hd hQ Y ht.2
  exact hU.trans hV.symm

end Zeta23.OPICAFollowup
