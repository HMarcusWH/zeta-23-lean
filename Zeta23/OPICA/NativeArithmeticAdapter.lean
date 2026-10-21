import Zeta23.OPICA.PrimitiveMasks
import Zeta23.OPICA.DivisorMask
import Zeta23.CCM.OriginalSincDriveLp
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The original integer drive as bounded causal data

The input is the existing literal `nativeOriginalIntegerDrive`. Its continuity,
positive first-prime gap and uniform bound are derived from the original
source. The divisor-controlled low-mask estimate is instantiated with that
actual source and its derived bound, including finite palette compensation.
-/

noncomputable section

open Finset

namespace Zeta23.OPICA

open Zeta23.CCM

theorem native_original_drive_uniform_bound (t : ℝ) :
    |nativeOriginalIntegerDrive t| ≤
      nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale) := by
  have hC := nativeOriginalDriveDecayConstant_pos.le
  have hs := UniversalSinc.fixedScale_pos.le
  by_cases ht : 0 ≤ t
  · have he : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hte : t * Real.exp (-(t / 2)) ≤ 2 := by
      have h := Real.mul_exp_neg_le_exp_neg_one (t / 2)
      have h1 : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith
    have hp : (1 + t + UniversalSinc.fixedScale) * Real.exp (-(t / 2)) ≤
        3 + UniversalSinc.fixedScale := by
      have h := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + UniversalSinc.fixedScale by positivity)
      nlinarith
    exact (nativeOriginalIntegerDrive_decay ht).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hp hC])
  · rw [nativeOriginalIntegerDrive_zero_of_neg (lt_of_not_ge ht), abs_zero]
    positivity

def nativeOriginalBoundedCausalDrive : BoundedCausalDrive where
  toFun := nativeOriginalIntegerDrive
  continuous := nativeOriginalIntegerDrive_continuous
  gap := Real.log 2 - UniversalSinc.fixedScale
  gap_pos := sub_pos.mpr nativeOriginalSource_scale_lt_log_two
  zero_before := fun _ ht => nativeIntegerDriveField_zero_before_firstPrime
    nativeOriginalSource_supported ht
  bound := nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)
  bound_nonneg := mul_nonneg nativeOriginalDriveDecayConstant_pos.le
    (by linarith [UniversalSinc.fixedScale_pos])
  abs_le := native_original_drive_uniform_bound

@[simp] theorem nativeOriginalBoundedCausalDrive_apply (t : ℝ) :
    nativeOriginalBoundedCausalDrive t = nativeOriginalIntegerDrive t := rfl

@[simp] theorem nativeOriginalBoundedCausalDrive_bound :
    nativeOriginalBoundedCausalDrive.bound =
      nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale) := rfl

/-- The literal original drive satisfies the low primitive estimate, with its
source bound derived above rather than supplied as an estimate hypothesis. -/
theorem native_original_drive_low_mask_bound (order : ℕ) (horder : 0 < order)
    (x y : ℕ → ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hBmax : 1 ≤ Bmax) (hT : 0 ≤ T) (hHT : H ≤ T)
    (hx : ∀ d, 0 < d → |x d| ≤ Ax * (divisorCount order d : ℝ))
    (hy : ∀ d, 0 < d → |y d| ≤ Ay * (divisorCount order d : ℝ))
    (B : ℝ → ℝ) (hBm : Measurable B) (hB : ∀ t ∈ Set.Icc H T, B t ≤ Bmax) :
    MeasureTheory.IntegrableOn
      (finiteLowPair nativeOriginalBoundedCausalDrive (driveIndexBound T) x y B)
      (Set.Icc H T) ∧
    |∫ t in Set.Icc H T,
      finiteLowPair nativeOriginalBoundedCausalDrive (driveIndexBound T) x y B t| ≤
      Ax * Ay * (4 * (T - H) *
        (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)) ^ 2 *
        Bmax * (1 + Real.log Bmax) ^ (2 * order - 2) * (1 + T) ^ (order * order)) := by
  constructor
  · exact finiteLowPair_integrableOn nativeOriginalBoundedCausalDrive order horder
      x y Ax Ay Bmax H T hAx hAy hBmax hT hx hy B hBm hB
  · simpa only [nativeOriginalBoundedCausalDrive_bound] using
      low_primitive_bilinear_bound nativeOriginalBoundedCausalDrive order horder
        x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hB

/-- Finite palettes preserve the causal gap; their absolute coefficient cost is explicit. -/
def finitePaletteDrive (U : BoundedCausalDrive) (S : Finset ℕ) (c : ℕ → ℝ)
    (hS : ∀ d ∈ S, 0 < d) : BoundedCausalDrive where
  toFun t := ∑ d ∈ S, c d * U (t - Real.log d)
  continuous := by
    apply continuous_finsetSum
    intro d hd
    exact continuous_const.mul (U.continuous.comp (continuous_id.sub continuous_const))
  gap := U.gap
  gap_pos := U.gap_pos
  zero_before := by
    intro t ht
    apply sum_eq_zero
    intro d hd
    have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hS d hd)
    rw [U.zero_before _ (by linarith), mul_zero]
  bound := (∑ d ∈ S, |c d|) * U.bound
  bound_nonneg := mul_nonneg (sum_nonneg (fun _ _ => abs_nonneg _)) U.bound_nonneg
  abs_le := by
    intro t
    calc
      _ ≤ ∑ d ∈ S, |c d * U (t - Real.log d)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ S, |c d| * U.bound := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (U.abs_le _) (abs_nonneg _)
      _ = _ := (sum_mul _ _ _).symm

/-- A fixed finite palette has the same estimate, with its actual coefficient
cost appearing explicitly in the source factor. -/
theorem native_finite_palette_low_mask_bound (S : Finset ℕ) (c : ℕ → ℝ)
    (hS : ∀ d ∈ S, 0 < d) (order : ℕ) (horder : 0 < order)
    (x y : ℕ → ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hBmax : 1 ≤ Bmax) (hT : 0 ≤ T) (hHT : H ≤ T)
    (hx : ∀ d, 0 < d → |x d| ≤ Ax * (divisorCount order d : ℝ))
    (hy : ∀ d, 0 < d → |y d| ≤ Ay * (divisorCount order d : ℝ))
    (B : ℝ → ℝ) (hBm : Measurable B) (hB : ∀ t ∈ Set.Icc H T, B t ≤ Bmax) :
    MeasureTheory.IntegrableOn
      (finiteLowPair (finitePaletteDrive nativeOriginalBoundedCausalDrive S c hS)
        (driveIndexBound T) x y B) (Set.Icc H T) ∧
    |∫ t in Set.Icc H T,
      finiteLowPair (finitePaletteDrive nativeOriginalBoundedCausalDrive S c hS)
        (driveIndexBound T) x y B t| ≤
      Ax * Ay * (4 * (T - H) *
        ((∑ d ∈ S, |c d|) *
          (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale))) ^ 2 *
        Bmax * (1 + Real.log Bmax) ^ (2 * order - 2) * (1 + T) ^ (order * order)) := by
  constructor
  · exact finiteLowPair_integrableOn _ order horder x y Ax Ay Bmax H T
      hAx hAy hBmax hT hx hy B hBm hB
  · simpa only [finitePaletteDrive, nativeOriginalBoundedCausalDrive_bound] using
      low_primitive_bilinear_bound
        (finitePaletteDrive nativeOriginalBoundedCausalDrive S c hS)
        order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hB

/-- The exact inverse-square-root weight as an arithmetic function. -/
def inverseSqrtArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun d => (Real.sqrt (d : ℝ))⁻¹, by simp⟩

theorem inverseSqrtArithmeticFunction_multiplicative :
    inverseSqrtArithmeticFunction.IsMultiplicative := by
  refine ⟨by norm_num [inverseSqrtArithmeticFunction], ?_⟩
  intro m n _hcoprime
  change (Real.sqrt ((m * n : ℕ) : ℝ))⁻¹ =
    (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
  simp only [mul_inv_rev, mul_comm]

def moebiusPaletteCoefficient (d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) / Real.sqrt (d : ℝ)

/-- The paper's literal finite squarefree-palette cost. -/
def squarefreePaletteCost (Q : ℕ) : ℝ :=
  ∏ p ∈ Q.primeFactors, (1 + (Real.sqrt (p : ℝ))⁻¹)

theorem squarefree_palette_absolute_cost (Q : ℕ) (hQ : Squarefree Q) :
    (∑ d ∈ Q.divisors, |moebiusPaletteCoefficient d|) = squarefreePaletteCost Q := by
  calc
    _ = ∑ d ∈ Q.divisors, (Real.sqrt (d : ℝ))⁻¹ := by
      apply sum_congr rfl
      intro d hd
      have hsq := hQ.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq
      rw [moebiusPaletteCoefficient, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
        hmu, one_div]
    _ = _ := by
      symm
      simpa only [squarefreePaletteCost, inverseSqrtArithmeticFunction,
        ArithmeticFunction.coe_mk] using
        inverseSqrtArithmeticFunction_multiplicative.prodPrimeFactors_one_add_of_squarefree hQ

/-- This is exactly the divisor-indexed Möbius translate source of paper 7.1. -/
def squarefreePaletteDrive (U : BoundedCausalDrive) (Q : ℕ) : BoundedCausalDrive :=
  finitePaletteDrive U Q.divisors moebiusPaletteCoefficient
    (fun _ hd => Nat.pos_of_mem_divisors hd)

@[simp] theorem squarefreePaletteDrive_apply (U : BoundedCausalDrive) (Q : ℕ) (t : ℝ) :
    squarefreePaletteDrive U Q t =
      ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ) / Real.sqrt (d : ℝ) *
        U (t - Real.log d) := rfl

theorem squarefreePaletteDrive_bound (U : BoundedCausalDrive) (Q : ℕ)
    (hQ : Squarefree Q) :
    (squarefreePaletteDrive U Q).bound = squarefreePaletteCost Q * U.bound := by
  change (∑ d ∈ Q.divisors, |moebiusPaletteCoefficient d|) * U.bound = _
  rw [squarefree_palette_absolute_cost Q hQ]

theorem native_squarefree_palette_uniform_bound (Q : ℕ) (hQ : Squarefree Q) (t : ℝ) :
    |squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q t| ≤
      squarefreePaletteCost Q *
        (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)) := by
  simpa only [squarefreePaletteDrive_bound _ Q hQ,
    nativeOriginalBoundedCausalDrive_bound] using
    (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q).abs_le t

/-- The actual Möbius-compensated native source has the paper's `b_Q²` low-mask cost. -/
theorem native_squarefree_palette_low_mask_bound (Q : ℕ) (hQ : Squarefree Q)
    (order : ℕ) (horder : 0 < order)
    (x y : ℕ → ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hBmax : 1 ≤ Bmax) (hT : 0 ≤ T) (hHT : H ≤ T)
    (hx : ∀ d, 0 < d → |x d| ≤ Ax * (divisorCount order d : ℝ))
    (hy : ∀ d, 0 < d → |y d| ≤ Ay * (divisorCount order d : ℝ))
    (B : ℝ → ℝ) (hBm : Measurable B) (hB : ∀ t ∈ Set.Icc H T, B t ≤ Bmax) :
    MeasureTheory.IntegrableOn
      (finiteLowPair (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) x y B) (Set.Icc H T) ∧
    |∫ t in Set.Icc H T,
      finiteLowPair (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) x y B t| ≤
      Ax * Ay * (4 * (T - H) *
        squarefreePaletteCost Q ^ 2 *
        (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)) ^ 2 *
        Bmax * (1 + Real.log Bmax) ^ (2 * order - 2) * (1 + T) ^ (order * order)) := by
  constructor
  · exact finiteLowPair_integrableOn _ order horder x y Ax Ay Bmax H T
      hAx hAy hBmax hT hx hy B hBm hB
  · have h := low_primitive_bilinear_bound
      (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
      order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hB
    rw [squarefreePaletteDrive_bound _ Q hQ, nativeOriginalBoundedCausalDrive_bound,
      mul_pow] at h
    exact h.trans_eq (by ring)

end Zeta23.OPICA
