import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Literal primitive masks and local finiteness

The low mask includes equality. The high mask is its strict complement.
The drive carries a genuine positive causal gap and a global bound. These
are source hypotheses, not assumptions of the low-mask estimate.
-/

noncomputable section

open Finset Set MeasureTheory
open scoped BigOperators

namespace Zeta23.OPICA

structure BoundedCausalDrive where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  gap : ℝ
  gap_pos : 0 < gap
  zero_before : ∀ t, t < gap → toFun t = 0
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  abs_le : ∀ t, |toFun t| ≤ bound

instance : CoeFun BoundedCausalDrive (fun _ => ℝ → ℝ) := ⟨BoundedCausalDrive.toFun⟩

/-- The literal gcd-reduced cutoff, with positive indices enforced at use sites. -/
def primitiveRatio (d e : ℕ) : ℝ := (max d e : ℕ) / (Nat.gcd d e : ℝ)

def lowPrimitiveMask (B : ℝ) (d e : ℕ) : ℝ := if primitiveRatio d e ≤ B then 1 else 0

def highPrimitiveMask (B : ℝ) (d e : ℕ) : ℝ := if B < primitiveRatio d e then 1 else 0

theorem primitiveMask_add_high (B : ℝ) (d e : ℕ) :
    lowPrimitiveMask B d e + highPrimitiveMask B d e = 1 := by
  unfold lowPrimitiveMask highPrimitiveMask
  by_cases h : primitiveRatio d e ≤ B
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

theorem primitiveRatio_self {d : ℕ} (hd : 0 < d) : primitiveRatio d d = 1 := by
  simp [primitiveRatio, Nat.ne_of_gt hd]

theorem lowPrimitiveMask_diagonal {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    lowPrimitiveMask B d d = 1 := by
  simp [lowPrimitiveMask, primitiveRatio_self hd, hB]

theorem lowPrimitiveMask_measurable {B : ℝ → ℝ} (hB : Measurable B) (d e : ℕ) :
    Measurable (fun t => lowPrimitiveMask (B t) d e) := by
  exact Measurable.ite (measurableSet_le measurable_const hB) measurable_const measurable_const

def translatedDrive (U : BoundedCausalDrive) (d : ℕ) (t : ℝ) : ℝ :=
  U (t - Real.log d) / Real.sqrt d

def driveIndexBound (T : ℝ) : ℕ := ⌈Real.exp T⌉₊

theorem translatedDrive_zero_of_index_gt (U : BoundedCausalDrive) {T t : ℝ}
    (ht : t ≤ T) {d : ℕ} (hd : driveIndexBound T < d) : translatedDrive U d t = 0 := by
  have hcast : Real.exp T < (d : ℝ) :=
    (Nat.le_ceil (Real.exp T)).trans_lt (by exact_mod_cast hd)
  have hdpos : (0 : ℝ) < d := (Real.exp_pos T).trans hcast
  have hlog : T < Real.log d := (Real.lt_log_iff_exp_lt hdpos).mpr hcast
  unfold translatedDrive
  rw [U.zero_before _ (by linarith [U.gap_pos]), zero_div]

theorem translatedDrive_zero_index (U : BoundedCausalDrive) (t : ℝ) :
    translatedDrive U 0 t = 0 := by
  simp [translatedDrive]

/-- One horizon bound works for every time in the interval, before any integration. -/
theorem drive_sum_eq_finite (U : BoundedCausalDrive) (x : ℕ → ℝ) {T t : ℝ}
    (ht : t ≤ T) :
    (∑' d : ℕ, x d * translatedDrive U d t) =
      ∑ d ∈ range (driveIndexBound T + 1), x d * translatedDrive U d t := by
  apply tsum_eq_sum
  intro d hd
  rw [translatedDrive_zero_of_index_gt U ht (by simpa using hd), mul_zero]

def finiteDriveField (U : BoundedCausalDrive) (N : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ range (N + 1), x d * translatedDrive U d t

def finiteLowPair (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ → ℝ)
    (B : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ range (N + 1), ∑ e ∈ range (N + 1),
    lowPrimitiveMask (B t) d e * (x d * translatedDrive U d t) *
      (y e * translatedDrive U e t)

def finiteHighPair (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ → ℝ)
    (B : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ range (N + 1), ∑ e ∈ range (N + 1),
    highPrimitiveMask (B t) d e * (x d * translatedDrive U d t) *
      (y e * translatedDrive U e t)

theorem finite_pair_partition (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ → ℝ)
    (B : ℝ → ℝ) (t : ℝ) :
    finiteLowPair U N x y B t + finiteHighPair U N x y B t =
      finiteDriveField U N x t * finiteDriveField U N y t := by
  unfold finiteLowPair finiteHighPair finiteDriveField
  rw [← sum_add_distrib, sum_mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  have h := primitiveMask_add_high (B t) d e
  calc
    _ = (lowPrimitiveMask (B t) d e + highPrimitiveMask (B t) d e) *
        (x d * translatedDrive U d t) * (y e * translatedDrive U e t) := by ring
    _ = _ := by rw [h, one_mul]

/-- Integrable pairings obey the exact literal low/high split. -/
theorem integral_pair_partition (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ → ℝ)
    (B : ℝ → ℝ) (I : Set ℝ)
    (hlow : IntegrableOn (finiteLowPair U N x y B) I)
    (hhigh : IntegrableOn (finiteHighPair U N x y B) I) :
    (∫ t in I, finiteHighPair U N x y B t) =
      (∫ t in I, finiteDriveField U N x t * finiteDriveField U N y t) -
      ∫ t in I, finiteLowPair U N x y B t := by
  have h : (fun t => finiteDriveField U N x t * finiteDriveField U N y t) =
      fun t => finiteLowPair U N x y B t + finiteHighPair U N x y B t := by
    funext t
    exact (finite_pair_partition U N x y B t).symm
  rw [h, integral_add hlow hhigh]
  ring

/-- The actual locally finite translate fields obey the integral partition on
one common finite horizon. Zero-index terms vanish by their literal weight. -/
theorem primitive_mask_partition (U : BoundedCausalDrive) (x y : ℕ → ℝ)
    (B : ℝ → ℝ) (H T : ℝ)
    (hlow : IntegrableOn (finiteLowPair U (driveIndexBound T) x y B) (Icc H T))
    (hhigh : IntegrableOn (finiteHighPair U (driveIndexBound T) x y B) (Icc H T)) :
    (∫ t in Icc H T, finiteHighPair U (driveIndexBound T) x y B t) =
      (∫ t in Icc H T, (∑' d : ℕ, x d * translatedDrive U d t) *
        (∑' e : ℕ, y e * translatedDrive U e t)) -
      ∫ t in Icc H T, finiteLowPair U (driveIndexBound T) x y B t := by
  rw [integral_pair_partition U (driveIndexBound T) x y B (Icc H T) hlow hhigh]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [drive_sum_eq_finite U x ht.2, drive_sum_eq_finite U y ht.2]
  rfl

end Zeta23.OPICA
