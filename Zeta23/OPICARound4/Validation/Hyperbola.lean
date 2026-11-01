import Zeta23.OPICARound4.ActualSourceHyperbola
import Zeta23.OPICARound4.HyperbolaDiagonal

/-! Independent complete-type consumers. These validate the exact source and
signed decomposition; none supplies the eventual arithmetic inequality. -/

noncomputable section
open Finset

namespace Zeta23.OPICARound4

theorem validation_madness_actual_hyperbola (t : ℝ) :
    actualCorrelationPrimeField t =
      2 * hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) -
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) :=
  actualCorrelationPrimeField_hyperbola_half t

theorem validation_madness_actual_drive (t : ℝ) (a : ℕ) (ha : 0 < a) :
    actualCorrelationLogarithmicTest t a =
      actualCorrelationIntegerDrive (t - Real.log a) / Real.sqrt a :=
  actualCorrelationLogarithmicTest_eq_integerDrive t a ha

theorem validation_madness_actual_normalization (t : ℝ) (a : ℕ) (ha : 0 < a) :
    Real.sqrt (Real.exp t) * actualCorrelationLogarithmicTest t a =
      actualFlatMobiusTest ((a : ℝ) / Real.exp t) :=
  actualFlatMobiusTest_normalization t a ha

theorem validation_madness_drive_rapid_decay (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |actualCorrelationIntegerDrive t| ≤ C * Real.exp (-A * t) :=
  actualCorrelationIntegerDrive_rapid_bound A hA

theorem validation_madness_short_term_rapid_decay (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |hyperbolaE (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)| ≤
        C * Real.exp (-A * t) :=
  actualCorrelationShortTerm_rapid_bound A hA

theorem validation_madness_observable_remainder (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |actualCorrelationPrimeField t +
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)| ≤
        C * Real.exp (-A * t) :=
  actualCorrelationPrimeField_add_longTerm_rapid_bound A hA

theorem validation_madness_complete_split (P R : ℝ → ℝ) (I x : ℝ) (Y : ℕ)
    (hP : ∀ y : ℝ, P y = I * y + R y) :
    mobiusPoissonQuadratic P x Y =
      (mobiusPoissonRankOne I x Y + mobiusPoissonOffDiagonal R x Y) +
        aliasDiagonal R x Y :=
  mobiusPoissonQuadratic_eq_rankOne_offDiagonal_add_diagonal P R I x Y hP

theorem validation_madness_diagonal_budget (R : ℝ → ℝ) {T x M : ℝ}
    (hT : 0 < T) (hx : 0 < x) (hM : 0 ≤ M)
    (hR : ∀ y : ℝ, 1 / T ≤ y → |R y| ≤ M) :
    |aliasDiagonal R x ⌊Real.sqrt (T * x)⌋₊| ≤
      (M * Real.sqrt T) * Real.sqrt x :=
  abs_aliasDiagonal_le_sqrt R hT hx hM hR

theorem validation_madness_lower_equivalence (P R : ℝ → ℝ) (I : ℝ)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hP : ∀ y : ℝ, P y = I * y + R y)
    (hR : ∀ y : ℝ, 1 / T ≤ y → |R y| ≤ M) :
    HasEventualSqrtLower (fun x => mobiusPoissonQuadratic P x ⌊Real.sqrt (T*x)⌋₊) ↔
      HasEventualSqrtLower (fun x =>
        mobiusPoissonRankOne I x ⌊Real.sqrt (T*x)⌋₊ +
          mobiusPoissonOffDiagonal R x ⌊Real.sqrt (T*x)⌋₊) :=
  eventual_sqrt_lower_poisson_iff_rankOne_offDiagonal P R I hT hM hP hR

/-- This arbitrary signed test is a falsifier of automatic positivity only. -/
theorem validation_madness_signed_test :
    hyperbolaT (fun n => if n = 1 then -1 else 0) 1 < 0 :=
  hyperbolaT_negative_test


theorem validation_madness_higher_prime_powers_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |actualCorrelationHigherPrimePowers t| ≤ C :=
  actualCorrelationHigherPrimePowers_uniform_bound

theorem validation_madness_prime_power_split (t : ℝ) :
    actualCorrelationPrimeField t =
      (∑ n ∈ Finset.Ioc 0 (actualCorrelationCutoff t) with n.Prime,
        Real.log n * actualCorrelationWeight t n) + actualCorrelationHigherPrimePowers t :=
  actualCorrelationPrimeField_split_prime_powers t

theorem validation_madness_drive_derivative_rapid (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |deriv actualCorrelationIntegerDrive t| ≤ C * Real.exp (-A * t) :=
  actualCorrelationIntegerDrive_deriv_rapid_bound A hA

theorem validation_madness_flat_test_derivative {r : ℝ} (hr : 0 < r) :
    HasDerivAt actualFlatMobiusTest
      (-(deriv actualCorrelationIntegerDrive (-Real.log r) +
          actualCorrelationIntegerDrive (-Real.log r) / 2) /
        (r * Real.sqrt r)) r :=
  actualFlatMobiusTest_hasDerivAt hr


theorem validation_madness_flat_test_c1 : ContDiff ℝ 1 actualFlatMobiusTest :=
  actualFlatMobiusTest_contDiff_one

theorem validation_madness_flat_test_compact : HasCompactSupport actualFlatMobiusTest :=
  actualFlatMobiusTest_hasCompactSupport

theorem validation_madness_actual_remainder_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → |actualFlatSamplingRemainder y| ≤ C :=
  actualFlatSamplingRemainder_bounded

theorem validation_madness_actual_diagonal (T : ℝ) (hT : 0 < T) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 0 < x →
      |aliasDiagonal actualFlatSamplingRemainder x ⌊Real.sqrt (T*x)⌋₊| ≤ D*Real.sqrt x :=
  actualFlatSamplingDiagonal_sqrt_bound T hT

theorem validation_madness_all_sampling_terms (y : ℝ) (hy : 0 < y) :
    actualFlatSamplingSum y = ∑' n : ℕ, actualFlatMobiusTest ((n:ℝ)/y) :=
  actualFlatSamplingSum_eq_tsum y hy

theorem validation_madness_actual_lower_equivalence (T : ℝ) (hT : 0 < T) :
    HasEventualSqrtLower (fun x =>
      mobiusPoissonQuadratic actualFlatSamplingSum x ⌊Real.sqrt (T*x)⌋₊) ↔
    HasEventualSqrtLower (fun x =>
      mobiusPoissonRankOne actualFlatSamplingMass x ⌊Real.sqrt (T*x)⌋₊ +
      mobiusPoissonOffDiagonal actualFlatSamplingRemainder x ⌊Real.sqrt (T*x)⌋₊) :=
  actualFlatSampling_eventual_lower_iff T hT


theorem validation_madness_actualCorrelationNativeDiagonal_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      |aliasDiagonal actualFlatSamplingRemainder (Real.exp t)
        (Nat.sqrt (actualCorrelationCutoff t / 2))| ≤ D*Real.sqrt (Real.exp t) :=
  actualCorrelationNativeDiagonal_bound

theorem validation_madness_actualCorrelationLongTerm_eventual_lower_iff_combined :
    (∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      -C ≤ hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2)) ↔
    (∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      -C ≤ (mobiusPoissonRankOne actualFlatSamplingMass (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2)) +
        mobiusPoissonOffDiagonal actualFlatSamplingRemainder (Real.exp t)
          (Nat.sqrt (actualCorrelationCutoff t / 2))) / Real.sqrt (Real.exp t)) :=
  actualCorrelationLongTerm_eventual_lower_iff_combined

theorem validation_madness_exact_sampling_bridge (t : ℝ) :
    Real.sqrt (Real.exp t) *
        hyperbolaT (actualCorrelationLogarithmicTest t) (actualCorrelationCutoff t / 2) =
      mobiusPoissonQuadratic actualFlatSamplingSum (Real.exp t)
        (Nat.sqrt (actualCorrelationCutoff t / 2)) :=
  actualCorrelationLongTerm_eq_sampling_quadratic t



theorem validation_madness_actual_mass_positive :
    actualFlatSamplingMass = actualSourceHalfMass^2 ∧ 0 < actualFlatSamplingMass :=
  ⟨actualFlatSamplingMass_eq_sourceHalfMass_sq, actualFlatSamplingMass_pos⟩

theorem validation_madness_actual_rank_one_nonnegative {x : ℝ} (hx : 0 ≤ x) (Y : ℕ) :
    0 ≤ mobiusPoissonRankOne actualFlatSamplingMass x Y :=
  mobiusPoissonRankOne_nonneg actualFlatSamplingMass_pos.le hx Y

end Zeta23.OPICARound4
