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

end Zeta23.OPICARound4
