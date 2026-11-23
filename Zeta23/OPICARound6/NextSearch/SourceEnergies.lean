import Zeta23.OPICARound6.PrimeFactorPaths.NativeFullTransfer
import Zeta23.OPICARound6.PrimeFactorPaths.NativeStoppingCost
import Mathlib.Tactic.Linarith

/-!
# Exact native whole-coarse signed energy search interface

The native cutoff, complete shells, physical weights, raw charges, removed
targets and spent partners are NOT replaced by abstract variables.

No asymptotic estimate is asserted or proved in this module. The positive
energy inequality conditionally composes existing finite theorems. The
negative-sign analogue and any subpower assertion remain OPEN.
-/

noncomputable section
namespace Zeta23.OPICARound6.NextSearch

open Zeta23.OPICARound6.PrimeFactorPaths
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

/-- Unmodified positive raw charge on occupied complete coarse shells. -/
def rawPositiveEnergy (X : ℕ) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X,
    weight j * (max (RoughNodeCharges.charge (roughCutoff X) (rawLabels X j)) 0)^2

/-- Opposite polarity on the SAME actual source, weights and shells. -/
def rawNegativeEnergy (X : ℕ) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X,
    weight j * (max (-(RoughNodeCharges.charge (roughCutoff X) (rawLabels X j))) 0)^2

/-- Opposed parity surplus of the same survivors with complete removals. -/
def opposedSurvivorEnergy (X : ℕ) (r : Removal) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X,
    weight j * (4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0)

/-- Exact unsigned discrepancy; no quantitative bound is asserted. -/
def unsignedErrorEnergy (X : ℕ) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X, weight j * (unsignedDiscrepancy X j)^2

/-- The combined target and spent-partner contribution from NativeCells. -/
def completeRemovalCost (X : ℕ) (r : Removal) : ℝ :=
  ∑ j ∈ wholeCoarseKeys X, weight j *
    (2 * (rawLabels X j).card *
      |RoughNodeCharges.charge (roughCutoff X) (removedLabels X j r)|)

/-- DERIVED: existing native finite signed-source transfer, unchanged. -/
theorem rawPositiveEnergy_le_full_components (X : ℕ) (r : Removal) :
    rawPositiveEnergy X ≤
      opposedSurvivorEnergy X r + unsignedErrorEnergy X +
        completeRemovalCost X r := by
  simpa only [rawPositiveEnergy, opposedSurvivorEnergy, unsignedErrorEnergy,
    completeRemovalCost] using
      NativeFullTransfer.native_raw_energy_upper X r (wholeCoarseKeys X)

/-- Conditional consumer: three arithmetic budgets are PREMISES, not proved. -/
theorem rawPositiveEnergy_le_of_component_budgets
    (X : ℕ) (r : Removal) (a b c : ℝ)
    (hOpposed : opposedSurvivorEnergy X r ≤ a)
    (hUnsigned : unsignedErrorEnergy X ≤ b)
    (hRemoved : completeRemovalCost X r ≤ c) :
    rawPositiveEnergy X ≤ a + b + c := by
  have h := rawPositiveEnergy_le_full_components X r
  linarith

/-- Source-native OPEN surrogate, NOT the original full ACTUAL_UPPER node. -/
def PositiveRawSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X₀ : ℕ,
    ∃ X : ℕ, max X₀ 64 ≤ X ∧ rawPositiveEnergy X ≤ C * (X : ℝ)^ε

/-- Fixed-negative-polarity surrogate. OPEN. -/
def NegativeRawSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X₀ : ℕ,
    ∃ X : ℕ, max X₀ 64 ≤ X ∧ rawNegativeEnergy X ≤ C * (X : ℝ)^ε

/-- One polarity selected BEFORE all epsilon/horizon quantifiers. OPEN. -/
def OnePolarityRawSubpower : Prop :=
  PositiveRawSubpower ∨ NegativeRawSubpower

end Zeta23.OPICARound6.NextSearch
