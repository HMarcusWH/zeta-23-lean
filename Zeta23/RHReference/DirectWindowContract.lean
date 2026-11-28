import Zeta23.OPICARound6.PrimeDeficit.Source

/-!
# Direct arithmetic-window contracts

The arithmetic handoff supplies a complete real window at arbitrarily late
scales. No estimate between the supplied windows is assumed. The source and
energy are the existing literal von-Mangoldt source and its positive-part
energy; these contracts introduce no replacement arithmetic object.
-/

set_option autoImplicit false

noncomputable section

open Zeta23.OPICARound6.PrimeDeficit

namespace Zeta23.RHReference

/-- A one-sided upper bound on every real point of one native window. -/
def LiteralWindowUpper (t A Y : ℝ) : Prop :=
  ∀ x ∈ Set.Icc Y (Y ^ (3 / 2 : ℝ)),
    literalG x ≤ A * x ^ (1 / 2 + t)

/-- Complete good windows exist beyond every requested threshold. -/
def CofinalLiteralWindowUpper (t A : ℝ) : Prop :=
  ∀ B : ℝ, ∃ Y : ℝ,
    max B 2 ≤ Y ∧ LiteralWindowUpper t A Y

/-- The direct original arithmetic supplier, with coefficient exactly one. -/
def DirectArithmeticWindowSupply : Prop :=
  ∀ t : ℝ, 0 < t → CofinalLiteralWindowUpper t 1

/-- An energy upper bound only at cofinally many complete windows. -/
def CofinalWindowEnergyUpper (κ C : ℝ) : Prop :=
  ∀ B : ℝ, ∃ Y : ℝ,
    max B 2 ≤ Y ∧ literalGEnergy Y ≤ C * Y ^ κ

/-- Arbitrarily small normalized energy can be obtained after any threshold.
The threshold remains an input so that a supplied window can be selected after
both the comparison onset and the aperture required by C1. -/
def CofinalNormalizedLiteralEnergy (δ : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ B : ℝ, ∃ Y : ℝ,
    max B 2 ≤ Y ∧ literalGEnergy Y / Y ^ δ ≤ 1 / (n : ℝ)

end Zeta23.RHReference
