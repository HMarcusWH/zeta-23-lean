import Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

namespace Zeta23.OPICARound6.PrimeFactorPaths.NativeFullTransfer
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells
open Zeta23.OPICARound6.PrimeFactorPaths

/-- The full native positive charge energy is bounded by the survivor deficit product,
the unsigned square discrepancy and the cost of signed removals in every incident cell. -/
theorem native_raw_energy_upper (X : ℕ) (r : Removal) (nodes : Finset Key) :
    (∑ j ∈ nodes, weight j * (max (RoughNodeCharges.charge (roughCutoff X) (rawLabels X j)) 0)^2) ≤
      (∑ j ∈ nodes, weight j * (4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0)) +
      (∑ j ∈ nodes, weight j * (unsignedDiscrepancy X j)^2) +
      ∑ j ∈ nodes, weight j *
        (2 * (rawLabels X j).card * |RoughNodeCharges.charge (roughCutoff X) (removedLabels X j r)|) := by
  have hchange := RoughNodeCharges.selector_energy_loss nodes (rawLabels X) r.all
    (roughCutoff X) weight (fun j _ => weight_nonneg j) 1 (by norm_num)
  simp only [one_mul] at hchange
  have hsigned :
      (∑ j ∈ nodes, weight j * (max (RoughNodeCharges.charge (roughCutoff X) (rawLabels X j)) 0)^2) -
      (∑ j ∈ nodes, weight j * (max (survivorCharge X j r) 0)^2) ≤
      ∑ j ∈ nodes, weight j *
        (2 * (rawLabels X j).card * |RoughNodeCharges.charge (roughCutoff X) (removedLabels X j r)|) := by
    rw [← Finset.sum_sub_distrib]
    apply le_trans _ hchange
    apply Finset.sum_le_sum
    intro j _
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (weight_nonneg j)
  have hsurv := (native_energy_bracket X r nodes).2
  linarith

end Zeta23.OPICARound6.PrimeFactorPaths.NativeFullTransfer
