import Zeta23.OPICARound6.PrimeFactorPaths.NativeCells
import Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra

namespace Zeta23.OPICARound6.PrimeFactorPaths.NativeStoppingCost
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

theorem native_opposed_cost (X : ℕ) (j : Key) (r : Removal) :
    4 * max (evenDeviation X j r) 0 * max (-oddDeviation X j r) 0 =
      max ((max (survivorCharge X j r) 0)^2 - (unsignedDiscrepancy X j)^2) 0 := by
  simpa only [deviation_difference, deviation_sum] using
    Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra.opposed_eq_charge_minus_discrepancy (evenDeviation X j r) (oddDeviation X j r)

theorem native_opposed_cost_reverse (X : ℕ) (j : Key) (r : Removal) :
    4 * max (oddDeviation X j r) 0 * max (-evenDeviation X j r) 0 =
      max ((max (-survivorCharge X j r) 0)^2 - (unsignedDiscrepancy X j)^2) 0 := by
  have hd : oddDeviation X j r - evenDeviation X j r = -survivorCharge X j r := by
    linarith [deviation_difference X j r]
  rw [Zeta23.OPICARound6.PrimeFactorPaths.StoppingAlgebra.opposed_eq_charge_minus_discrepancy, hd,
    add_comm (oddDeviation X j r) _, deviation_sum]

end Zeta23.OPICARound6.PrimeFactorPaths.NativeStoppingCost
