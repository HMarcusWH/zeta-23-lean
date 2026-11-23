import Zeta23.OPICARound6.NextSearch.BipolarTransfer

open Zeta23.OPICARound6.NextSearch
open Zeta23.OPICARound6.PrimeFactorPaths.NativeCells

noncomputable section

-- Independent literal consumers for the key finite/conditional statements.
example (X : ℕ) (r : Removal) :
    rawNegativeEnergy X ≤ reverseOpposedSurvivorEnergy X r +
      unsignedErrorEnergy X + completeRemovalCost X r :=
  rawNegativeEnergy_le_full_components X r

example (X : ℕ) (r : Removal) :
    rawPositiveEnergy X + rawNegativeEnergy X ≤
      pairedOpposedSurvivorEnergy X r + unsignedErrorEnergy X + completeRemovalCost X r :=
  (rawBipolarEnergy_bracket X r).2

example (r : ℕ → Removal)
    (h : TailSubpower (fun X => unsignedErrorEnergy X + completeRemovalCost X (r X))) :
    OnePolarityRawSubpower ↔
      (CofinalSubpower (fun X => opposedSurvivorEnergy X (r X)) ∨
       CofinalSubpower (fun X => reverseOpposedSurvivorEnergy X (r X))) :=
  onePolarityRawSubpower_iff_opposed_of_tail_error r h

#check Zeta23.OPICARound6.NextSearch.raw_survivor_polarity_difference
#print axioms Zeta23.OPICARound6.NextSearch.raw_survivor_polarity_difference
#check Zeta23.OPICARound6.NextSearch.reverseOpposedSurvivorEnergy_bracket
#print axioms Zeta23.OPICARound6.NextSearch.reverseOpposedSurvivorEnergy_bracket
#check Zeta23.OPICARound6.NextSearch.rawNegativeEnergy_bracket
#print axioms Zeta23.OPICARound6.NextSearch.rawNegativeEnergy_bracket
#check Zeta23.OPICARound6.NextSearch.rawNegativeEnergy_le_full_components
#print axioms Zeta23.OPICARound6.NextSearch.rawNegativeEnergy_le_full_components
#check Zeta23.OPICARound6.NextSearch.rawPositiveEnergy_bracket
#print axioms Zeta23.OPICARound6.NextSearch.rawPositiveEnergy_bracket
#check Zeta23.OPICARound6.NextSearch.rawSquareEnergy_eq_polarities
#print axioms Zeta23.OPICARound6.NextSearch.rawSquareEnergy_eq_polarities
#check Zeta23.OPICARound6.NextSearch.rawSquareEnergy_removal_bound
#print axioms Zeta23.OPICARound6.NextSearch.rawSquareEnergy_removal_bound
#check Zeta23.OPICARound6.NextSearch.pairedOpposedSurvivorEnergy_eq
#print axioms Zeta23.OPICARound6.NextSearch.pairedOpposedSurvivorEnergy_eq
#check Zeta23.OPICARound6.NextSearch.pairedOpposedSurvivorEnergy_bracket
#print axioms Zeta23.OPICARound6.NextSearch.pairedOpposedSurvivorEnergy_bracket
#check Zeta23.OPICARound6.NextSearch.rawBipolarEnergy_bracket
#print axioms Zeta23.OPICARound6.NextSearch.rawBipolarEnergy_bracket
#check Zeta23.OPICARound6.NextSearch.unsignedErrorEnergy_nonnegative
#print axioms Zeta23.OPICARound6.NextSearch.unsignedErrorEnergy_nonnegative
#check Zeta23.OPICARound6.NextSearch.cofinalSubpower_of_tail_error
#print axioms Zeta23.OPICARound6.NextSearch.cofinalSubpower_of_tail_error
#check Zeta23.OPICARound6.NextSearch.cofinalSubpower_iff_of_tail_error
#print axioms Zeta23.OPICARound6.NextSearch.cofinalSubpower_iff_of_tail_error
#check Zeta23.OPICARound6.NextSearch.positiveRawSubpower_iff_opposed_of_tail_error
#print axioms Zeta23.OPICARound6.NextSearch.positiveRawSubpower_iff_opposed_of_tail_error
#check Zeta23.OPICARound6.NextSearch.negativeRawSubpower_iff_opposed_of_tail_error
#print axioms Zeta23.OPICARound6.NextSearch.negativeRawSubpower_iff_opposed_of_tail_error
#check Zeta23.OPICARound6.NextSearch.onePolarityRawSubpower_iff_opposed_of_tail_error
#print axioms Zeta23.OPICARound6.NextSearch.onePolarityRawSubpower_iff_opposed_of_tail_error

-- These are proposition definitions only. They are not proved here.
#check PositiveRawSubpower
#check NegativeRawSubpower
#check OnePolarityRawSubpower
