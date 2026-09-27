import Zeta23.ExceptionalZero.QuantitativeDetectorFamily

namespace Zeta23.ExceptionalZero

structure QuantitativeCanonicalWitness where
  detector : QuantitativeDetectorData
  provenance : String
  carrier : String
  normalization : String

def QuantitativeCanonicalWitnessVisibility : Prop := False

end Zeta23.ExceptionalZero
