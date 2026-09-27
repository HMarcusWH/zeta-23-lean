import Zeta23.ExceptionalZero.QuantitativeDetectorFamily

namespace Zeta23.ExceptionalZero

structure QuantitativeCanonicalWitness where
  detector : QuantitativeDetectorData
  provenance : String
  carrier : String
  normalization : String

-- Visibility/masking control remains an OPEN obligation in the campaign
-- manifest. This module only preserves the same-witness data and provenance.

end Zeta23.ExceptionalZero
