import Zeta23.CCM.FirstCrossingGeneratedStrictEvenFrontier
import Zeta23.CCM.FirstCrossingInheritedStationarity

noncomputable section

namespace Zeta23.RHRC

open Zeta23.CCM

/-!
# Post-#282 contact-calculus contract

This module is a compiler-facing premise firewall.  The exported examples must
typecheck without caller-supplied legacy realization, curvature/arithmetic
identity, zero-curvature equality, endpoint barrier, RH, or RH-equivalent
positivity premise.
-/

example (c : GeneratedStrictEvenContact) :
    Nonempty (GeneratedStrictEvenVariationBranch c) :=
  c.production_frontier

example (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactFirstVariation .even
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0 :=
  c.firstVariation_eq_zero_of_inherited hinh

example (c : GeneratedStrictEvenContact)
    (hstationary :
      productionContactFirstVariation .even
        c.generated.shell.Lstar (c.generated.shell.k + 1) c.z = 0) :
    0 < productionContactRemainderValue
      c.generated.shell.Lstar (c.generated.shell.k + 1) c.z
      (canonicalStationaryEvenResponse c hstationary) :=
  c.production_stationary_remainder_pos hstationary

end Zeta23.RHRC
