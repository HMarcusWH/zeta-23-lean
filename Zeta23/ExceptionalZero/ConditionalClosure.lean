import Zeta23.ExceptionalZero.Defs

namespace Zeta23.ExceptionalZero

/-- Pure logical seam for the exceptional-zero strategy. The substantive mathematical work is to
    instantiate `bad`, `growth`, and prove the two hypotheses without circular assumptions. -/
theorem no_bad_of_growth_contradiction (bad growth : Prop)
    (bad_implies_growth : bad → growth)
    (not_growth : ¬ growth) : ¬ bad := by
  intro hbad
  exact not_growth (bad_implies_growth hbad)

end Zeta23.ExceptionalZero
