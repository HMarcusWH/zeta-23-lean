import Zeta23.ExceptionalZero.Step123OutputProducer
import Zeta23.CCM.Step123SameStateN39

/-!
# N39: generated accessors for the actual original interior

The rho-free proof is in `CCM.Step123SameStateN39`. These accessors apply
it directly to the same native packet of the generated output. The
original depth is supplied by the source producer, with no new premise.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-- The original smooth negative energy of the same generated packet. -/
theorem GeneratedStep123Output.originalWeilEnergy_neg
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123Output ρ β σ R) :
    (zetaZeroConfig.W g.native.originalTrial g.native.originalTrial).re < 0 :=
  g.native.originalWeilEnergy_neg

/-- The generated original interior is not zero almost everywhere. -/
theorem GeneratedStep123Output.originalInterior_not_ae_zero
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123Output ρ β σ R) :
    ¬ (g.native.smoothOriginal.interior =ᵐ[volume] (0 : ℝ → ℂ)) :=
  g.native.originalInterior_not_ae_zero

/-- The generated original interior is not the zero function. -/
theorem GeneratedStep123Output.originalInterior_ne_zero
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123Output ρ β σ R) :
    g.native.smoothOriginal.interior ≠ (0 : ℝ → ℂ) :=
  g.native.originalInterior_ne_zero

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.GeneratedStep123Output.originalWeilEnergy_neg
#print axioms Zeta23.ExceptionalZero.GeneratedStep123Output.originalInterior_not_ae_zero
#print axioms Zeta23.ExceptionalZero.GeneratedStep123Output.originalInterior_ne_zero
