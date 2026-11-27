import Zeta23Arithmetic.NativePrincipal
import Zeta23.RHReference.CompactEnergyClosure
import Zeta23.RHReference.Perron.LiteralPerronFixedStripTransfer

/-!
Connect the attributed arithmetic supply and the Perron transfer to the
literal source and generated witness pair. Qualification requires the exact
common compiler epoch and a reviewed independently pinned source closure.
-/

set_option autoImplicit false

namespace Zeta23.RHReference

open Zeta23.OPICARound6.PrimeDeficit

/-- Bind the proved Perron estimate to the unchanged native source definition. -/
theorem native_literal_ramp_fixed_gap_transfer : LiteralRampFixedStripTransfer := by
  intro t ht ht₁ hzero
  simpa only [literalG] using literalRamp_fixed_gap_transfer ht ht₁ hzero

/-- Exact stock target, reached through the actual generated trial pair. -/
theorem riemannHypothesis_compact_literal_ramp_candidate : RiemannHypothesis := by
  obtain ⟨δ, hδ, hcompare⟩ := Zeta23.OPICATerminal.bothParityPowerComparison_proved
  let t : ℝ := min (δ / 12) (1 / 8)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht₁ : t ≤ 1 / 8 := min_le_right _ _
  have ht₂ : t ≤ δ / 12 := min_le_left _ _
  have hzero (s : ℂ) (hs : 1 / 2 + t / 2 < s.re) (hs₁ : s ≠ 1) :
      riemannZeta s ≠ 0 := by
    intro hz
    exact (not_le_of_gt hs) (Zeta23Arithmetic.Principal.principal_fixed_strip
      (by linarith : 1 / 2 < (1 / 2 + t / 2 : ℝ))
      (by linarith : (1 / 2 + t / 2 : ℝ) < 1) s hs₁ hz)
  exact compact_energy_reference_of_fixed_strip hcompare ht
    (by linarith) (by linarith) hzero native_literal_ramp_fixed_gap_transfer

end Zeta23.RHReference

#print axioms Zeta23.RHReference.native_literal_ramp_fixed_gap_transfer
#print axioms Zeta23.RHReference.riemannHypothesis_compact_literal_ramp_candidate
