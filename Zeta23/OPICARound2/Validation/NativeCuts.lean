import Zeta23.OPICARound2.NativeCuts

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICAFollowup

namespace Zeta23.OPICARound2.Validation

/-- Literal native field and literal half-line weighted energy. -/
theorem damping_energy_identity (d : ℕ) (ε : ℝ) :
    nativeDampingEnergy d ε = ∫⁻ t : ℝ in Ici 0,
      ENNReal.ofReal (Real.exp (-2*ε*t)*|primeFieldFamily d t|^2) := rfl

theorem damping_source_identity (d : ℕ) (ε t : ℝ) :
    nativeDampedFamily d ε t = ((Real.exp (-ε*t)*primeFieldFamily d t : ℝ):ℂ) := rfl

theorem expected_positive_abscissa (d : ℕ) :
    (∀ ε : ℝ, nativeZeroDisplacementSup<ε →
      (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
        (Real.exp (-2*ε*t)*|primeFieldFamily d t|^2))<∞) ∧
    (∀ ε : ℝ, 0<ε → ε<nativeZeroDisplacementSup →
      (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
        (Real.exp (-2*ε*t)*|primeFieldFamily d t|^2))=∞) ∧
    sInf {ε : ℝ | 0<ε ∧ (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
      (Real.exp (-2*ε*t)*|primeFieldFamily d t|^2))<∞}=nativeZeroDisplacementSup :=
  ⟨fun _ hε => nativeDampingEnergy_finite_of_theta_lt d hε,
    fun _ hε hlt => nativeDampingEnergy_infinite_below_theta d hε hlt,
    native_positive_damping_abscissa d⟩

theorem expected_actual_cut_equivalences :
    (nativeZeroDisplacementSup=0 ↔ NativeOriginalPrimeFieldAllDampedL2) ∧
    (NativeOriginalPrimeFieldAllDampedL2 ↔ NativeInputAllRangeClosure) ∧
    (NativeInputAllRangeClosure ↔ RiemannHypothesis) ∧
    (NativeOriginalPrimeFieldAllDampedIntegral ↔ RiemannHypothesis) :=
  ⟨native_damping_abscissa_and_cut_equivalence.2.2.2.1,
    native_damping_abscissa_and_cut_equivalence.2.2.2.2.1,
    native_actual_cuts_equivalent.2.1,native_actual_cuts_equivalent.2.2⟩

theorem expected_cofinal_complete_quietness (time : ℕ→ℝ)
    (h : Tendsto time atTop atTop) :
    nativeCompleteObservationQuiet time ↔ nativeZeroDisplacementSup=0 :=
  native_complete_quiet_iff_theta_zero time h

/-- Actual order zero is included; no growing-order condition has been dropped. -/
theorem expected_ms1_rate (time : ℕ→ℝ) (cofinal : Tendsto time atTop atTop)
    (d : ℕ→ℕ)
    (slow : Tendsto (fun n => (d n:ℝ)*Real.log ((d n:ℝ)+2)/time n) atTop (𝓝 0))
    (C : ℝ) (hC : 1<C) :
    Tendsto (fun n => Real.log
      (1+(∫ t : ℝ in Icc (time n-C*Real.log (time n)) (time n),
        |primeFieldFamily (d n) t|^2))/(2*time n)) atTop (𝓝 nativeZeroDisplacementSup) :=
  native_cut_slow_source_rate time cofinal d slow C hC

theorem actual_order_zero_damped_integrability {ε : ℝ}
    (hε : nativeZeroDisplacementSup<ε) :
    MemLp (fun t : ℝ => ((Real.exp (-ε*t)*primeFieldFamily 0 t : ℝ):ℂ)) 2 volume :=
  nativeDampedFamily_memLp_of_theta_lt 0 hε

#print axioms Zeta23.OPICARound2.native_damping_abscissa_and_cut_equivalence
#print axioms Zeta23.OPICARound2.native_cut_slow_source_rate
#print axioms Zeta23.OPICARound2.Validation.expected_positive_abscissa
#print axioms Zeta23.OPICARound2.Validation.expected_actual_cut_equivalences

theorem actual_zeta_count_exceeds_every_linear_budget (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C*T<(zetaZeroConfig.N T (2*T):ℝ) :=
  native_zeta_zero_count_superlinear C

#print axioms Zeta23.OPICARound2.native_zeta_zero_count_superlinear

end Zeta23.OPICARound2.Validation
