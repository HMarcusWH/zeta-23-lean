import Zeta23.CCM.CanonicalSmallApertureGroundSpectrum

noncomputable section

namespace Zeta23.CCM

/-!
# WP4: D2 Full K3 conditional mathematical certificate interface

An Arb search may eventually certify both parity bottoms on the frozen
continuous interval [1/512, log 16]. This Lean module proves *only*
that such a mathematically stated interval fact, if supplied, composes
with the already unconditional #275 coercive tiny-aperture base.

No binary certificate is accepted as a theorem here. The missing
all-interval premise is explicit and cannot be extracted from a finite
grid, a research script PASS flag, or an RH-equivalent conjecture.
-/

/-- A proved continuous finite-window K3 parity bound extends to all
positive apertures below log 16, using the unconditional small-aperture
unit lower bound with N=2. -/
theorem k3ParityBottom_positive_of_finite_window
    (p : ReversalParity)
    (hWindow : ∀ L ∈ Set.Icc ((1 : ℝ) / 512) (Real.log 16),
        0 < parityRayleighBottom p L 3)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom p L 3 := by
  by_cases hsmall : L ≤ (1 : ℝ) / 512
  · have hbase : 1 ≤ parityRayleighBottom p L 3 := by
      simpa using
        (one_le_parityRayleighBottom_succ_of_smallAperture
          p hL hsmall 2 (by omega))
    linarith
  · have hleft : (1 : ℝ) / 512 ≤ L :=
      (lt_of_not_ge hsmall).le
    exact hWindow L ⟨hleft, hUpper⟩

/-- The exact two-parity D2 logical record, conditional on genuine positive
whole-window certificates for BOTH legal compressed parity sectors. -/
theorem k3BothParityBottom_positive_of_finite_windows
    (hWindows : ∀ p : ReversalParity,
      ∀ L ∈ Set.Icc ((1 : ℝ) / 512) (Real.log 16),
        0 < parityRayleighBottom p L 3)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom .even L 3 ∧
      0 < parityRayleighBottom .odd L 3 := by
  exact ⟨k3ParityBottom_positive_of_finite_window .even
    (hWindows .even) hL hUpper,
    k3ParityBottom_positive_of_finite_window .odd
    (hWindows .odd) hL hUpper⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.k3ParityBottom_positive_of_finite_window
#print axioms Zeta23.CCM.k3BothParityBottom_positive_of_finite_windows
