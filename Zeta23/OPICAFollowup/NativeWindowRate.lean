import Zeta23.OPICAFollowup.MultiplicityTail

/-!
# Native fixed-source logarithmic windows

This file begins the original J5.2 window-rate lane. Its integral is the
literal continuous-horizon physical prime field, not a synthetic energy packet.
The full Tendsto-to-nativeZeroDisplacementSup theorem remains OPEN: the
multiplicity-tail lower bound must still be combined with uniform source costs,
the old-memory estimate and the matching upper rate.

The definitions and elementary boundary lemmas below are supporting results.
No primary root is claimed here.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup

/-- The open interval of completion-rate parameters is nonempty exactly
when the chosen actual right zero has sufficient displacement.  This is
the strict feasibility calculation in the J5.2 terminal-memory argument;
the right zero and constants are chosen BEFORE a varying horizon. -/
theorem nativeWindow_rate_parameter_interval {C Theta delta b : ℝ}
    (hC : 1 < C) (hdelta : Theta + (C - 1) * b < C * delta) :
    ∃ xi : ℝ, (Theta - delta) / (C - 1) < xi ∧ xi < delta - b := by
  have hden : 0 < C - 1 := by linarith
  have hstrict : (Theta - delta) / (C - 1) < delta - b := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [hdelta]
  refine ⟨((Theta - delta) / (C - 1) + (delta - b)) / 2, ?_, ?_⟩
  · linarith
  · linarith

/-- The two strict exponential separations: early memory decays relative to
the completed terminal witness, and that witness exceeds the test rate b.
This does NOT assume the missing analytic memory estimate as an input. -/
theorem nativeWindow_rate_exponent_margin {C Theta delta b xi : ℝ}
    (hC : 1 < C)
    (hlow : (Theta - delta) / (C - 1) < xi)
    (hhigh : xi < delta - b) :
    Theta - C * xi < delta - xi ∧ b < delta - xi := by
  have hden : 0 < C - 1 := by linarith
  have hstrict := (div_lt_iff₀ hden).mp hlow
  constructor
  · nlinarith [hstrict]
  · linarith

/-- Physical energy of the actual d-th native prime field on the literal
terminal interval [T-C log T,T]. No integer-horizon replacement is made. -/
def nativeWindowEnergy (d : ℕ) (C T : ℝ) : ℝ :=
  ∫ t : ℝ in Icc (T - C * Real.log T) T, |primeFieldFamily d t| ^ 2

/-- The physical integrand is integrable on every terminal window, including
degenerate and initially reversed intervals. -/
theorem nativeWindowEnergy_integrable (d : ℕ) (C T : ℝ) :
    IntegrableOn (fun t : ℝ => |primeFieldFamily d t| ^ 2)
      (Icc (T - C * Real.log T) T) := by
  have hc : Continuous (fun t : ℝ => |primeFieldFamily d t| ^ 2) :=
    ((primeFieldFamily_contDiff d).continuous.abs).pow 2
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

theorem nativeWindowEnergy_nonneg (d : ℕ) (C T : ℝ) :
    0 ≤ nativeWindowEnergy d C T := by
  unfold nativeWindowEnergy
  exact integral_nonneg (fun t => sq_nonneg _)

/-- A window ending before the actual causal prime gap contains no signal.
This uses the source-bound primeFieldFamily, not a prescribed zero field. -/
theorem nativeWindowEnergy_zero_before_causal_gap (d : ℕ) (C T : ℝ)
    (hT : T < nativeCausalGap) : nativeWindowEnergy d C T = 0 := by
  unfold nativeWindowEnergy
  have hz : ∀ t ∈ Icc (T - C * Real.log T) T,
      |primeFieldFamily d t| ^ 2 = (0 : ℝ) := by
    intro t ht
    rw [primeFieldFamily_zero_before d (lt_of_le_of_lt ht.2 hT)]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Icc hz]
  simp

/-- The normalised literal rate used in the unfinished J5.2 theorem. -/
def nativeWindowLogRate (d : ℕ) (C T : ℝ) : ℝ :=
  Real.log (1 + nativeWindowEnergy d C T) / (2 * T)

theorem nativeWindowLogRate_nonneg (d : ℕ) (C T : ℝ) (hT : 0 < T) :
    0 ≤ nativeWindowLogRate d C T := by
  unfold nativeWindowLogRate
  apply div_nonneg
  · exact Real.log_nonneg (by linarith [nativeWindowEnergy_nonneg d C T])
  · positivity

end Zeta23.OPICAFollowup
