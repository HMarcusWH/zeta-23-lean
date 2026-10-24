import Zeta23.OPICAFollowup.NativeWindowRate

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup

/-- Original MS1 primary: arbitrary cofinal real horizons, with any finite
nonpositive prefix retained by eventual equality. The source-order hypothesis
is the original d log(d+2)=o(T), including order zero. -/
theorem native_slow_source_window_rate (time : ℕ → ℝ)
    (cofinal : Tendsto time atTop atTop) (d : ℕ → ℕ)
    (slow : Tendsto (fun n => (d n : ℝ)*Real.log ((d n : ℝ)+2)/time n) atTop (𝓝 0))
    (C : ℝ) (hC : 1 < C) :
    Tendsto (fun n =>
      Real.log (1+(∫ t : ℝ in Icc (time n-C*Real.log (time n)) (time n),
        |primeFieldFamily (d n) t|^2))/(2*time n)) atTop (𝓝 nativeZeroDisplacementSup) :=
  NativeWindowProof.Asymptotic.slowSourceRealHorizons_window_rate time cofinal d slow hC

#print axioms native_slow_source_window_rate
end Zeta23.OPICAFollowup
