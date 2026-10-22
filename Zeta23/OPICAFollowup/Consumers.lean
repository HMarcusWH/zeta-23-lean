import Zeta23.OPICAFollowup.RobustLaurent
import Zeta23.OPICA.NativeJetAdapter

/-!
UNCHECKED continuation at 9b6a9a3.  This file supplies the full same-output
word/jet consumer only.  The other four original Consumers roots are still
OPEN and are not replaced by premises or empty packets.
-/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
namespace Zeta23.OPICAFollowup
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICA

/-- The selected right zero is the one already used by the native completed
input obstruction of this same Step123 output.  No independent zero is chosen. -/
def step123WordRightZero {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (_out : GeneratedStep123CompleteOutput rho beta phase late) : zetaZeroConfig.carrier :=
  nativeZeroJetRightZero rho

lemma step123WordRightZero_right {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) :
    1/2 < (step123WordRightZero out : ℂ).re :=
  nativeZeroJetRightZero_re_gt_half rho out.generated.offLine

/-- Full native local-word observation on the SAME existing generated output.
The independent histories are unrestricted beyond NativeWordHistory.  In
particular no joint continuation-domain certificate is added to this root.
The conditional derivative clause covers all positive completion counts,
including p*m=1; the normalized Laurent limit also covers p=0.
-/
theorem step123_word_jet_consumer {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late)
    (w : NativeWord)
    (history : NativeWordHistory ((step123WordRightZero out : ℂ)-1/2)) :
    let rr := step123WordRightZero out
    let hr := step123WordRightZero_right out
    (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
    (step123OpicaView out).field = nativeOriginalPrimeField ∧
    (step123OpicaView out).input = nativeCompletedInput ∧
    Step123SameStateFieldRecord out.generated.native ∧
    GeneratedStep123RangeObstruction rho out.generated.offLine ∧
    zeroMult (rr : ℂ) = zeroMult (rho : ℂ) ∧
    nativeZeroJetParameter rho + (nativeZeroJetDamping rho : ℂ) = (rr : ℂ)-1/2 ∧
    0 < nativeZeroJetDamping rho ∧
    (nativeWordPrimePole rr hr).source = nativeOriginalSource ∧
    (nativeWordPrimePole rr hr).center = (rr : ℂ)-1/2 ∧
    (nativeWordPrimePole rr hr).field = nativePrimeTransformGerm ∧
    (nativeWordPrimePole rr hr).residue =
      -(zeroMult (rho : ℂ) : ℂ)*nativeOriginalSourceLaplace ((rr : ℂ)-1/2) ∧
    (∃ S : ℝ, wordHistorySafeThreshold w history ≤ S ∧ 1/2 ≤ S ∧
      ∀ z : ℂ, S < z.re →
        (∀ term ∈ nativeWordCausalState w rr history,
          Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
        (nativeWordCausalState w rr history).laplace z =
          nativeWordTransformedField w rr history z) ∧
    MeromorphicAt (nativeWordTransformedField w rr history) ((rr : ℂ)-1/2) ∧
    (∀ z : ℂ, nativeWordCorrectedField w rr history z =
      wordUnitFactor w z*riemannZeta (z+1/2)^wordCompletionCount w*nativePrimeTransformGerm z) ∧
    meromorphicOrderAt (nativeWordCorrectedField w rr history) ((rr : ℂ)-1/2) =
      (((wordCompletionCount w*zeroMult (rho : ℂ) : ℕ) : ℤ)-1 : ℤ) ∧
    nativeWordLeadingCoefficient w rr =
      -(zeroMult (rho : ℂ) : ℂ)*nativeOriginalSourceLaplace ((rr : ℂ)-1/2)*
        wordUnitFactor w ((rr : ℂ)-1/2)*
        (iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rr : ℂ)/
          ((zeroMult (rho : ℂ)).factorial : ℂ))^wordCompletionCount w ∧
    nativeWordLeadingCoefficient w rr ≠ 0 ∧
    Tendsto (fun z => (z-((rr : ℂ)-1/2))^
      (-(((wordCompletionCount w*zeroMult (rho : ℂ) : ℕ) : ℤ)-1))*
        nativeWordCorrectedField w rr history z)
      (𝓝[≠] ((rr : ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rr)) ∧
    (0 < wordCompletionCount w →
      (nativeWordCorrectedField w rr history =ᶠ[𝓝[≠] ((rr : ℂ)-1/2)]
        nativeWordRegularRepresentative w rr hr) ∧
      AnalyticAt ℂ (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) ∧
      (∀ j : ℕ, j < wordCompletionCount w*zeroMult (rho : ℂ)-1 →
        iteratedDeriv j (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) = 0) ∧
      iteratedDeriv (wordCompletionCount w*zeroMult (rho : ℂ)-1)
        (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) =
        ((wordCompletionCount w*zeroMult (rho : ℂ)-1).factorial : ℂ)*
          nativeWordLeadingCoefficient w rr ∧
      iteratedDeriv (wordCompletionCount w*zeroMult (rho : ℂ)-1)
        (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) ≠ 0) ∧
    inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) =
      (-1 : ℂ)^zeroMult (rho : ℂ)*nativeCompletionRationalMultiplier ((rr : ℂ)-1/2)*
        nativeOriginalSourceLaplace ((rr : ℂ)-1/2)*
          iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rr : ℂ) ∧
    inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) ≠ 0 := by
  let rr := step123WordRightZero out
  let hr := step123WordRightZero_right out
  have hm : zeroMult (rr : ℂ) = zeroMult (rho : ℂ) := nativeZeroJetRightZero_mult rho
  have hphysical := nativeWord_corrected_transform w rr hr history
  have horder := nativeWord_order_and_leading w rr hr history
  have hview := step123_output_opica_view_correct out
  dsimp only
  refine ⟨hview.1,hview.2.1,hview.2.2.1,hview.2.2.2.1,hview.2.2.2.2,
    hm,nativeZeroJetParameter_add_damping rho,
    nativeZeroJetDamping_pos rho out.generated.offLine,rfl,rfl,rfl,?_,
    hphysical.1,hphysical.2.1,hphysical.2.2.1,?_,?_,horder.2.2.2.2.2.1,?_,?_,
    native_completed_input_obstruction_jet rho out.generated.offLine,
    native_completed_input_obstruction_ne_zero rho out.generated.offLine⟩
  · change -(zeroMult (rr:ℂ):ℂ)*nativeOriginalSourceLaplace ((rr:ℂ)-1/2)=_
    rw [hm]
  · simpa only [hm] using horder.2.1
  · simp only [nativeWordLeadingCoefficient,hm]
  · simpa only [hm] using horder.2.2.2.2.2.2.1
  · intro hp
    simpa only [hm] using nativeWord_first_nonzero_derivative w rr hr history hp

/-- Optional contour companion: its actual common DISK hypotheses and error
budget are explicit. They do not become premises of the local primary above.
No common global continuation domain for the histories is required here. -/
theorem step123_word_contour_consumer {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) (w : NativeWord)
    (history : NativeWordHistory ((step123WordRightZero out : ℂ)-1/2))
    (raw correction recovery : ℂ→ℂ) (r Eraw Ecorrection Erecovery : ℝ)
    (hr : 0<r)
    (hg : MeromorphicAt (nativeWordObservedField raw correction recovery)
      ((step123WordRightZero out : ℂ)-1/2))
    (hfd : AnalyticOnNhd ℂ (nativeWordCorrectedField w (step123WordRightZero out) history)
      (closedBall ((step123WordRightZero out : ℂ)-1/2) r \ {((step123WordRightZero out : ℂ)-1/2)}))
    (hgd : AnalyticOnNhd ℂ (nativeWordObservedField raw correction recovery)
      (closedBall ((step123WordRightZero out : ℂ)-1/2) r \ {((step123WordRightZero out : ℂ)-1/2)}))
    (hraw : ContourErrorBudget (nativeWordTransformedField w (step123WordRightZero out) history)
      raw ((step123WordRightZero out : ℂ)-1/2) r Eraw)
    (hcorrection : ContourErrorBudget (wordCorrection w history) correction
      ((step123WordRightZero out : ℂ)-1/2) r Ecorrection)
    (hrecovery : ∀ z∈sphere ((step123WordRightZero out : ℂ)-1/2) r, ‖recovery z‖≤Erecovery)
    (hstrict : Eraw+Ecorrection+Erecovery <
      ‖nativeWordLeadingCoefficient w (step123WordRightZero out)‖*
      r^(((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1)) :
    ‖laurentObservedCoefficient (nativeWordObservedField raw correction recovery)
      ((step123WordRightZero out : ℂ)-1/2) hg
      (((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1) -
      nativeWordLeadingCoefficient w (step123WordRightZero out)‖ ≤
      r^(-(((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1))*
      (Eraw+Ecorrection+Erecovery) ∧
    laurentObservedCoefficient (nativeWordObservedField raw correction recovery)
      ((step123WordRightZero out : ℂ)-1/2) hg
      (((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1) ≠ 0 := by
  exact (nativeWord_contour_consumer w (step123WordRightZero out)
    (step123WordRightZero_right out) history raw correction recovery r Eraw Ecorrection Erecovery
    hr hg hfd hgd hraw hcorrection hrecovery hstrict).2.2

end Zeta23.OPICAFollowup
