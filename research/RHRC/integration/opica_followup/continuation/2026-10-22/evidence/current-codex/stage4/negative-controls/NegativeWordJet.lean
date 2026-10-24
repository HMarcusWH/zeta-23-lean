import Zeta23.OPICAFollowup.Consumers

/-!
Independent expected-type and actual-domain consumers for the original root
`Zeta23.OPICAFollowup.step123_word_jet_consumer` (R1-NB1, R2-J1).

The 22 conclusion clauses are restated below with every `let` of the source
statement expanded, so no abbreviation can hide a weaker conclusion. The domain
consumer instantiates the root on outputs produced by the parent constructor
`exists_generatedStep123CompleteOutput` for every admissible off-line zero,
damping, phase, horizon, word and unrestricted history. No contour premise or
continuation-domain certificate is added.
-/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICA

namespace OPICAWordJetNegative

/-- Independent restatement of the complete same-output word/jet conclusion. -/
def WordJetConclusion {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late)
    (w : Zeta23.OPICAFollowup.NativeWord)
    (history : Zeta23.OPICAFollowup.NativeWordHistory
      ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)) : Prop :=
  (Zeta23.OPICA.step123OpicaView out).source = nativeOriginalIntegerDrive ∧
  (Zeta23.OPICA.step123OpicaView out).field = nativeOriginalPrimeField ∧
  (Zeta23.OPICA.step123OpicaView out).input = nativeCompletedInput ∧
  Step123SameStateFieldRecord out.generated.native ∧
  GeneratedStep123RangeObstruction rho out.generated.offLine ∧
  zeroMult (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) = zeroMult (rho : ℂ) ∧
  nativeZeroJetParameter rho + (nativeZeroJetDamping rho : ℂ) =
    (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2 ∧
  0 < nativeZeroJetDamping rho ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).source = nativeOriginalSource ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).center =
      (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2 ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).field =
      Zeta23.OPICAFollowup.nativePrimeTransformGerm ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).residue =
      -(zeroMult (rho : ℂ) : ℂ) * nativeOriginalSourceLaplace
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ∧
  (∃ S : ℝ, Zeta23.OPICAFollowup.wordHistorySafeThreshold w history ≤ S ∧ 1/2 ≤ S ∧
    ∀ z : ℂ, S < z.re →
      (∀ term ∈ Zeta23.OPICAFollowup.nativeWordCausalState w
          (Zeta23.OPICAFollowup.step123WordRightZero out) history,
        Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * term.regular t)) ∧
      (Zeta23.OPICAFollowup.nativeWordCausalState w
          (Zeta23.OPICAFollowup.step123WordRightZero out) history).laplace z =
        Zeta23.OPICAFollowup.nativeWordTransformedField w
          (Zeta23.OPICAFollowup.step123WordRightZero out) history z) ∧
  MeromorphicAt (Zeta23.OPICAFollowup.nativeWordTransformedField w
      (Zeta23.OPICAFollowup.step123WordRightZero out) history)
    ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ∧
  (∀ z : ℂ, Zeta23.OPICAFollowup.nativeWordCorrectedField w
      (Zeta23.OPICAFollowup.step123WordRightZero out) history z =
    Zeta23.OPICAFollowup.wordUnitFactor w z * riemannZeta (z + 1/2) ^
      Zeta23.OPICAFollowup.wordCompletionCount w *
        Zeta23.OPICAFollowup.nativePrimeTransformGerm z) ∧
  meromorphicOrderAt (Zeta23.OPICAFollowup.nativeWordCorrectedField w
      (Zeta23.OPICAFollowup.step123WordRightZero out) history)
    ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) =
    (((Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) : ℕ) : ℤ) : ℤ) ∧
  Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
      (Zeta23.OPICAFollowup.step123WordRightZero out) =
    -(zeroMult (rho : ℂ) : ℂ) * nativeOriginalSourceLaplace
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
      Zeta23.OPICAFollowup.wordUnitFactor w
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
      (iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta
          (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) /
        ((zeroMult (rho : ℂ)).factorial : ℂ)) ^ Zeta23.OPICAFollowup.wordCompletionCount w ∧
  Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
      (Zeta23.OPICAFollowup.step123WordRightZero out) ≠ 0 ∧
  Tendsto (fun z => (z - ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)) ^
      (-(((Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) : ℕ) : ℤ) - 1)) *
      Zeta23.OPICAFollowup.nativeWordCorrectedField w
        (Zeta23.OPICAFollowup.step123WordRightZero out) history z)
    (𝓝[≠] ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2))
    (𝓝 (Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
      (Zeta23.OPICAFollowup.step123WordRightZero out))) ∧
  (0 < Zeta23.OPICAFollowup.wordCompletionCount w →
    (Zeta23.OPICAFollowup.nativeWordCorrectedField w
        (Zeta23.OPICAFollowup.step123WordRightZero out) history =ᶠ[𝓝[≠]
          ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)]
      Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
        (Zeta23.OPICAFollowup.step123WordRightZero out)
        (Zeta23.OPICAFollowup.step123WordRightZero_right out)) ∧
    AnalyticAt ℂ (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
        (Zeta23.OPICAFollowup.step123WordRightZero out)
        (Zeta23.OPICAFollowup.step123WordRightZero_right out))
      ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ∧
    (∀ j : ℕ, j < Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1 →
      iteratedDeriv j (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
          (Zeta23.OPICAFollowup.step123WordRightZero out)
          (Zeta23.OPICAFollowup.step123WordRightZero_right out))
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) = 0) ∧
    iteratedDeriv (Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1)
        (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
          (Zeta23.OPICAFollowup.step123WordRightZero out)
          (Zeta23.OPICAFollowup.step123WordRightZero_right out))
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) =
      ((Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1).factorial : ℂ) *
        Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
          (Zeta23.OPICAFollowup.step123WordRightZero out) ∧
    iteratedDeriv (Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1)
        (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
          (Zeta23.OPICAFollowup.step123WordRightZero out)
          (Zeta23.OPICAFollowup.step123WordRightZero_right out))
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ≠ 0) ∧
  inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) =
    (-1 : ℂ) ^ zeroMult (rho : ℂ) * nativeCompletionRationalMultiplier
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
      nativeOriginalSourceLaplace ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
        iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta
          (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) ∧
  inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) ≠ 0

/-- Expected type: the root proves exactly the independently restated
conclusion for every existing output, word and unrestricted history. -/
theorem expected_step123_word_jet_consumer {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late)
    (w : Zeta23.OPICAFollowup.NativeWord)
    (history : Zeta23.OPICAFollowup.NativeWordHistory
      ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)) :
    WordJetConclusion out w history :=
  Zeta23.OPICAFollowup.step123_word_jet_consumer out w history

/-- Actual-domain consumer: for every zero, admissible damping, phase and
horizon, the parent constructor supplies a genuine same-state output whose
threshold is paid, and the full conclusion holds for every word and history. -/
theorem expected_step123_word_jet_actual_domain (rho : zetaZeroConfig.carrier) {beta : ℝ}
    (hbeta : 0 < beta) (hbetarho : beta < |(rho : ℂ).re - 1 / 2|)
    (phase : ReversalParity) (late : ℝ) (w : Zeta23.OPICAFollowup.NativeWord) :
    ∃ out : GeneratedStep123CompleteOutput rho beta phase late,
      max late step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
        ∀ history : Zeta23.OPICAFollowup.NativeWordHistory
            ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2),
          WordJetConclusion out w history := by
  obtain ⟨out, hpaid⟩ :=
    exists_eachPhase_cofinal_generatedStep123CompleteOutput rho hbeta hbetarho phase late
  exact ⟨out, hpaid, fun history => expected_step123_word_jet_consumer out w history⟩

/-- The selected right zero is genuinely to the right of the critical line. -/
theorem expected_step123_word_right_zero {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) :
    1/2 < (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ).re :=
  Zeta23.OPICAFollowup.step123WordRightZero_right out

end OPICAWordJetNegative

#print axioms OPICAWordJetNegative.expected_step123_word_jet_consumer
#print axioms OPICAWordJetNegative.expected_step123_word_jet_actual_domain
#print axioms OPICAWordJetNegative.expected_step123_word_right_zero
