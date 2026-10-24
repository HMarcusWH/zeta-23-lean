# Stage 13: the arithmetic sawtooth force (F1)

This stage starts from the Stage 12 record `8c5d0cad1494a3cad8035a9c8b26937fb2536010`, which
is published together with this stage. The source commit checked here is
`294e60f57ac967e23d0d39291732e4dd12bdeac4` (tree `1e4784aac58a897fce8be237612be0e71a2d8c84`).
Exact hashes, commands and logs are in [stage13 STATUS.json](evidence/current-codex/stage13/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain
OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment status
changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/SawtoothForce.lean` imports exactly
`Zeta23.OPICAFollowup.LogFourierSobolev` and `Zeta23.OPICAFollowup.ProfileEulerMaclaurin`, its
BUILD_MANIFEST `direct_project_imports` list, plus the Mathlib modules for the Euler-Mascheroni
constant and Stirling's formula. It defines the two required definitions:
- `sawtoothWeight` t := e^(-t/2) {e^t} (real valued, as a complex function on ℝ);
- `nativeLogForce` := -(∂ w) - (1/2) w, built from Mathlib's tempered-distribution derivative of
  the L² tempered distribution `sawtoothWeightTD` of w.

The narrow runner now builds fifteen modules and replays twenty consumer files.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `sawtooth_integrable_force_identity` (F1.1) | - w ∈ L¹ ∩ L²; w = e^(t/2) for t < 0 and \|w\| ≤ e^(-t/2);<br>- the tempered force acts on Schwartz tests by ∫ w (φ' - φ/2);<br>- only on smooth compactly supported tests, 𝔤 = Σ_{n≥1} n^(-1/2) δ_(log n) - e^(t/2) dt;<br>- at every t = log n, n ≥ 1 (n = 1 retained), w has left limit n^(-1/2) and value 0. | [ExpectedSawtoothForce.lean](consumers/ExpectedSawtoothForce.lean) (11 receipts) |
| `sawtooth_actual_mellin_fourier` (F1.2, F1.3) | - For 0 < Re s < 1, {x} x^(-s-1) is integrable on (0, ∞) and ∫_0^∞ {x} x^(-s-1) dx = -ζ(s)/s;<br>- 𝓕_log w(ξ) = -ζ(1/2 + iξ)/(1/2 + iξ) and -(1/2 + iξ) 𝓕_log w(ξ) = ζ(1/2 + iξ);<br>- in the Mathlib convention, as tempered distributions, 𝓕 𝔤 = ζ(1/2 + 2πi·). | same file |
| `sawtooth_norm_weighted_zeta_moment` (F1.4) | - Exact cells: ∫_0^1 {x}²/x² = 1 and ∫_n^(n+1) {x}²/x² = 1 + n/(n+1) - 2n log(1 + 1/n);<br>- the closed form ∫_0^L = 2L - H_L - 2(L-1) log L + 2 log Γ(L) and its limit log(2π) - γ;<br>- ‖w‖₂² = log(2π) - γ = (1/2π) ∫ \|ζ(1/2+iξ)\|²/(ξ² + 1/4) dξ, with the integrand integrable;<br>- 𝔤 ∈ H⁻¹: \|⟨𝔤, φ⟩\| ≤ (log(2π) - γ)^(1/2) ‖φ‖_(H¹), ‖φ‖²_(H¹) = ‖φ'‖² + ‖φ‖²/4, on H¹ pairs and Schwartz tests. | same file |

**Proof.**
- **Compact-test identity.** On each cell [log n, log(n+1)], e^t - n is smooth, and
  w' + w/2 = e^(t/2) there. Integrating by parts cell by cell telescopes, and each left endpoint
  contributes the left limit n^(-1/2). Compact support removes the outer terms. The cell at
  t < 0 is handled separately, where w = e^(t/2) and its boundary at t = 0 is the n = 1 atom.
- **Mellin transform.** It comes from the Stage 8 continuation
  ζ(s) = s/(s-1) - 1/2 - s ∫_1^∞ B₁({t}) t^(-s-1). The pieces 1/(1 - s) and 1/(2s) from (0, 1]
  and the mean part cancel exactly. The substitution x = e^t and the Stage 10 convention give the
  log-Fourier transform.
- **Fourier transform of the force.** (𝓕 𝔤) φ = ∫ w ((𝓕 φ)' - 𝓕 φ/2). Since w ∈ L¹, the
  multiplication formula moves this pairing to the transform side. There (𝓕 φ)' = 𝓕(-2πix φ)
  produces the symbol -(1/2 + 2πiη), and its product with 𝓕 w(η) is ζ(1/2 + 2πiη).
- **Norm.** The exact cell integrals telescope to the closed form. The limit uses Stirling's
  formula for log Γ(L) and H_L - log L → γ. The Stage 10 L¹ ∩ L² Plancherel identity then
  converts ‖w‖₂² into the weighted zeta moment. The H⁻¹ bound is the Stage 10 force-pairing bound
  with ‖w‖₂ = (log(2π) - γ)^(1/2).

**Recorded formalization choices (no premise added, no domain narrowed).**
- **Tempered force.** The force is a `TemperedDistribution` built from the actual L² function w
  and Mathlib's distributional derivative. The lattice-minus-continuum form is stated only on
  smooth compactly supported tests, where each piece makes sense. Neither exponentially growing
  piece is transformed separately.
- **The atom sum.** Σ_{n≥1} n^(-1/2) δ_(log n) acts as ∑' n, (n+1)^(-1/2) φ(log(n+1)). The sum is
  finite on every compact test.
- **Conventions.** The 2π-free logarithmic convention of Stage 10 is used for (F1.2). The Mathlib
  statement is the tempered-distribution identity 𝓕 𝔤 = ζ(1/2 + 2πi·). The consumer proves the
  conversion 𝓕_log w(2πη) = 𝓕 w(η).
- **H⁻¹.** "𝔤 ∈ H⁻¹" is the explicit bound with the weight a(ξ) = ξ² + 1/4 norm. The constant is
  the square root of the budget.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for fifteen modules and twenty
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Ten negative
controls are rejected for their intended reasons:
- Mellin transform +ζ(s)/s;
- log-Fourier denominator 1/2 - iξ;
- Mathlib-convention transform ζ(1/2 + iη);
- continuum part with a plus sign;
- atom weights n^(1/2);
- left limit 1 at log n;
- budget log(2π) + γ;
- weighted moment without 1/(2π);
- closed form with -2L log L;
- H⁻¹ constant equal to the budget instead of its square root.

The ledger now records 41 historical, 37 narrow and 22 absent roots. This is not aggregate
acceptance of 78 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The three roots above, with the supporting
   results:
   - `mellin_fract`;
   - `integral_fract_sq_closed` and `tendsto_integral_fract_sq`;
   - `sawtooth_weighted_zeta_moment`;
   - `sawtooth_compact_identity` and `sawtooth_jump`;
   - `fourier_nativeLogForce` and `logH1_schwartz`.

   All receipts are standard-only. The consumer proves:
   - an independent bump of radius 1/4 at log 2 isolates the single atom 2^(-1/2): the force on
     it equals 2^(-1/2) - ∫ e^(t/2) φ;
   - the jump of w at log 2 equals that atom weight;
   - the two conventions agree on w;
   - 1/2 < log(2π) - γ < 2.
2. **Workflow harvest at `b9627cc1`, partial**
   ([ci-harvest-b9627cc1-partial.json](evidence/current-codex/stage13/ci-harvest-b9627cc1-partial.json)).
   - At record time 20 of the 22 runs on the Stage 11 head had completed. None was cancelled.
   - The OPICA checkpoint (PR and push runs) passes preparation, the exact-source subset, the
     narrow candidates (thirteen modules and eighteen consumer files, including
     ExpectedForcedEuler, with the W01, W04/W07 and W06 steps) and the frozen regression.
   - Sixteen research replays have succeeded. The two long replays (post-284 and post287
     WP2/WP4) were still in progress and are harvested with the next stage.
   - Only the designed fail-closed gates are red: full release readiness, the parent
     opica-contract and opica-component-summary, python-rhrc and rhkg-compiler-receipt.
   - The Stage 12 head and this stage's head are pushed together after the Stage 11 CI
     completes.
3. **What changed.** F1 is complete at the narrow level. The weighted zeta moment
   (1/2π) ∫ \|ζ(1/2+iξ)\|²/(ξ² + 1/4) dξ = log(2π) - γ is now formal from the pinned Mathlib. It
   is a classical identity, but was not available there. The paper's force is an actual tempered
   distribution with explicit atoms and an explicit transform.
4. **Upstream.**
   - Stage 8's continuation formula is the only analytic input for (F1.3). No functional equation
     is used.
   - Stage 10's convention and its L¹ ∩ L² Plancherel identity give (F1.2) and (F1.4).
   - Dependency compression: no F1 statement involves a zero of ζ. The force, its transform, its
     norm and the budget are all construction-level and zero-free.
5. **Downstream.**
   - `WeightedSpectralMeasure` (F2) imports only `SawtoothForce`. Its measure
     dω = \|ζ(1/2+iξ)\|² dξ/(2π) has finite weighted moment ∫ dω/a = log(2π) - γ by (F1.4),
     without finite total mass, exactly as its contract requires.
   - For κ ∉ [1/4, ∞), \|1/(a - κ)\| ≤ C_κ/a on a ≥ 1/4, so M(κ) = ∫ dω/(a - κ) is absolutely
     convergent and holomorphic by dominated differentiation. Im M = Im κ ∫ dω/\|a - κ\|² is
     algebra. Both F2 roots of that module are therefore within reach of existing tools.
   - `NativeResolvent` then needs (F1.2): 𝓕_log 𝔤 = ζ(1/2 + iξ) is the right-hand side of the
     resolvent equation.
6. **Resurrected routes.** None. Stage 10's zero-free budget is now matched by the actual force.
7. **New RH-relevant clues.**
   - DERIVED: the H⁻¹ norm of the actual force equals ‖w‖₂ = (log(2π) - γ)^(1/2), with no zero
     dependence. Any separation of on-line from off-line zeros must come from the sampling
     functional, not from the force norm.
   - EXPERIMENTAL SIGNAL (Stage 12 f2-consistency.log): at the first two zeros, κ M(κ) computed
     from this module's measure ω reproduces the sampled R2-S2 defect b. The match improves with
     the cutoff, even though κ lies on the cut [1/4, ∞), where the F2 contract does not state
     the identity. The double zero of \|ζ\|² at ξ = γ cancels the pole there.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath 1.3.0, not interval certified;
     [numerical-falsification.log](evidence/current-codex/stage13/numerical-falsification.log)):
     - the Mellin transform at s = 1/2, 0.3 + 2i and the first zero agrees with -ζ(s)/s to 3e-7,
       1.7e-6 and 3e-7 (cell quadrature to 4000 with the mean-value tail);
     - the closed form matches direct quadrature at L = 1, 5 and 40 to 15 digits;
     - on a compact bump containing log 1, …, log 6, the force equals the atom sum minus the
       continuum part to working precision; without the atoms (-1.38) or with weights n^(1/2)
       (2.09) it misses the value 0.0753.
   - Stage 10 had already checked (F1.4) three ways (1.2606614, 1.260668 and log(2π) - γ).
   - Vacuity: all statements are unconditional or hold on the whole strip. The atom is detected
     by an independent test.
   - Circularity: no premise mentions ζ beyond the strip condition in (F1.3).
9. **Highest-leverage next moves.**
   - `WeightedSpectralMeasure` (F2, two roots, now unblocked; a candidate with consumer and
     negative controls already compiles in scratch).
   - `NativeResolvent` (F2, three roots), including b = κ M(κ). The Stage 12 signal suggests
     also checking its extension to the cut at actual zeros.
   - `SquareDefect` (R2-S3), proved in scratch.
   - `BoundaryAmplitude` (F3), `CoPoissonJets` and J5.2/MS1.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 13 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 12 and Stage 13 heads, the 22 absent roots, RH, Step 4
and the independent closing inequalities.
