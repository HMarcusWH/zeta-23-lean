# Stage 15: the native forced log-resolvent and the sampling Stieltjes identity (F2)

This stage starts from the Stage 14 record `bd918c7cf62aac92aacaa4939b97f1ddd185dabf`, which
published Stages 12 to 14. The source commit checked here is
`ee783dd8c400971f9a887552f6544dd1ac572cab` (tree `8e97f1648f18d8ae41ef07ce9f99ee6eb9953f01`).
Exact hashes, commands and logs are in [stage15 STATUS.json](evidence/current-codex/stage15/STATUS.json).
All 100 original roots and 28 acceptance units remain required. RH, Step 4 and the independent
closing inequalities remain OPEN. No frozen specification, PDF, parent mathematical source or
optional-amendment status changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/NativeResolvent.lean` imports exactly
`Zeta23.OPICAFollowup.WeightedSpectralMeasure` and `Zeta23.OPICAFollowup.SamplingCompatibility`,
its BUILD_MANIFEST `direct_project_imports` list. Its required definition is
`nativeLogResolvent` κ t := (1/2π) ∫ e^(iξt) κ ζ(1/2 + iξ)/(a(ξ) - κ) dξ, the inverse log-Fourier
transform of the actual arithmetic quotient (a(ξ) = ξ² + 1/4). It is built from ζ and κ only, not
from any zero. The narrow runner now builds seventeen modules and replays twenty-two consumer files.
With this stage all five F2 roots have narrow gates.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `native_forced_resolvent_unique` (F2) | For an actual zero ρ (0 < Re ρ < 1) with κ = ρ(1 - ρ) off the cut [1/4, ∞):<br>- ψ = e^(t/2) h(e^t), with its log-unitary derivative ψ', is an H¹ pair (`LogH1`);<br>- it solves the weak forced equation ∫ ψ' φ' + (1/4 - κ) ∫ ψ φ = κ 𝔤(φ) for every Schwartz φ, where 𝔤 = -(D + 1/2) w is the Stage 13 force;<br>- it is the unique H¹ weak solution;<br>- its log-Fourier transform is κ ζ(1/2 + iξ)/(a(ξ) - κ);<br>- it equals `nativeLogResolvent` κ. | [ExpectedNativeResolvent.lean](consumers/ExpectedNativeResolvent.lean) (13 receipts) |
| `native_sample_stieltjes_identity` (F2) | Same hypotheses:<br>- b = Σ_{n ≥ 1} h(n) - 1/2;<br>- every cell gives ∫_n^(n+1) {x} h' = h(n + 1) - ∫_n^(n+1) h (the endpoint terms);<br>- {x} h' is integrable on (0, ∞) and b = ∫_0^∞ {x} h'(x) dx;<br>- b = ∫ w (ψ' - ψ/2), the H⁻¹-H¹ pairing of 𝔤 with ψ, and \|b\| ≤ ‖w‖₂ (∫ \|ψ'\|² + ∫ \|ψ\|²/4)^(1/2);<br>- w is real (conjugation) and b = (1/2π) ∫ conj(𝓕_log w)(iξ - 1/2) 𝓕_log ψ dξ (normalization);<br>- b = κ M(κ). | same file |
| `native_profile_spectral_norms` (F2) | For an actual zero with Im κ ≠ 0:<br>- ∫_0^∞ \|h\|² = \|κ\|² ∫ dω/\|a - κ\|² = \|κ\|² Im M(κ)/Im κ;<br>- the Euler form ∫ x² \|h'\|² = \|κ\|² ∫ a dω/\|a - κ\|²;<br>- for every second actual zero σ with κ_σ off the cut (mixed compatibility): N(ρ, σ) = κ_ρ conj κ_σ ∫ dω/((a - κ_ρ)(a - conj κ_σ)), Q(ρ, σ) = κ_ρ conj κ_σ ∫ a dω/((a - κ_ρ)(a - conj κ_σ)), and (κ_ρ - conj κ_σ) N = conj κ_σ b_ρ - κ_ρ conj b_σ;<br>- (F2.5) \|b\| ≤ \|κ\|(1 + \|κ\|/\|Im κ\|)(log(2π) - γ). | same file |

**Proof.**
- **Weak equation.** On a compact log test χ, the test x^(-1/2) χ(log x) on (0, ∞) turns the Stage 11
  forced Euler equation into ∫ ψ' χ' + (1/4 - κ) ∫ ψ χ = κ ∫ w (χ' - χ/2). Cutoffs β(t/(n + 1)) φ
  extend it to every Schwartz φ: ψ, ψ' ∈ L², and both sides converge by dominated convergence. The
  right side is κ 𝔤(φ) by Stage 13's `nativeLogForce_apply`.
- **Quotient.** ψ and ψ' are integrable: the profile and its derivative decay like e^(-\|t\|/2) in log
  variables. 𝓕ψ' = 2πiη 𝓕ψ for an absolutely continuous ψ, and testing the weak equation against
  Fourier transforms of Schwartz functions gives (ξ² + 1/4 - κ) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ). That
  uses Stage 13's 𝓕𝔤 = ζ(1/2 + 2πiη) and the fundamental lemma for the continuous difference.
- **Uniqueness.** A homogeneous H¹ weak solution D has (4π²η² + c) 𝓕D = 0 as an L² function in the
  tempered sense. The multiplier never vanishes off the cut, so 𝓕D = 0, D = 0 a.e., and D = 0 by
  continuity.
- **Inversion.** Off the cut \|(a - κ)^(-1)\| ≤ (1 + \|κ\|/δ)/a. Since \|ζ\| ≤ \|ζ\|² + 1, the quotient is
  dominated by a multiple of \|ζ\|²/a + 1/a, which is integrable by (F1.4). Mathlib's Fourier inversion
  for continuous L¹ functions with L¹ transform gives ψ = `nativeLogResolvent` κ.
- **Sample.**
  - On (n, n + 1), (x - n) h(x) has derivative h + (x - n) h'. The fundamental theorem of calculus,
    with {x} = x - n off the endpoint, gives the cell identity, and adjacent cells sum.
  - Both sides converge as N → ∞: {x} h' ≤ C min(1, x⁻²), Σ h(n) is summable, and ∫_0^∞ h = 1/2
    (Stage 9).
  - Substituting x = e^t gives w (ψ' - ψ/2) = e^t {e^t} h'(e^t).
  - Polarized Plancherel on L¹ ∩ L², with 𝓕_log w = -ζ(s)/s and 𝓕_log(ψ' - ψ/2) = -conj(s) 𝓕_log ψ
    (s = 1/2 + iξ), turns the integrand into κ \|ζ(s)\|²/(a - κ). With the density 1/(2π) this is κ M(κ).
- **Norms.**
  - The norm and Euler form come from Plancherel for ψ and ψ' (\|𝓕_log ψ'\| = \|ξ\| \|𝓕_log ψ\|) and Stage 10's
    form identity ∫ x² \|h'\|² = ∫ \|ψ'\|² + ∫ \|ψ\|²/4.
  - The mixed pairings come from the unitary substitutions N(ρ, σ) = ∫ conj ψ_σ ψ_ρ and
    Q(ρ, σ) = ∫ conj(ψ_σ' - ψ_σ/2)(ψ_ρ' - ψ_ρ/2), together with conj(iξ - 1/2)(iξ - 1/2) = a.
  - The undivided identity is the resolvent identity under ω,
    (κ - μ) ∫ dω/((a - κ)(a - μ)) = M(κ) - M(μ), with M(conj κ) = conj M(κ). (F2.5) is the Stage 14
    budget times \|κ\|.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **Domain.** The contract's domain is an actual off-line zero with κ nonreal. The first two roots
  are proved on the full resolvent set ℂ \ [1/4, ∞), which contains every nonreal κ: a weaker premise.
  The consumer derives the nonreal case from Re ρ ≠ 1/2 and Im ρ ≠ 0. The third root assumes Im κ ≠ 0,
  as (F2.5) requires; its mixed clauses accept any second actual zero with κ_σ off the cut.
- **"Unique H¹ solution of (-D² + 1/4 - κ) ψ = κ𝔤".** This means uniqueness among all `LogH1` pairs
  (D, D') solving the weak equation against every Schwartz test. The weak form pairs -D² as ∫ ψ' φ'
  (bilinear, no conjugation).
- **The forced log-resolvent.** `nativeLogResolvent` is an actual inverse Fourier transform of an
  integrable function (the root proves integrability off the cut). For κ on the cut no statement
  uses it.
- **"H⁻¹-H¹ pairing".** ∫ w (ψ' - ψ/2) is the continuous extension of 𝔤 from Schwartz tests: it equals
  𝔤(φ) on Schwartz φ (Stage 13) and is bounded by ‖w‖₂ times the H¹ form (Stage 10).
- **Endpoint terms, normalization and conjugation.** These are the explicit cell identity, the 1/(2π)
  Plancherel factor, and the reality of w (stated as conj w = w), each a separate clause.
- **"Norm and Euler form".** ∫_0^∞ \|h\|² and `logForm` h' = ∫_0^∞ x² \|h'\|².
- **Unpromoted supporting result.** `logFourier_zeroProfile_undivided`:
  (a(ξ) - κ) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ) for every actual zero in the strip, critical-line zeros
  included. The removable on-cut quotient remark stays unpromoted, as BUILD_SPEC's F2 note directs.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for seventeen modules and twenty-two
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Eleven negative
controls are rejected for their intended reasons:
- the quotient with a + κ;
- the weak equation with 1/4 + κ;
- the identification without the resolvent hypothesis;
- b = M(κ) and b = -κM(κ);
- the cell endpoint h(n);
- the Fourier pairing without conjugation;
- the norm without \|κ\|²;
- the Euler form without a;
- the mixed pairing with κ_σ;
- the budget factor without the 1.

The ledger now records 41 historical, 42 narrow and 17 absent roots. This is not aggregate
acceptance of 83 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The three roots above and the supporting results
   listed in STATUS.json, all standard-only. The consumer proves:
   - an actual off-line zero (Re ρ ≠ 1/2, Im ρ ≠ 0) has nonreal κ, its log profile is the forced
     log-resolvent, and b = κ M(κ);
   - for nonreal κ, b/κ = M(κ), Im(b/κ)/Im κ = ∫ dω/\|a - κ\|² > 0, and b ≠ 0;
   - the forced log-resolvent is itself an H¹ weak solution;
   - the diagonal N(ρ, ρ) is the norm formula;
   - at the conjugate zero conj ρ (ζ(conj s) = conj ζ(s)), the undivided identity has vanishing left side
     and forces b_(conj ρ) = conj b_ρ;
   - at a critical-line zero the supporting identity reads (ξ² - (Im ρ)²) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ),
     with both sides zero at ξ = Im ρ.
2. **Workflow harvest at `bd918c7c`** ([partial harvest](evidence/current-codex/stage15/ci-harvest-bd918c7c-partial.json)).
   - 20 of the 22 runs on the Stage 14 head had completed; no run was cancelled.
   - OPICA preparation, the exact-source subset, the narrow job (sixteen modules, twenty-one consumer
     files, including all three Stage 12 to 14 consumers) and the frozen-regression jobs pass in both
     the PR and the push run.
   - Sixteen of the eighteen inherited research replays pass. The post287 WP2/WP4 interval research
     and the post-284 source-inertia campaign were still running and are harvested with the next stage.
   - Only the designed fail-closed gates are red: Full release readiness (PR and push),
     opica-contract, opica-component-summary, python-rhrc and rhkg-compiler-receipt.
3. **What changed.** F2 is complete at the narrow level, with five roots. The sampling functional of
   an actual zero, b = Σ h(n) - 1/2, is now formally κ times the Stieltjes transform of the positive
   measure dω = \|ζ(1/2 + iξ)\|² dξ/2π, and the zero profile is identified with an explicit resolvent.
4. **Upstream.**
   - Inputs:
     - ForcedEuler (Stage 11) for the compact weak equation;
     - SawtoothForce (Stage 13) for 𝔤, its Fourier transform and its pairing formula;
     - LogFourierSobolev (Stage 10) for Plancherel, the form identity and the pairing bound;
     - ZeroProfiles (Stage 9) for decay, ∫_0^∞ h = 1/2 and the summable samples;
     - WeightedSpectralMeasure (Stage 14) for ω, M and the budget.
   - **Dependency compression (DERIVED, informal).** The Fourier quotient, the Parseval computation of
     ∫ w (ψ' - ψ/2) and the norms use nothing about the zero beyond the weak equation. For any κ off the
     cut, the zero-free resolvent `nativeLogResolvent` κ already satisfies ∫ w (ψ_κ' - ψ_κ/2) = κ M(κ).
     The zero hypothesis enters only through two identifications:
     - this resolvent is the actual profile e^(t/2) h(e^t), via the Stage 11 forced Euler equation;
     - the pairing is the sample Σ h(n) - 1/2, which needs summability and ∫ h = 1/2, both of which
       need ζ(ρ) = 0.
   - Two independent derivations of the undivided S2 identity now agree:
     - Stage 12, by integer-cell summation of the Euler equation;
     - this stage, by the resolvent identity under ω.
5. **Downstream.**
   - `BoundaryAmplitude` (F3) imports this module. Its generic forced profile
     1 - S_ρ/b_ρ - ζ(ρ) x^(ρ-1)/b_ρ is where ζ(ρ) = 0 becomes a plateau condition.
   - `Consumers.actual_force_sampling_consumer` (R2-S1b, F1, F2, F3) can now consume all of F1 and F2.
6. **Resurrected routes.** LEAD: the on-cut (critical-line) quotient.
   - The earlier obstacle was division by a vanishing Im κ.
   - That reason has changed: the undivided identity is now formal for every actual zero. The
     quotient is therefore determined off the two points ξ = ±Im ρ by the continuous transform 𝓕_log ψ.
   - The remark stays unpromoted.
7. **New RH-relevant clues.**
   - PROVED (consumer): an off-line zero would have b ≠ 0, with b/κ a value of the Herglotz function
     M, so Im(b/κ)/Im κ > 0.
   - This excludes nothing. Any value of M has this sign, which matches the paper's scope limit: a
     positive spectral density permits nonreal forced parameters.
   - EXPERIMENTAL SIGNAL ([numerical-falsification.log](evidence/current-codex/stage15/numerical-falsification.log)):
     at the first two zeros, 𝓕_log ψ(γ) computed from h equals κ i ζ'(ρ)/(2γ) to 1e-9.
   - DERIVED (informal): that value follows from the undivided identity and the continuity of 𝓕_log ψ.
   - LEAD: the multiplicity of a critical-line zero is visible in the Mellin transform of its own
     profile at its own height. 𝓕_log ψ(γ) ≠ 0 exactly when the zero is simple.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath, not interval certified; the first zeros are on the line,
     so κ is on the cut and the off-cut roots are not tested):
     - summation by parts and the log-variable pairing agree with b to 1.7e-8 and 3.8e-8 at L = 400
       (residual ~ L⁻³);
     - \|b\| is well below the H⁻¹-H¹ bound;
     - the undivided identity holds to ≤ 4e-7 relative at five frequencies per zero, with 𝓕_log ψ
       computed directly from h, while the control a + κ fails by O(1);
     - the endpoint h(n) is off by about 0.9.
   - Vacuity: the off-cut roots are conditional on an off-line zero, which may not exist. The
     supporting identity is exercised on actual critical-line zeros, formally and numerically.
   - Circularity: no premise mentions the conclusion. `nativeLogResolvent` is defined from ζ and κ only.
9. **Highest-leverage next moves.**
   - `SquareDefect` (R2-S3, four roots), proved in scratch.
   - `BoundaryAmplitude` (F3): the generic forced profile, unique in the log form domain, and its
     plateau coefficient.
   - `CoPoissonJets` → `ConfluentProfiles` → `FiniteSpanSeparation`, J5.2/MS1, and `Consumers`.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 15 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 15 head, the 17 absent roots, RH, Step 4 and the
independent closing inequalities.
