# Stage 14: the arithmetic spectral measure and its Stieltjes function (F2)

This stage starts from the Stage 13 record `f958c65fef07f3f4403e8f46e09ebacf3a7dddd1`, which
is published together with this stage. The source commit checked here is
`496990ad01f2408cfca5edd81b9dc40428d120af` (tree `e3b3430e60eeea0cd3fabe501c6eae0d5eec39ac`).
Exact hashes, commands and logs are in [stage14 STATUS.json](evidence/current-codex/stage14/STATUS.json).
All 100 original roots and 28 acceptance units remain required. RH, Step 4 and the independent
closing inequalities remain OPEN. No frozen specification, PDF, parent mathematical source or
optional-amendment status changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean` imports exactly
`Zeta23.OPICAFollowup.SawtoothForce`, its BUILD_MANIFEST `direct_project_imports` list. It
defines the three required definitions:
- `spectralEnergy` ξ := ξ² + 1/4 (the paper's a);
- `arithmeticSpectralMeasure` := the density measure dω = \|ζ(1/2+iξ)\|² dξ/(2π), through
  `arithmeticDensity`;
- `arithmeticStieltjes` κ := ∫ dω/(a - κ) (the paper's M).

It also defines `spectralResolventSet` = {Im κ ≠ 0 or Re κ < 1/4}, proved equal to ℂ \ [1/4, ∞).
The narrow runner now builds sixteen modules and replays twenty-one consumer files.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `arithmetic_stieltjes_holomorphic` (F2) | - The resolvent set is ℂ \ [1/4, ∞) and is open; the density is nonnegative;<br>- 1/a is ω-integrable with ∫ dω/a = log(2π) - γ, and no finite total mass is asserted or used;<br>- locally absolutely convergent: every κ₀ off the cut has a ball on which \|(a - κ)⁻¹\| ≤ C/a uniformly;<br>- the kernel is ω-integrable at every resolvent point;<br>- M has derivative ∫ dω/(a - κ)² there and is holomorphic on the resolvent set. | [ExpectedWeightedSpectralMeasure.lean](consumers/ExpectedWeightedSpectralMeasure.lean) (10 receipts) |
| `arithmetic_stieltjes_sign_budget` (F2) | For Im κ ≠ 0:<br>- 1/\|a - κ\|² is ω-integrable;<br>- Im M(κ)/Im κ = ∫ dω/\|a - κ\|² > 0;<br>- \|M(κ)\| ≤ (1 + \|κ\|/\|Im κ\|)(log(2π) - γ) and ∫ dω/\|a - κ\|² ≤ (1 + \|κ\|/\|Im κ\|)(log(2π) - γ)/\|Im κ\|;<br>- no sample is asserted real. | same file |

**Proof.**
- **Weighted moment.** It is (F1.4) rewritten through the density of ω.
- **Domination.** For κ at distance δ > 0 from [1/4, ∞): a/(a - κ) = 1 + κ/(a - κ), so
  \|(a - κ)⁻¹\| ≤ (1 + \|κ\|/δ)/a, which is ω-integrable. On the ball of radius δ/2 the gap is at
  least δ/2. That gives the uniform local bound, and also a bound (2/δ)C/a for the derivative
  kernel (a - κ)⁻².
- **Holomorphy.** It follows from Mathlib's dominated differentiation under the integral.
- **Sign.** Im (a - κ)⁻¹ = Im κ/\|a - κ\|². The integral is positive because ω ≠ 0: its weighted
  moment log(2π) - γ is positive (log(2π) > 1 > 2/3 > γ).
- **Budget.** The same domination with δ = \|Im κ\|.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **The measure.** ω is `volume.withDensity` of the actual density, so it is a positive measure.
  Only its weighted moment is used.
- **"Outside [1/4, ∞)".** This is the set {Im κ ≠ 0 or Re κ < 1/4}, proved equal to the complement
  of the image of [1/4, ∞).
- **"Locally absolutely convergent".** Each point has a ball and one ω-integrable dominating
  function C/a valid for every κ in the ball.
- **"Holomorphic".** `DifferentiableOn ℂ` on the open resolvent set, with the explicit derivative.
- **"Explicit weighted-source bounds".** The two displayed bounds. They are the inputs of the
  paper's (F2.5) once b = κM(κ) is proved (NativeResolvent).

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for sixteen modules and twenty-one
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Eight negative
controls are rejected for their intended reasons:
- moment log(2π) + γ;
- moment 2π(log(2π) - γ);
- holomorphy on all of ℂ;
- derivative with a minus sign;
- integrability without the resolvent hypothesis;
- the sign identity with a minus sign;
- positivity without Im κ ≠ 0;
- the budget factor without the 1.

The ledger now records 41 historical, 39 narrow and 20 absent roots. This is not aggregate
acceptance of 80 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above, with the supporting results:
   - `arithmetic_weighted_moment`;
   - `integral_arithmeticSpectralMeasure` and `integrable_arithmeticSpectralMeasure_iff`;
   - `arithmeticSpectralMeasure_univ_pos`;
   - `exists_gap`, `gap_ball` and `norm_inv_sub_le`;
   - `isOpen_spectralResolventSet`.

   All receipts are standard-only. The consumer proves:
   - the weighted moment equals the F1 source norm ‖w‖₂² of the actual sawtooth weight;
   - M(-1) is real and positive (computed, not imposed);
   - Im M(i) > 0 and \|M(i)\| ≤ 2(log(2π) - γ);
   - an off-line strip parameter has Im κ = (1 - 2 Re ρ) Im ρ ≠ 0, so κ lies in the resolvent set
     with Im M/Im κ > 0;
   - a critical-line parameter has real κ = 1/4 + (Im ρ)² on the cut, outside the resolvent set,
     where neither root is asserted.
2. **Workflow harvest at `b9627cc1`** ([ci-harvest-b9627cc1.json](evidence/current-codex/stage14/ci-harvest-b9627cc1.json)).
   All 22 runs on the Stage 11 head have now completed; no run was cancelled. This completes the
   partial harvest recorded with Stage 13.
   - The two long research replays that were still running both succeeded:
     - post287 WP2/WP4 interval research;
     - the post-284 source-inertia campaign, including the M51 K=2 Arb certificate, the
       independent verification of every materialized K2 M51 interval, the M76 Arb grid and the
       WP4 D2 K3 feasibility gate (UNRESOLVED allowed). Its post287-full-k3 job was skipped, as on
       every pull_request run.
   - All eighteen inherited research replays pass. They are regression and research outputs with no
     OPICA theorem authority.
   - OPICA preparation, exact-source subset, narrow (thirteen modules, eighteen consumer files) and
     frozen-regression jobs pass.
   - Only the designed fail-closed gates are red: Full release readiness (PR and push),
     opica-contract, opica-component-summary, python-rhrc and rhkg-compiler-receipt.
3. **What changed.** The measure side of F2 is formal: ω, its finite weighted moment, the
   holomorphic Stieltjes function off the cut, the Herglotz sign and the explicit budget. What
   remains of F2 is the identification of the actual zero profile with the forced resolvent and
   b = κ M(κ) (`NativeResolvent`).
4. **Upstream.**
   - (F1.4) is the only analytic input. The whole module is zero-free: Stage 8's continuation,
     Stage 10's Plancherel identity and Stage 13's moment identity.
   - Dependency compression: positivity of ω needs no information about ζ beyond the moment
     identity, because a positive weighted moment forces ω ≠ 0.
5. **Downstream.**
   - `NativeResolvent` imports this module and `SamplingCompatibility`. Once b = κM(κ) is proved:
     - (F2.5) \|b\| ≤ \|κ\|(1 + \|κ\|/\|Im κ\|)(log(2π) - γ) is this stage's budget times \|κ\|;
     - DERIVED (informal): the first (F2.4) norm formula then follows from Stage 12's (S2.4),
       Im M/Im κ = N_ii/\|κ\|², and this stage's sign identity, Im M/Im κ = ∫ dω/\|a - κ\|².
       Together they give ‖h‖² = N_ii = \|κ\|² ∫ dω/\|a - κ\|² with no further analysis.
   - `BoundaryAmplitude` (F3) imports `NativeResolvent`.
6. **Resurrected routes.** None.
7. **New RH-relevant clues.**
   - DERIVED (informal): M is a Nevanlinna (Herglotz) function, and its Pick matrices
     [(M_i - conj M_j)/(κ_i - conj κ_j)] are the L²(ω) Gram matrices of 1/(a - κ_i). Stage 12's
     divided-difference positivity is therefore exactly the Pick positivity of M at the zero
     parameters, assuming b = κM. R2-S2 then carries no positivity information beyond the zero-free
     measure ω. This matches the paper: the mixed versions "identify its previously implicit
     source measure".
   - EXPERIMENTAL SIGNAL ([numerical-falsification.log](evidence/current-codex/stage14/numerical-falsification.log),
     with Stage 12's values):
     - at κ = 200 + 3i, near the first zero's κ₁ = 200.04 on the cut, M = 0.06441 + 0.00528i, so
       Re M is close to b₁/κ₁ = 0.064486;
     - Im M/Im κ = 0.00176 is close to N₁₁/κ₁² = 0.00184.

     This is consistent with the removable on-cut limits at an actual zero (paper remark after
     (F2.5); Stage 12 f2-consistency.log). It is not a formal statement.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath and numpy, not interval certified;
     [numerical-falsification.log](evidence/current-codex/stage14/numerical-falsification.log)):
     - ∫ dω/a = 1.2606680 against log(2π) - γ = 1.2606614 (|ξ| < 400 with a mean-value tail);
     - M(-1) = 0.46037 is real and positive;
     - at κ = i, 1 + 5i, 0.2 + 0.01i and 200 + 3i both bounds hold with margin, and the reversed
       sign fails;
     - central finite differences of M agree with ∫ dω/(a - κ)² to 8 digits (6 next to the cut
       edge);
     - the identity Im M/Im κ = ∫ dω/\|a - κ\|² is algebraic on the same nodes, so it is not an
       independent check.
   - Vacuity: the resolvent set contains -1, i and every off-line strip parameter's κ, and ω ≠ 0
     is proved.
   - Circularity: no premise mentions a zero of ζ. The consumer's zero-related statements use only
     the strip parameter's algebra.
9. **Highest-leverage next moves.**
   - `NativeResolvent` (F2, three roots): the H¹ forced resolvent, b = κM(κ) through the H⁻¹-H¹
     pairing ∫ w(ψ' - ψ/2), and (F2.4)/(F2.5).
   - `SquareDefect` (R2-S3), proved in scratch.
   - `BoundaryAmplitude` (F3), `CoPoissonJets` and J5.2/MS1.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 14 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 12 to 14 heads, the 20 absent roots, RH, Step 4 and
the independent closing inequalities.
