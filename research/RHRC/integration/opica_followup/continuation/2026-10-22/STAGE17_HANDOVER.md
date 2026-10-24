# Stage 17: the generic forced resolvent and its boundary amplitude (F3)

This stage starts from the Stage 16 record `c6ce649d`. The source commit checked here is
`ff73372615bad86e613081318cebf2b453def4bf` (tree `cf212d4798df70380f5b730a43bbe220a72aadeb`). Exact hashes, commands and logs are in
[stage17 STATUS.json](evidence/current-codex/stage17/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain OPEN.
No frozen specification, PDF, parent mathematical source or optional-amendment status changed, and
no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/BoundaryAmplitude.lean` imports exactly
`Zeta23.OPICAFollowup.NativeResolvent` and `Zeta23.OPICAFollowup.ProfileEulerMaclaurin`, its
BUILD_MANIFEST `direct_project_imports` list. It defines the two required definitions:
- `boundaryAmplitude` ρ := ζ(ρ)/b_ρ;
- `genericForcedProfile` ρ := 1 - S_ρ(\|x\|)/b_ρ - (ζ(ρ)/b_ρ)\|x\|^(ρ-1), built from the actual finite
  sums, together with its explicit derivative `genericForcedProfileDeriv`.

The narrow runner now builds nineteen modules and replays twenty-four consumer files. With this stage
both F3 roots have narrow gates.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `generic_forced_profile_unique` (F3) | For an arbitrary parameter 1/2 < Re ρ < 1, Im ρ ≠ 0, not necessarily a zero:<br>- h̃ lies in the log form domain;<br>- it satisfies the actual force equation ∫ x² h̃' φ' = κ(∫ (h̃ - 1) φ + Σ_{n ≥ 1} φ(n)) on positive-axis tests;<br>- every log-form-domain solution of that equation equals h̃ on (0, ∞);<br>- in log variables ψ = e^(t/2) h̃(e^t) is in H¹, solves (-D² + 1/4 - κ) ψ = κ𝔤 weakly on Schwartz tests and is the unique H¹ weak solution;<br>- 𝓕_log ψ = κ ζ(1/2 + iξ)/(a - κ), and ψ equals `nativeLogResolvent` κ;<br>- both ends are controlled: near 0, h̃ = O(x^(Re ρ - 1)) and \|h̃'\| = \|A(ρ - 1)\| x^(Re ρ - 2); at infinity, h̃ = O(x^(-Re ρ)) and h̃' = O(x^(-Re ρ - 1)). | [ExpectedBoundaryAmplitude.lean](consumers/ExpectedBoundaryAmplitude.lean) (8 receipts) |
| `generic_boundary_amplitude` (F3) | For 1/2 < Re ρ < 1:<br>- b_ρ = (1 - 2ρ)/κ;<br>- on (0, 1), h̃ = 1 - (ζ(ρ)/b_ρ) x^(ρ-1);<br>- the plateau h̃ ≡ 1 on (0, 1) holds iff ζ(ρ) = 0, and then h̃ is the zero profile;<br>- at infinity, \|h̃ - (-(ζ(1-ρ)/b_ρ) x^(-ρ) + κ B₂({x})/(2x²))\| ≤ C x⁻³;<br>- no integrability of h̃ is asserted. | same file |

**Proof.**
- **Tail.** The Stage 9 finite-sum expansion
  S_ρ = ζ(1-ρ) x^(-ρ) - ζ(ρ) x^(ρ-1) + b_ρ + (2ρ - 1) B₂/(2x²) + R holds for every strip parameter.
  With κ b_ρ = 1 - 2ρ, the ζ(ρ) x^(ρ-1) term cancels the boundary term exactly. The derivative
  expansion of the cells gives h̃' = ρ(ζ(1-ρ)/b_ρ) x^(-ρ-1) + O(x⁻²).
- **Log form domain.**
  - Near 0, x^(2Re ρ - 2) is integrable because Re ρ > 1/2. At infinity, x^(-2Re ρ) is integrable for
    the same reason.
  - The zero-profile derivative is bounded for every strip parameter, which gives the local FTC
    representation and interval integrability.
- **Force equation.**
  - The Stage 11 identity ∫ x² h' φ' = κ(∫ (h - 1) φ + Σ φ(n)) holds for every strip parameter
    ≠ 1/2.
  - For u = x^(ρ-1), (x² u')' = ρ(ρ - 1) x^(ρ-1) = -κu, and integration by parts on the support of a
    positive-axis test gives ∫ x² u' φ' = κ ∫ u φ. So h̃ = h - Au satisfies the same identity with no
    new atom.
- **Weak equation and resolvent.**
  - The Stage 15 transfer to log variables is generalized here to `log_weak_compact_of`, which takes
    any log-form-domain pair with this Euler identity. The cutoff extension then gives the Schwartz
    weak equation.
  - ψ and ψ' are dominated by K e^(-(Re ρ - 1/2)\|t\|), so they are L¹. The Stage 15 Fourier quotient,
    uniqueness and inversion then apply verbatim with Im κ = (1 - 2Re ρ) Im ρ ≠ 0.
  - Physical uniqueness: any log-form-domain solution g maps to an H¹ weak solution, which equals
    e^(t/2) h̃(e^t), so g = h̃ on (0, ∞).
- **Plateau.** If h̃ ≡ 1 on (0, 1), evaluating at 1/2 gives A 2^(1-ρ) = 0, so A = 0 and ζ(ρ) = 0.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **Domain.** `generic_forced_profile_unique` uses exactly the source hypotheses
  1/2 < Re ρ < 1, Im ρ ≠ 0. `generic_boundary_amplitude` is proved without Im ρ ≠ 0 (a weaker
  premise).
- **"The actual force equation".** This is the physical Euler identity on positive-axis tests (the
  distributional equation -(x² h')' = κ(h - 1 + Σ δ_n) on (0, ∞)), and in log variables the weak
  equation with the tempered force 𝔤 = -(D + 1/2) w of Stage 13.
- **"Uniquely solves".** This means uniqueness among log-form-domain profiles (physical) and among H¹
  pairs (log variables).
- **"Both ends controlled".** These are explicit power bounds for h̃ and h̃' near 0 and at infinity.
- **h̃ is even.** h̃ is defined with \|x\| so that it is even like the zero profile; only (0, ∞) enters.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for nineteen modules and twenty-four
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Nine negative
controls are rejected for their intended reasons:
- a plus sign near 0;
- the plateau iff ζ(ρ) ≠ 0;
- the tail term x^(ρ-1) with ζ(ρ);
- the log-form-domain claim on 0 < Re ρ;
- the identification without Im ρ ≠ 0;
- the quotient with a + κ;
- the force equation without the comb;
- the resolvent at conj κ;
- the near-zero exponent Re ρ.

The ledger now records 41 historical, 48 narrow and 11 absent roots. This is not aggregate
acceptance of 89 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** Both roots and the supporting results listed in
   STATUS.json, all standard-only. The consumer proves:
   - at an actual off-line zero with 1/2 < Re ρ < 1, h̃ is the zero profile, and the F2 and F3
     routes to the forced log-resolvent agree;
   - if ζ(ρ) ≠ 0, the plateau fails and h̃ is unbounded near 0, so it is not a sharp-gap profile;
   - if ζ(1 - ρ) ≠ 0, h̃ is not integrable on (1, ∞), so no L¹ assertion is possible in general.
2. **Workflow harvest at `c6ce649d`** ([partial harvest](evidence/current-codex/stage17/ci-harvest-c6ce649d-partial.json)).
   - 19 of the 22 runs on the Stage 16 record head had completed.
   - OPICA preparation, the exact-source subset, the narrow job (eighteen modules, twenty-three
     consumer files, including ExpectedSquareDefect; W01, W04/W07 and W06 steps) and the
     frozen-regression jobs pass in both the PR and the push run.
   - Fifteen of the eighteen inherited research replays pass. Three were still running and are
     superseded on this head by the next push; they are recorded as in progress,
     not as passed.
   - Only the designed fail-closed gates are red: Full release readiness (PR and push),
     opica-contract, opica-component-summary, python-rhrc and rhkg-compiler-receipt.
3. **What changed.** F3 is complete at the narrow level, and with it F1-F3. The forced resolvent of
   every off-cut parameter in the right half strip now has an explicit physical expression from the
   actual finite sums. Its only zero-dependent feature is the boundary amplitude ζ(ρ)/b_ρ.
4. **Upstream.**
   - Inputs:
     - the generic finite-sum expansion (Stage 9);
     - the Stage 11 Euler identity for every strip parameter;
     - the Stage 15 transfer, extension, quotient, uniqueness and inversion, reused unchanged and
       generalized in `log_weak_compact_of`;
     - the Stage 13 force.
   - Dependency compression (PROVED here): the resolvent side of F2 never needs ζ(ρ) = 0. The zero
     hypothesis enters only as the plateau condition A = 0.
5. **Downstream.** `Consumers.actual_force_sampling_consumer` (F1-F3) is now buildable from proved
   roots.
6. **Resurrected routes.** None.
7. **New RH-relevant clues.**
   - PROVED: the map ρ ↦ ψ_κ = nativeLogResolvent κ is ζ-defined for all off-cut κ, and "ρ is a zero"
     is equivalent to "the physical form of ψ_κ has the plateau on (0, 1)". That is exactly the paper's
     diagnostic: a homogeneous spectral proof would have to rule out the vanishing of the boundary
     functional A(ρ), not the existence of a nonreal resolvent.
   - EXPERIMENTAL SIGNAL ([numerical-falsification.log](evidence/current-codex/stage17/numerical-falsification.log)):
     at the generic parameters ρ = 0.75 + 10i and 0.6 + 3i (not zeros, κ nonreal), the transform
     𝓕_log ψ̃(ξ), computed directly from the finite sums with analytic power tails, equals
     κζ(1/2 + iξ)/(a - κ) to ≤ 3e-8 at four frequencies each.
   - This is the first numerical check of the F2 quotient off the cut; the first zeros are on the line.
   - The truncated transforms of h without the boundary term drift at the predicted scale
     \|A\| X^(Re ρ - 1/2)/\|ρ - s\|.
8. **Falsification checks.**
   - The L² growth of h versus convergence for h̃: ∫_1^200 \|h\|² = 1505 against ∫_1^200 \|h̃\|² = 108
     at ρ = 0.75 + 10i.
   - The tail residual × x³ is bounded (1.1 to 1.6).
   - Vacuity: the hypotheses are satisfiable (every ρ in the open region qualifies, with no zero
     assumption).
   - Circularity: no premise mentions h̃ or its equation.
9. **Highest-leverage next moves.**
   - `Consumers.actual_force_sampling_consumer`: compose F1-F3 with both Fourier conventions.
   - `CoPoissonJets` → `ConfluentProfiles` → `FiniteSpanSeparation` (multiplicity jets, confluent
     determinant, finite-span exclusion).
   - J5.2/MS1 (`NativeWindowRate`, `MovingSourceWindowRate`) and the remaining `Consumers`.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 17 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the published head, the 11 absent roots, RH, Step 4 and the
independent closing inequalities.
