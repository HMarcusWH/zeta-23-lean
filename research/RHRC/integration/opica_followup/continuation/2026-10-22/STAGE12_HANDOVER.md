# Stage 12: the native multi-zero sampling compatibility law (R2-S2)

This stage starts from the Stage 11 record `b9627cc1e76c7e4541cf86de8d79d31acda8f7d5`. The
source commit checked here is `7b81e03b4f231be0581cde6a4871fb456577a1c8` (tree
`a9d71e91e0377d89fec860422df0dac981de77d3`). Exact hashes, commands and logs are in
[stage12 STATUS.json](evidence/current-codex/stage12/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain
OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment status
changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/SamplingCompatibility.lean` imports exactly
`Zeta23.OPICAFollowup.ForcedEuler`, its BUILD_MANIFEST `direct_project_imports` list. It defines
the three required definitions, with pairings linear in the first argument:
- `profileGram` ρ σ := ∫_0^∞ h_ρ conj h_σ (the paper's N);
- `profileFormGram` ρ σ := ∫_0^∞ x² h_ρ' conj h_σ' (the paper's Q, with h' = `deriv`);
- `profileSample` ρ := Σ_{n≥1} h_ρ(n) (the paper's S), and `profileSampleDefect` = S - 1/2 (b).

It also defines `controlVector`, the paper's auxiliary finite-dimensional control. The narrow
runner now builds fourteen modules and replays nineteen consumer files.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `native_sampling_gram_identity` (R2-S2, S2.1) | For any family of actual zeros (ζ(ρ_i) = 0, 0 < Re ρ_i < 1):<br>- every sample series Σ h_i(n) is summable, both pairings are integrable on (0, ∞), and ∫_0^∞ h_i = 1/2;<br>- the pairing of (S1.4) with conj h_j on [0, N + 1] equals κ_i (∫ (h_i - 1) conj h_j + Σ_{m<N} conj h_j(m + 1)) plus the explicit boundary term (N+1)² h_i'((N+1)-) conj h_j(N+1), and that term tends to 0;<br>- Q_ij = κ_i (N_ij + conj b_j) = conj κ_j (N_ij + b_i). | [ExpectedSamplingCompatibility.lean](consumers/ExpectedSamplingCompatibility.lean) (11 receipts) |
| `native_sampling_form_positive` (R2-S2, S2.2-S2.4) | For any finite family of actual zeros:<br>- N, Q and Q - N/4 are positive semidefinite (hence Hermitian);<br>- the undivided identity (κ_i - conj κ_j) N_ij = conj κ_j b_i - κ_i conj b_j holds always, including at conjugate coincidence;<br>- the divided difference N_ij/(κ_i conj κ_j) = (M_i - conj M_j)/(κ_i - conj κ_j), M = b/κ, holds only when κ_i - conj κ_j ≠ 0;<br>- when Im κ_i ≠ 0, Im M_i / Im κ_i = N_ii/\|κ_i\|² with N_ii > 0. | same file |

**Proof.**
- **Pairing.** The Stage 11 cell integration by parts is generalized from C¹ tests to a second
  factor that is smooth on each closed cell (`cell_parts_branch`, `euler_parts_branch`). Applied
  to conj h_j, it telescopes to the finite identity `gram_finite`, where the Stage 9 jumps produce
  the atoms conj h_j(n).
- **Boundary.** The boundary term is O(N^-2): h_i' = O(x^-2) from Stage 9 and h_j(N+1) → 0.
- **Limit.** Passing N → ∞ uses the integrability of both pairings (h ∈ L², x h' ∈ L²), the
  summability of the samples and ∫_0^∞ h_j = 1/2. This gives the first form; the second follows
  from Hermitian symmetry of N and Q.
- **Positivity.** N and Q are integral Gram matrices. For Q - N/4, the quadratic form at c is the
  log form of H = Σ conj(c_i) h_i minus ‖H‖²/4. Finite combinations stay in `LogFormDomain`
  (`logFormDomain_sum`), so the Stage 10 form identity turns the form into ∫ \|ψ_H'\|² ≥ 0.
- **Algebra.** (S2.2) is the difference of the two forms of (S2.1). (S2.3) divides (S2.2) by a
  nonzero denominator. (S2.4) is the imaginary part of the diagonal of (S2.2), with N_ii ≥ 1
  because h = 1 on (0, 1).

**The finite countercontrol (paper, after Theorem S2).** For a positive real diagonal A, a real
vector g and nonreal κ_i, `finite_countercontrol` proves:
- h_i = κ_i (A - κ_i I)^(-1) g with b_i = g* h_i satisfies (S2.1), (S2.2) and (S2.3);
- its Gram matrices N_ij = ⟨h_i, h_j⟩ and Q_ij = ⟨A h_i, h_j⟩ are positive semidefinite.

The consumer exercises it with A = 1, g = 1 and κ = i, where N_00 = 1/2. It is an auxiliary
control, not a zeta system. It rejects only the inference from positivity and the displayed
identities to real parameters.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **Families.** The paper chooses one representative per distinct κ_i. The theorems hold for every
  family (finite for the matrix statements), so duplicates are allowed and nothing is narrowed.
- **Linear-first convention.** It is explicit in all three definitions. b_j enters (S2.1)
  conjugated, and the second form carries conj κ_j.
- **Derivative.** Q uses Mathlib's `deriv`. It agrees almost everywhere with the explicit cell
  derivative `zeroProfileDeriv`, and the finite pairing is stated with the cell derivative.
- **Positivity.** "Positive semidefinite Hermitian" is `Matrix.PosSemidef`, which includes the
  Hermitian property.
- **Division.** The divided difference carries the hypothesis κ_i - conj κ_j ≠ 0. (S2.4) carries
  Im κ_i ≠ 0. No division by a vanishing imaginary part occurs.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for fourteen modules and nineteen
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Ten negative
controls are rejected for their intended reasons:
- an unconjugated sample κ_i (N + b_j);
- an unconjugated κ_j in the second form;
- S instead of b = S - 1/2;
- half-line integral 1;
- boundary limit κ instead of 0;
- Q - N/2;
- the divided identity without its hypothesis;
- the S2.4 sign -N/\|κ\|²;
- no zero hypothesis;
- the finite control without nonreal parameters.

The ledger now records 41 historical, 34 narrow and 25 absent roots. This is not aggregate
acceptance of 75 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above, with the supporting results:
   - `gram_finite`, the finite-cell pairing, for every strip ρ ≠ 1/2;
   - `gram_boundary_tendsto` and `gram_identity`;
   - `posSemidef_gram` and `posSemidef_finite_gram`;
   - `logFormDomain_sum`;
   - `finite_countercontrol`.

   All receipts are standard-only. The consumer proves:
   - the diagonal: N_ii > 0 is real and Q_ii - N_ii/4 is real and nonnegative;
   - at a zero on the critical line (κ real), the self-pairing forces b real;
   - conjugate coincidence: conj ρ is an actual zero with κ(conj ρ) = conj κ(ρ), the divided
     identity is unavailable for that pair, and the retained undivided identity gives
     b_ρ = conj b_(conj ρ);
   - the finite pairing is construction-level, exercised at ρ = 3/4 and σ = 2/3;
   - the countercontrol is non-vacuous with a nonreal parameter.
2. **Workflow harvest.** The latest completed harvest is the Stage 10 head `7b156e06`
   ([stage11 harvest](evidence/current-codex/stage11/ci-harvest-7b156e06.json)). All OPICA
   preparation, subset, narrow and regression jobs pass there, as do all eighteen research
   replays. Only the designed fail-closed gates are red. CI on the Stage 11 head `b9627cc1` was
   in progress when this record was written and is harvested with the next stage.
3. **What changed.** R2-S2 is complete at the narrow level. The actual profile chain R2-S1a
   (Stage 9), R2-S1b (Stages 10 and 11) and R2-S2 (this stage) is now formal for actual zeros.
   The paper's rejection of the automatic spectral-exclusion inference is now a theorem pair: the
   native law, and a finite system that satisfies the same law with nonreal parameters.
4. **Upstream.**
   - Stage 11's cell integration by parts carries over to piecewise-smooth second factors with no
     new analysis.
   - Stage 9 supplies the decay, the jumps and ∫ h = 1/2. Stage 10 supplies Q - N/4.
   - Dependency compression: the finite identity `gram_finite` needs only a strip ρ ≠ 1/2. The
     zero hypothesis enters only through convergence at infinity (summability, integrability,
     the vanishing boundary term and ∫ h = 1/2). This matches the Stage 11 LEAD.
5. **Downstream.**
   - `NativeResolvent` (F2) imports `SamplingCompatibility` and `WeightedSpectralMeasure`.
   - `Counterexamples` imports `SamplingCompatibility`. Its finite countercontrol can reuse
     `finite_countercontrol` instead of restating it.
6. **Resurrected routes.** None needed. The paper's falsification of the spectral-exclusion
   inference is now formal.
7. **New RH-relevant clues.**
   - DERIVED (informal, two lines from the formal results): with D = diag(1/κ_i), D N D* ⪰ 0 and
     (S2.3) make the matrix [(M_i - conj M_j)/(κ_i - conj κ_j)] positive semidefinite for any
     finite family of zeros in one open half-plane of the κ plane. That is a Nevanlinna-Pick
     matrix: the data (κ_i, M_i) satisfy Pick's interpolation condition. F2 names the candidate
     interpolant, the Stieltjes function M(κ) = ∫ dω/(a - κ) with dω = \|ζ(1/2+iξ)\|² dξ/(2π)
     and a = ξ² + 1/4. Its Pick kernel is the L²(ω) Gram matrix of 1/(a - κ_i), and F2 claims
     b = κ M(κ).
   - Falsification of the clue as an exclusion tool: the finite countercontrol has M_i =
     g*(A - κ_i)^(-1) g, a Nevanlinna function with nonreal κ_i. Pick positivity therefore
     cannot by itself exclude off-line zeros, so the clue is structural and not closing.
   - EXPERIMENTAL SIGNAL (not a gate; [f2-consistency.log](evidence/current-codex/stage12/f2-consistency.log)
     and [f2-norms.log](evidence/current-codex/stage12/f2-norms.log)). The paper's remark after
     (F2.5) says the F2 formulas extend to actual critical-line zeros through removable quotients.
     Numerically, against this stage's R2-S2 values:
     - at cutoff X = 800, κ M(κ) is 12.899689 and 6.184141 at the first two zeros, against the
       sampled b = 12.899687 and 6.184275. The relative gap shrinks from 1e-3 and 4e-3 at X = 200
       to 2e-7 and 2e-5 at X = 800;
     - at X = 400, \|κ\|² ∫ dω/(a - κ)² = 73.68102 and \|κ\|² ∫ a dω/(a - κ)² = 17319.83, against
       N_11 = 73.68139 and Q_11 = 17319.72.

     This supports, but does not prove, that the R2-S2 Gram data are the L²(ω) Gram data of the
     functions κ_i/(a - κ_i). F2 would then identify the source measure behind R2-S2, as the paper
     states for the off-line case.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath 1.3.0, first two zeros, not interval certified;
     [numerical-falsification.log](evidence/current-codex/stage12/numerical-falsification.log)):
     - with cutoffs L = 200 and 400 (Hurwitz-zeta tail for Q), max \|Q_ij - κ_i(N_ij + conj b_j)\|
       is 2.4e-4 and 3.2e-5, relative about 2e-9 and 3e-10, decaying like L^-3;
     - N_ii > 0 and Q_ii - N_ii/4 > 0, and the divided difference agrees to 10 digits;
     - dropping -1/2 misses by exactly \|κ_1\|/2 = 100.02;
     - on-line zeros have real κ and b, so the conjugations are not numerically visible there.
       They are covered by the negative controls and the conjugate-coincidence consumer;
     - the countercontrol with three nonreal κ satisfies (S2.1) to 1.2e-20, with positive Gram
       eigenvalues;
     - at the non-zero ρ = 3/4 the sample partial sums grow like 1.72 L^(3/4), matching
       (4/3) ζ(3/4)/b. Without the zero there is no sampling law.
   - Vacuity: the theorems need actual zeros, which Mathlib cannot exhibit. The finite pairing
     and the countercontrol are exercised on explicit parameters. The diagonal consumer does not
     depend on a particular zero.
   - Circularity: no premise states a Gram identity or positivity. Everything is derived from the
     actual profile and the actual zero hypotheses.
9. **Highest-leverage next moves.**
   - `SawtoothForce` (F1), already proved in scratch, then `WeightedSpectralMeasure` and
     `NativeResolvent` (F2). The b = κ M(κ) identity is the formal version of the Pick clue.
   - `SquareDefect` (R2-S3), also proved in scratch.
   - `CoPoissonJets` and J5.2/MS1 in parallel.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 12 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 11 and Stage 12 heads, the 25 absent roots, RH,
Step 4 and the independent closing inequalities.
