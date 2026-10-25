# Stage 11: the forced Euler equation of the actual zero profiles (R2-S1b)

This stage starts from PR #294 head `7b156e062343e99211d65b893bed1b619d01c82d` (Stage 10). The
source commit checked here is `5b8ad4288f9ebff5c34483c1c38f8132c32bb3ff` (tree
`3114caac6900813b1ab49dc6048bb3c628358c47`). Exact hashes, commands and logs are in
[stage11 STATUS.json](evidence/current-codex/stage11/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain
OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment status
changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/ForcedEuler.lean` imports exactly
`Zeta23.OPICAFollowup.ZeroProfiles` and `Zeta23.OPICAFollowup.LogFourierSobolev`, its
BUILD_MANIFEST `direct_project_imports` list. It defines:
- `PositiveAxisTest`: smooth, compactly supported, complex-valued tests on (0, ∞);
- `eulerImage` ρ φ := -∫_0^∞ h (x² φ')', which is ⟨-(x² h')', φ⟩ with h' the distributional
  derivative;
- `zeroProfileDeriv`: the explicit cell derivative of h.

The narrow runner now builds thirteen modules and replays eighteen consumer files.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `zero_profile_forced_euler` (R2-S1b, S1.4) | At an actual zero (ζ(ρ) = 0, 0 < Re ρ < 1), for every test φ:<br>- ⟨-(x² h')', φ⟩ = κ (∫_0^∞ (h - 1) φ + Σ_{n≥1} φ(n));<br>- the a.e. derivative gives the same value ∫ x² h' φ';<br>- between integers (x² h')' = κ (1 - h);<br>- at every integer n ≥ 1, h is continuous (no derivative of a delta), and the actual jump n² (h'(n+) - h'(n-)) = -κ produces the atom κ δ_n. | [ExpectedForcedEuler.lean](consumers/ExpectedForcedEuler.lean) (10 receipts) |
| `zero_profile_not_homogeneous_operator_vector` (R2-S1b) | At an actual zero:<br>- κ ≠ 0;<br>- no function locally integrable on (0, ∞), in particular none in L²(0, ∞), represents the Euler image. So h is not in the operator domain of the L² self-adjoint realization of -∂(x² ∂);<br>- for every c ∈ ℂ the homogeneous equation -(x² h')' = c h fails;<br>- the form identity is retained: h with `zeroProfileDeriv` lies in `LogFormDomain`, and (S1.5) holds. | same file |

**Proof.**
- **Cells.** Each cell branch x^(-ρ) A_n - x^(ρ-1) B_n solves (x² g')' + κ g = 0.
- **Telescoping.** Integrating by parts on [n, n+1] against any C¹ function and summing to N+1
  telescopes. The boundary terms at an integer n combine into n²(h'(n-) - h'(n+)) = κ, using the
  Stage 9 jump lemma; the first cell is constant. This holds for every N and every C¹ function.
- **Distributional form.** A second telescoping, of h against (x² φ')' using the continuity of
  h, gives the distributional form. Compact support then removes the boundary at N+1.
- **Not a function.** The shrinking bumps φ_k at 1 have φ_k(1) = 1 and radius 1/(2(k+1)).
  Pairing them with the identity gives κ = ∫ f φ_k for f = g - κ(h - 1), which is integrable near
  1. Dominated convergence sends the right side to 0, which contradicts κ ≠ 0.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **Test functions.** "In distributions on (0, ∞)" means testing against smooth, compactly
  supported, complex-valued functions with support in (0, ∞). The Euler image uses only h
  itself (-∫ h (x² φ')'), so no choice of h' enters the distributional statement. The a.e.
  derivative form is an additional clause.
- **The atom sum.** Σ_{n≥1} δ_n acts as ∑' n, φ(n + 1). The sum is finite on every test.
- **Not an L² function.** Stated as the nonexistence of an L²(0, ∞) density, and more strongly
  of a locally integrable density.
- **No homogeneous eigenvalue inference.** Stated as the failure of -(x² h')' = c h for every
  complex c.
- **The zero premise.** The premises are the actual zero hypotheses, and ρ ≠ 1/2 is derived.
  The distributional identity and the non-function result themselves hold for every strip
  parameter ρ ≠ 1/2: see `forced_euler_identity` and `eulerImage_not_function`, exercised at
  ρ = 3/4 in the consumer. Only the retained form identity needs the zero.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for thirteen modules and eighteen
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Nine negative
controls are rejected for their intended reasons:
- force sign -κ;
- no atoms;
- atom weight κ/n²;
- continuum part h instead of h - 1;
- ordinary part κ(h - 1);
- jump +κ;
- an L² Euler image;
- the homogeneous eigenvector with c = κ;
- no zero hypothesis.

The ledger now records 41 historical, 32 narrow and 27 absent roots. This is not aggregate
acceptance of 73 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above, with the supporting results:
   - `forced_euler_identity` and `eulerImage_not_function`, for every strip ρ ≠ 1/2;
   - `profile_parts`, the telescoped integration by parts of h;
   - `euler_parts`, the telescoped ∫_0^(N+1) x² h' v' with atoms and the boundary term, for any
     C¹ function v;
   - `hasDerivAt_sq_mul_deriv_zeroProfile`, the ordinary part;
   - `zeroProfile_mem_logFormDomain`.

   All receipts are standard-only. The consumer proves:
   - an independent bump at 1 sees the atom: the Euler image minus the ordinary part equals
     exactly κ ≠ 0;
   - the jump clause equals the Stage 9 jump, and its one-sided derivatives are unique;
   - the explicit derivative is the right derivative and the a.e. derivative.
2. **Workflow harvest at `7b156e06`** ([ci-harvest-7b156e06.json](evidence/current-codex/stage11/ci-harvest-7b156e06.json)).
   All 22 runs completed; none was cancelled, in progress or queued at harvest.
   - The OPICA checkpoint (PR and push runs) passes preparation, the exact-source subset, the
     narrow candidates (twelve modules and seventeen consumer files, including
     ExpectedLogFourierSobolev, with the W01, W04/W07 and W06 steps) and the frozen regression.
   - All eighteen inherited research replays succeed. They are regression and research
     outputs, not OPICA theorem authority.
   - Only the designed fail-closed gates are red: full release readiness, the parent
     opica-contract and opica-component-summary, python-rhrc and rhkg-compiler-receipt (at the
     canonical-state validation). CI on the new head is pending at publication.
3. **What changed.** R2-S1b is complete at the narrow level: (S1.4), the non-homogeneity and
   (S1.5) are all formal for actual zero profiles. The paper rejects the inference "positive
   form, hence self-adjoint eigenvalue, hence real κ". The structural fact behind that rejection
   is now a theorem: the Euler image carries the atoms κ δ_n and is not a function.
4. **Upstream.**
   - The Stage 9 jumps and the closed-cell gluing give the atoms.
   - The Stage 10 form domain gives (S1.5).
   - Dependency compression: neither distributional statement needs the zero. Both hold for
     every strip ρ ≠ 1/2. Within R2-S1b, the zero enters only through decay at infinity, that is,
     through the form domain.
5. **Downstream.**
   - `SamplingCompatibility` (R2-S2, imports ForcedEuler only) is unblocked. Its Gram identity
     Q_ij = κ_i(N_ij + conj b_j) pairs (S1.4) with conj h_j. That is `euler_parts` with a
     piecewise-smooth function in place of a C¹ test. The boundary term (N+1)² h_i'(N+1-) h_j(N+1)
     is O(N^-2), and ∫_0^∞ h_j = 1/2 comes from Stage 9.
   - Q - N/4 ⪰ 0 follows from linearity of `LogFormDomain` and (S1.5).
6. **Resurrected routes.** None needed. The Stage 1 first-cell cost reappears as the first
   atom: at the first zero κ = 200.04 is the weight of δ_1.
7. **New RH-relevant clues (LEAD/HYPOTHESIS, not formal).**
   - The forced equation and its atoms are construction-level. Testing (S1.4) on compactly
     supported functions cannot distinguish zeros from non-zeros. Zero information can enter a
     downstream argument only through boundary behavior at infinity: the integrability of h, the
     outer boundary term of the R2-S2 pairing, and ∫_0^∞ h = 1/2.
   - LEAD: for a generic strip ρ ≠ 1/2, the R2-S2 identity should acquire exactly the boundary
     amplitude of F3 (`BoundaryAmplitude`). Formalizing it would localize where the zero
     hypothesis acts in the sampling law.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath 1.3.0, first zero, not interval certified;
     [numerical-falsification.log](evidence/current-codex/stage11/numerical-falsification.log)):
     - on three bump tests over (0.6, 3.7), (1.2, 1.9) and (2.5, 6.4), ⟨x² h', φ'⟩ =
       -⟨h, (x² φ')'⟩ = κ(⟨h - 1, φ⟩ + Σ φ(n)) to at most 7e-29;
     - dropping the atoms misses by up to 511, and the homogeneous κ⟨h, φ⟩ misses by 11 to 37;
     - on scaled bumps at 1 of radius 0.4 down to 0.004, the Euler image minus the continuum
       part equals κ = 200.04045483239 to 14 digits, while the continuum part tends to 0.
   - A first attempt used exp(-1/((x-a)(c-x))) bumps of small radius. Its quadrature failed,
     because the effective width is about r². The scaled family replaced it. That was a
     numerical artifact, not a mathematical discrepancy.
   - Vacuity: the test class is non-degenerate (an independent bump at 2). The identity and the
     non-function result are exercised at ρ = 3/4.
   - Circularity: the proof never uses ζ(ρ) = 0 except for ρ ≠ 1/2 and the retained form identity.
9. **Highest-leverage next moves.**
   - `SamplingCompatibility` (R2-S2: the Gram identity and PSD/divided differences).
   - `SawtoothForce` (F1), then the F2/F3 chain.
   - `SquareDefect` (four generic roots instantiated by `zeroProfile`).
   - `CoPoissonJets`.
   - J5.2/MS1 in parallel.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 11 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 11 head, the 27 absent roots, RH, Step 4 and the
independent closing inequalities.
