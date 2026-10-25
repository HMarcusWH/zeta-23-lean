# Stage 9: the actual zero profiles (R2-S1a)

This stage starts from PR #294 head `eacba23fd9d7d8b4e5f27c8d4ccf1df864572614` (Stage 8).
The source commit checked here is `b67ab3f74730f07b0ddbcef6e27214b3e6fb8228` (tree
`609536bfbdd3a502a756897ecfebdfb1381e7648`). Exact hashes, commands and logs are in
[stage9 STATUS.json](evidence/current-codex/stage9/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain
OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment status
changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/ZeroProfiles.lean` imports exactly
`Zeta23.OPICAFollowup.RenormalizedCoPoisson` and `Zeta23.OPICAFollowup.ProfileEulerMaclaurin`.
That is its BUILD_MANIFEST `direct_project_imports` list. Both required definitions exist:
`spectralKappa` (kappa = rho(1 - rho)) and `zeroProfile` (h = 1 - S_rho(\|x\|)/b_rho), built from
the frozen CP1 finite sums `finiteSumSrho` and `normalizationBrho`. The narrow runner now builds
eleven modules and replays sixteen consumer files.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `zero_profile_regular_selfdual` (R2-S1a) | At an actual zero (zeta(rho) = 0, 0 < Re rho < 1), h is even, continuous, in L^1 and L^2, and equal to 1 on [-1, 1]. It is Fourier self-dual as an ordinary L^1 function (F h = h, Mathlib F) and on Schwartz pairings. int h = h(0) = 1, the half-line integral is 1/2, and the Stage 7 zero measure satisfies nu = (dx + delta_0 - D_0) - h dx on Schwartz tests. | [ExpectedZeroProfiles.lean](consumers/ExpectedZeroProfiles.lean) (11 receipts) |
| `zero_profile_tail_and_jumps` (R2-S1a) | At an actual zero:<br>- h = kappa B2({x})/(2x^2) + O(x^-3) for \|x\| >= 1;<br>- the exact differentiated finite sums give h' in every cell, with h' = O(x^-2) between integers, leading term kappa B1({x})/x^2 and remainder O(x^-4);<br>- at every integer n >= 1 the unique one-sided derivatives jump by -kappa/n^2, and h'(1-) = 0;<br>- x h' is in L^2(0, oo). | same file |

**Proof.**
- **Expansion.** Stage 8's expansion, applied at s = rho and s = 1 - rho, gives the exact identity
  S_rho = zeta(1-rho) x^(-rho) - zeta(rho) x^(rho-1) + b_rho + (2rho-1) B2/(2x^2) + E with
  E = O(x^-3). The two zeta terms vanish at a zero; Mathlib's functional equation gives
  zeta(1 - rho) = 0.
- **Derivative.** Inside each cell, S_rho is the smooth branch x^(-rho) A_n - x^(rho-1) B_n with
  constant cell sums. Differentiating that exact branch and inserting both expansions gives
  S' = (2rho-1) B1({x})/x^2 + O(x^-4): the 1/x and B2/x^3 terms cancel identically.
- **Jumps.** The two branches agree at every integer, so S is continuous there. Their
  derivatives differ by (1 - 2rho)/n^2, and dividing by b_rho = (1-2rho)/kappa gives the jump.
- **Self-duality.** The pairing identity comes from the Stage 7 zero measure, Fourier inversion
  for the Lebesgue functional and Poisson summation for the comb. The multiplication formula
  int F h phi = int h F phi and uniqueness against smooth compactly supported tests then give
  F h = h pointwise. Evaluating at 0 gives int h = 1, and evenness gives the half-line value.

**Recorded formalization choices (no premise added, no domain narrowed).**

- The only premises are zeta(rho) = 0 and 0 < Re rho < 1. The condition rho != 1/2, which b_rho
  != 0 needs, is derived: zeta is negative on the real segment (0, 1) (parent
  `riemannZeta_ne_zero_of_real_critical_strip`). The Stage 7 zero-measure root still lists
  rho != 1/2 as a premise. That premise is redundant, not a narrowing.
- "Fourier-self-dual" is proved in its strongest ordinary sense, F h = h for the L^1 continuous
  function, together with the Schwartz-pairing form.
- "h'(n+) - h'(n-)": one-sided derivatives within [n, oo) and (-oo, n]. They are unique, and the
  consumer proves that any such derivatives satisfy the jump identity. "h' between integers" is
  the exact cell derivative. The L^2 clause uses `deriv h`, which equals the cell derivative off
  the null set of integers. The positive half-line is stated; evenness gives the negative side.
- "Actual zeta zero and functional equation used": the zero enters the self-duality (through the
  zero measure) and the tail; the functional equation enters through zeta(1 - rho) = 0, which
  integrability needs.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for eleven modules and sixteen
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Nine negative
controls are rejected for their intended reasons:
- tail sign -kappa;
- tail exponent -4;
- jump +kappa/n^2;
- h'(1-) = 1;
- plateau [-2, 2];
- anti-self-duality;
- half-line integral 1;
- no zero hypothesis;
- closed strip Re rho <= 1.

The ledger now records 41 historical, 28 narrow and 31 absent roots. This is not aggregate
acceptance of 69 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above, with the supporting
   `finiteSumSrho_expansion` (S1a identity for every strip parameter), `srhoCellDeriv_expansion`,
   `srhoCellDeriv_jump`, `continuous_zeroProfile` (no zero needed), `zeroProfile_pairing` and
   `fourier_zeroProfile`. All receipts are standard-only. The consumer additionally proves:
   - h is one minus the actual zero-measure density on the whole line;
   - h(0) = F h(0) = int h = 1;
   - the one-sided derivatives in the jump clause are unique;
   - the lattice values h(n) are absolutely summable.
2. **Workflow harvest at `eacba23f`** ([ci-harvest-eacba23f.json](evidence/current-codex/stage9/ci-harvest-eacba23f.json)).
   - **OPICA follow-up** (PR run 39995156643 and push run 39995145005): preparation,
     exact-source subset, narrow candidates (all fifteen consumer files including
     ExpectedEulerMaclaurin, runner exit 0) and frozen regression PASS. Full release readiness
     FAIL, as designed.
   - **Parent and RHRC checks:** parent `opica-contract` and `opica-component-summary` FAIL,
     unchanged; `opica-regression` PASS; `opica-formal` and `opica-dependency-delta` are skipped.
     `python-rhrc` FAIL, and `rhkg-compiler-receipt` FAIL at the canonical-state validation, both
     pre-existing. `lean` and `r003-normalization-audit` PASS.
   - **Inherited research replays:** all eighteen PASS, the post-284 campaign last (completed
     19:13Z). None of the 22 runs was cancelled. They create no OPICA theorem authority.
3. **What changed.** This is the first R2 spectral-lane module. The zero profile is now an actual
   L^1 and L^2 Fourier self-dual function, with its tail, cell derivatives and jumps, not only a
   measure. Continuity holds for every parameter. Integrability is where the zero enters.
4. **Upstream.**
   - Stage 8's expansion is used at both specializations.
   - The Stage 7 zero-measure self-duality is used for the pairings, and the historical
     `dilated_comb_fourier` for Poisson summation.
   - Dependency compression: the parent real-segment nonvanishing theorem removes the rho != 1/2
     premise, and the same argument would simplify the Stage 7 root.
5. **Downstream.**
   - `ForcedEuler.zero_profile_forced_euler`. Inside each cell the branches solve the Euler
     equation (x^2 g')' + kappa g = 0, since the exponents -rho and rho-1 solve
     a(a+1) + kappa = 0. The jump of x^2 h' is n^2 (-kappa/n^2) = -kappa at every integer, which
     gives the atoms kappa delta_n. All ingredients now exist formally, but the module must also
     import `LogFourierSobolev`, which is still absent.
   - `CoPoissonJets` (imports ZeroProfiles only) and `SquareDefect` (imports ZeroProfiles and
     the parent `Involution`) are now unblocked by imports. SquareDefect's roots are generic in an
     even continuous self-dual h in L^1 and L^2 with a plateau, and `zeroProfile` is an actual
     instance.
6. **Resurrected routes.**
   - The Stage 7 DERIVED tail is now formal at second order.
   - The Stage 1 first-cell negative-mass cost connects directly: at the first zero, h(1.7) is
     about -9.18 (mpmath), so the profile is strongly negative in the first cell where
     kappa = 200.04 dominates.
7. **New RH-relevant clues (LEAD/HYPOTHESIS, not formal).**
   - DERIVED (informal; the converse is not formalized): for 0 < Re rho < 1 and rho != 1/2, the
     profile is in L^1 iff zeta(rho) = 0. Off zeros, the exact S1a identity leaves
     -[zeta(1-rho) x^(-rho) - zeta(rho) x^(rho-1)]/b_rho. Its terms decay like x^(-sigma) and
     x^(sigma-1), which is not integrable for 0 < sigma < 1. On the line the two terms have equal
     modulus but distinct frequencies x^(-+i gamma), so they cannot cancel. This is a second
     zero-detection mechanism, alongside Stage 7's bounded density at the origin. LEAD:
     formalize the converse as "integrability detects zeros".
   - kappa is real exactly on the critical line, so h is real-valued only for on-line zeros. For
     the first zero h is a real, even, self-dual function equal to 1 on [-1, 1] that takes large
     negative values in the first cell. As in the paper, a positivity target for h fails, and no
     separation of on-line from off-line zeros follows.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath 1.3.0, first zero, not interval certified;
     [numerical-falsification.log](evidence/current-codex/stage9/numerical-falsification.log)):
     - F h(xi) = 2 int_0^oo h cos(2 pi x xi) matches h(xi) to <= 1.5e-8 at xi = 0.4, 1.7, 3.25, 6.6
       (truncation 600 cells);
     - int_0^600 h = 0.4999999949;
     - finite-difference jumps at n = 1, 3, 10 match -kappa/n^2 to eight digits;
     - x^3 \|h - kappa B2/(2x^2)\| stays in [2.5, 9.6] for x in [5.5, 300].
   - Vacuity: Mathlib exhibits no explicit zero, so the zero-dependent clauses cannot be
     instantiated. The construction-level clauses (continuity, evenness, plateau, cell
     derivatives, jump formula) are exercised at rho = 3/4 in the consumer. A negative control
     rejects the tail without the zero hypothesis.
   - Boundary: S(1) = 0, so h(+-1) = 1, consistent with the plateau. h is constant near 0. The
     left derivative at 1 is exactly 0, and the first jump is -kappa.
   - Circularity: the zero hypothesis enters only through the CP1.7 cancellation in the zero
     measure and through zeta(1 - rho) = 0. Fourier self-duality uses only Poisson summation and
     Fourier inversion beyond that.
9. **Highest-leverage next moves.**
   - `LogFourierSobolev` (log-unitary form identity and Plancherel). It unblocks `ForcedEuler`,
     whose first root is now mostly assembled, and `SawtoothForce`.
   - `SquareDefect`: four generic roots instantiated by `zeroProfile`.
   - `CoPoissonJets.copoisson_zero_jets_measures` by parameter differentiation (Stage 8 item 5).
   - J5.2/MS1 and R2-S3 in parallel.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 9 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 9 head, the 31 absent roots, RH, Step 4 and the
independent closing inequalities.
