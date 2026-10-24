# Stage 8: the finite-sum Euler-Maclaurin expansion (R2-S1a, R2-H1, F3)

This stage starts from PR #294 head `d58f536aaec51726d5b3341926b183931d4523ad` (Stage 7).
The source commit checked here is `e2903338a04689d65ec91ef4fb73616937055f24` (tree
`ce889f8c256c2c39ade1eac9a36df6b4bad6ea77`). Exact hashes, commands and logs are in
[stage8 STATUS.json](evidence/current-codex/stage8/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain
OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment status
changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/ProfileEulerMaclaurin.lean` imports only Mathlib modules.
That matches its BUILD_MANIFEST entry, whose `direct_project_imports` list is empty. Both
required definitions, `bernoulliOneRight` and `bernoulliTwo`, exist. The narrow runner now
builds ten modules and replays fifteen consumer files.

## Completed narrow gate (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `finite_sum_euler_maclaurin_uniform` (R2-S1a, R2-H1, F3) | For 0 < Re s, s != 1 and every real cutoff x >= 1: sum_(1<=n<=x) n^(-s) = zeta(s) + x^(1-s)/(1-s) - B1({x}) x^(-s) - s B2({x}) x^(-s-1)/2 + R(s,x). The sum keeps the right integer endpoint, and B1 = -1/2 and B2 = 1/6 at integers. The remainder has the explicit bound \|R(s,x)\| <= (\|s\|(\|s\|+1)/6 + \|s\|(\|s\|+1)(\|s\|+2)/12) x^(-Re s - 2) for all x > 0. One constant works on every compact parameter set, R(., x) is holomorphic in s, and the exact differentiated finite sums hold inside every cell. | [ExpectedEulerMaclaurin.lean](consumers/ExpectedEulerMaclaurin.lean) (10 receipts) |

**Proof (no imported formula).**
1. Abel summation (`sum_mul_eq_sub_integral_mul₀`) gives the exact first-order identity for
   every real x >= 1.
2. For Re s > 1, letting x -> oo along the integers proves
   zeta(s) = s/(s-1) - 1/2 - s int_1^oo B1({t}) t^(-s-1) dt from the Dirichlet series. The
   right side is a Mellin transform of a bounded function, so it is holomorphic on Re s > 0.
   The identity theorem on the star-convex domain {Re s > 0, s not in [1, oo)} extends the
   identity to that domain. The real points s > 1 are already covered by the Re s > 1 case,
   so the identity holds on all of 0 < Re s, s != 1.
3. Two integrations by parts on (x, oo) against the continuous periodic B2/2 and B3/3, whose
   right derivatives are B1 and B2, give the second-order expansion and the explicit remainder
   R(s,x) = -(s(s+1)/6) B3({x}) x^(-s-2) + (s(s+1)(s+2)/6) int_x^oo B3({t}) t^(-s-3) dt.

**Recorded formalization choices (no premise added, no domain narrowed).**

- Parameter domain 0 < Re s, s != 1. It contains the open critical strip, so it covers both
  specializations s = rho and s = 1 - rho in R2-S1a and every compact parameter disk inside the
  strip in R2-H1. The cutoff domain x >= 1 is "uniformly across real cutoffs". On 0 < x < 1 the
  finite sum is empty and the expansion is not claimed; a negative control rejects that use.
- "O_s(x^(-Re s - 2)), locally uniformly": an explicit constant polynomial in \|s\|, valid for
  all x > 0. As a separate clause, one constant works for all s in a compact subset of the
  domain and all x >= 1. The constant is uniform on bounded sets, **not in the height**. See
  the falsification checks below.
- "Including differentiated finite sums" (BUILD_SPEC module text; the S1a proof's "exact
  differentiated finite sums, not an unspecified big-O remainder"): the finite sum has
  derivative 0 inside every open cell (n, n+1), and the remainder has the exact cell derivative
  -(s(s+1)/2) B2({x}) x^(-s-2). Holomorphy of R(., x) is included so that parameter jets
  (R2-H1) follow by Cauchy estimates. No parameter-derivative bound is stated in the root.
- zeta is Mathlib's `riemannZeta`. The Bernoulli continuation formula is proved, not assumed.
  The module uses no functional equation.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for ten modules and fifteen
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Eight negative
controls are rejected for their intended reasons:
- B1 at integers +1/2 (left endpoint);
- the left-closed sum over [1, n);
- sign +B1;
- B2 coefficient s instead of s/2;
- remainder exponent -Re s - 3;
- closed half-plane Re s >= 0;
- the divergent Dirichlet tsum in place of zeta;
- cutoff 0 < x.

The ledger now records 41 historical, 26 narrow and 33 absent roots. This is not aggregate
acceptance of 67 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The root above, with the supporting
   `rightPowerSum_abel`, `zeta_eq_bernoulli`, `integral_Ioi_parts`, `rightPowerSum_expansion`,
   `eulerMaclaurinRemainder_norm_le` and the cell-derivative lemmas. All receipts are
   standard-only. The consumer proves four further statements that bind the root to the
   actual objects:
   - `expected_srho_expansion`: for every strip parameter and x >= 1, the actual CP1
     `finiteSumSrho` equals
     zeta(1-rho) x^(-rho) - zeta(rho) x^(rho-1) + b_rho + (2rho-1) B2({x})/(2x^2)
     + x^(-rho) R(1-rho,x) - x^(rho-1) R(rho,x).
     The two B1/x terms cancel exactly.
   - `expected_srho_tail_at_zero`: at an actual zero, with zeta(1-rho) = 0 from Mathlib's
     functional equation, S_rho(x) = b_rho + (2rho-1) B2({x})/(2x^2) + O(x^-3) uniformly for
     x >= 1, with the constant explicit in \|rho\|.
   - `expected_right_endpoint_jump`: crossing the integer n adds exactly n^(-s).
   - `expected_isBigO`: the paper's O-form for every fixed parameter.
2. **Workflow harvest at `d58f536a`** ([ci-harvest-d58f536a.json](evidence/current-codex/stage8/ci-harvest-d58f536a.json)).
   - **OPICA follow-up** (PR run 39984091212 and push run 39984084215): preparation,
     exact-source subset, narrow candidates (all fourteen consumer files, runner exit 0) and
     frozen regression PASS. Full release readiness FAIL, as designed.
   - **Parent and RHRC checks:** parent `opica-contract` and `opica-component-summary` FAIL,
     unchanged from earlier heads; `opica-regression` PASS; `opica-formal` and
     `opica-dependency-delta` are skipped. `python-rhrc` FAIL, and `rhkg-compiler-receipt` FAIL
     at the canonical-state validation, both pre-existing. `lean` and
     `r003-normalization-audit` PASS.
   - **Inherited research replays:** all eighteen PASS, including the post287 WP2/WP4 interval
     research (completed 17:02Z) and the post-284 campaign (completed 17:17Z). None of the 22
     runs was cancelled. They create no OPICA theorem authority.
3. **What changed.** The profile chain now has its analytic foundation. The parent PNT+ port
   already supplied the first-order form (CP1.6, used in Stage 7 through `Zeta0EqZeta`). This
   module is an independent, Mathlib-only second-order derivation, so the CP1 module and the
   profile modules do not share a proof dependency. Both are formal and agree on `riemannZeta`.
   The BUILD_MANIFEST import lists keep them separate, so no dependency compression was
   attempted: RenormalizedCoPoisson may import only DilatedComb.
4. **Upstream.**
   - PROVED (consumer): the Stage 7 DERIVED statement "S_rho - b_rho = O(1/y) at zeros" is now
     a formal second-order statement with the explicit B2 term.
   - DERIVED (informal): in the identity of item 1, the zeta(1-rho) x^(-rho) and
     zeta(rho) x^(rho-1) terms are the only parts of order slower than x^-2. At a zero, where
     both vanish, the first correction to b_rho is a lattice-periodic function times x^-2. This is
     the Euler-Maclaurin form of the CP1 observation that zeta(rho) = 0 iff the measure has a
     bounded density at the origin.
5. **Downstream.**
   - `zero_profile_tail_and_jumps`: h = 1 - S_rho/b_rho and (2rho-1)/b_rho = -kappa, so
     `expected_srho_tail_at_zero` is literally h = kappa B2({x})/(2x^2) + O(x^-3).
   - DERIVED (informal): inside a cell, the derivative of S_rho is computed from the exact
     finite sums (constant in the cell) and the expansions of both sums. This gives
     h'(x) = kappa B1({x})/x^2 + O(x^-3). That form proves h' = O(x^-2) and x h' in L^2(1, oo).
     The jump of B1 at every integer is -1, which reproduces the paper's
     h'(n+) - h'(n-) = -kappa/n^2 (S1.2) from the Euler-Maclaurin side. It agrees with the
     direct finite-sum computation of the jump and is consistent with B2' = 2 B1.
   - `copoisson_zero_jets_measures` (R2-H1), DERIVED (informal): x^(s+2) R(s,x) is holomorphic
     in s and bounded by C uniformly on a compact disk (root clauses 4 to 6). Cauchy estimates
     then give d_s^k R = O(x^(-Re s - 2) (1 + log x)^k) with jet-dependent constants. At zeros
     the remainder contributes O(x^-3 log^k x), and the zeta terms vanish through the actual
     multiplicity. So each higher density is O(x^-2), as H1 states, and the root as stated is
     sufficient for the H1 Euler-Maclaurin step.
   - `SawtoothForce` and `BoundaryAmplitude` also import this module. Their remaining
     dependencies are `LogFourierSobolev` and `NativeResolvent`.
6. **Resurrected routes.** The first-order CP1.6 step proved in Stage 7 (`partialZeta_error`)
   and the derived O(1/y) tail now have their second-order completion. The Stage 6 and 7
   density-plus-atom and complex-variation tools are what ZeroProfiles will reuse.
7. **New RH-relevant clues (LEAD/HYPOTHESIS, not formal).**
   - The universal tail coefficient of the zero profile is kappa = rho(1-rho) =
     sigma - sigma^2 + gamma^2 + i gamma(1 - 2 sigma). It is real exactly when sigma = 1/2
     (gamma != 0). The leading tail kappa B2/(2x^2) and the jump -kappa/n^2 are therefore real
     and lattice-periodic only on the critical line. This is the paper's own S1 structure: it
     is a reformulation, not new leverage. The paper warns that kappa is not an eigenvalue of a
     self-adjoint problem, because the lattice force is retained.
   - EXPERIMENTAL SIGNAL: the remainder is not uniform in height. At x = 1 and s = 0.3 + 14i,
     \|R\| = 1.41 (mpmath). The expansion is only quantitatively useful for x >> \|gamma\|, the
     scale of the classical approximate functional equation. Any argument that needs
     uniformity over all zeros must supply that scale separately.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath 1.3.0;
     [numerical-falsification.log](evidence/current-codex/stage8/numerical-falsification.log),
     not interval certified):
     - The identity holds to the tail-truncation error (<= 3e-9) at five parameters,
       including heights 14 and 21.02 and s = 2, and at five cutoffs.
     - The cutoffs include x = 10 and x = 10 - 1e-12 on the two sides of an integer.
     - The left-closed convention misses by 0.50 at x = 10.
     - R(1/2, 1) matches 1 - zeta(1/2) - 5/2 + 1/24 to ten digits.
     - At the first actual zero, x^3 \|S_rho - b_rho - (2rho-1)B2/(2x^2)\| stays in
       [0.36, 1.35] for x in [5.5, 300].
   - Sharpness (EXPERIMENTAL SIGNAL): at non-integer cutoffs, R x^(Re s + 2) tends to
     -(s(s+1)/6) B3({x}), which is not 0 (for example 5.3e-3 at s = 1/2, x = 23.3). The
     exponent -Re s - 2 cannot be improved, and a negative control rejects -Re s - 3.
   - Boundary: x = 1 is exercised exactly (`expected_nonvacuous_half`). At integers B3 = 0 and
     the leading remainder term vanishes, which is consistent with the smaller values there.
     s = 1 is excluded from the identity but not from the bound clause. The remainder stays
     bounded near s = 1 because the poles of zeta(s) and x^(1-s)/(1-s) cancel. The harmonic-sum
     expansion at s = 1 is not claimed.
   - Circularity: the module uses no functional equation and no parent zeta bound. The consumer
     uses Mathlib's `riemannZeta_one_sub` only for zeta(1-rho) = 0.
9. **Highest-leverage next moves.**
   - `ZeroProfiles` (imports RenormalizedCoPoisson and ProfileEulerMaclaurin, both now
     available):
     - `zero_profile_tail_and_jumps` from `expected_srho_tail_at_zero`, the cell derivative
       above and the CP1 jump computation;
     - `zero_profile_regular_selfdual` from the Stage 7 zero measure
       (nu = dx + delta_0 - D_0 - h dx) and the L^1 tail.
   - `CoPoissonJets.copoisson_zero_jets_measures` by the Cauchy-estimate route of item 5.
   - In parallel: `LogFourierSobolev` (unblocks `ForcedEuler` and `SawtoothForce`), J5.2/MS1
     and R2-S3.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 8 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 8 head, the 33 absent roots, RH, Step 4 and the
independent closing inequalities.
