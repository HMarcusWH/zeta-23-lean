# Stage 5: HT2 controlled limit and CT1 normalized distributional limit

This stage starts from PR #294 head `6a2e20b2ef7f16db9beb2f394a47b23bcbad2515` (Stage 4).
The source commit checked here is `0cb2abec41e97708d6969033ff219a180ff65faa`
(tree `94ac77583b5ab6465a74e53e7f438ef7ed0a36d4`); exact hashes, commands and logs are in
[stage5 STATUS.json](evidence/current-codex/stage5/STATUS.json). All 100 original roots and
28 acceptance units remain required. RH, Step 4 and the independent closing inequalities
remain OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment
status changed. The only import change is the Mathlib helper
`Mathlib.Analysis.Normed.Group.Tannery` in `NearGapLimits.lean` (frozen revision; recorded in
the source receipt as BUILD_SPEC requires).

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `near_gap_controlled_limit_zero` (R1-HT2) | Locally finite real Jordan pairs with one common linear total-variation constant, canonical Fourier self-duality, off-lattice nonnegativity and near gaps a_n in (0,1], a_n -> 1: every Schwartz pairing tends to 0. No evenness premise (derived by `jordan_even_of_selfdual`). | [ExpectedNearGapLimit.lean](consumers/ExpectedNearGapLimit.lean); 10 standard-only receipts |
| `dilation_normalized_limit_not_measure` (R1-CT1) | For the genuine CT1 distributions, nu_L/L^2 -> T = (x^2 Sha')' = sum_n (n^2 delta_n'' - 2n delta_n') as L -> 0 (L != 0), in Mathlib's tempered-distribution topology and on every test; T(phi) = sum_n (n^2 phi''(n) + 2n phi'(n)); near each integer n, T = n^2 delta_n'' - 2n delta_n'; T != 0; T is not of order zero at any nonzero integer; T is not given by any locally finite Jordan pair; the normalized variation near 1 diverges. | [ExpectedNormalizedLimit.lean](consumers/ExpectedNormalizedLimit.lean); 9 standard-only receipts |

**Recorded implementation refinement (HT2).** The frozen contract text says "prove
compact-limit extraction and uniform tails". The implementation proves the identical
conclusion, under the identical premises, with the explicit estimate
`nearGap_schwartz_pairing_bound`:

|nu(phi)| <= (1-a)2C(2N+3)K + 2 Lip(phi) d C(1+N) + 2K (pi^2 N^2/(4 d^2))(1-a)(2C) + 4C(9B+8K)/N^2

(K, B Schwartz seminorms, any N >= 1, 0 < d <= 1/2). Its inputs are the translated
sinc/triangle identity, integer tent interpolation, the near-gap mass bound and the uniform
cubic Schwartz tail. Uniform tails are proved; no compact extraction, limiting measure or
total-variation convergence is used. The ledger entry carries this refinement verbatim.

**CT1 formalization choices.** The limit filter is L -> 0 with L != 0, which contains the
paper domain 0 < L < log 2 as L -> 0+ (derived in the consumer on the explicit three-comb
pairing). "Not order zero" is stated at every nonzero integer against the sup seminorm on tests
supported in [n - 1/2, n + 1/2]. The not-a-measure, local-form and variation clauses are
additional.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for all nine modules and ten
consumer files. The unchanged W04/W07 (52) and W06 (14) workflow consumers pass against the
new source. Eight negative controls are rejected for their intended reasons: gaps -> 1/2,
total-variation conclusion, missing off-lattice premise, a constant CT1 member claimed zero,
wrong derivative sign, normalization L instead of L^2, measure representation, and the origin
claimed non-order-zero. The ledger now records 41 historical, 19 narrow and 40 absent roots.
This is not aggregate acceptance of 60 roots. All roots listed for R1-HT2 and R1-CT1 in
BUILD_SPEC now have narrow gates; aggregate acceptance of those units remains OPEN.

New supporting results: `ct1NormalizedLimit_fourier_selfdual` (T is canonically Fourier
self-dual), `translated_sinc_triangle_pairing` (for every linearly growing self-dual Jordan
pair and every real y), `jordan_pairing_order_zero` (any locally finite Jordan pair is of
order zero on compact intervals) and the generic `second_difference_bound`.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above with their exact
   premises; `nearGap_schwartz_pairing_bound`; `nearGapCombFamily_controlled_limit`;
   `ct1NormalizedLimit_fourier_selfdual`; `translated_sinc_triangle_pairing`;
   `nearGap_translated_triangle_bound`; `jordan_pairing_order_zero`.
2. **Workflow harvest at `6a2e20b`** ([ci-harvest-6a2e20b.json](evidence/current-codex/stage5/ci-harvest-6a2e20b.json)).
   No run was cancelled. OPICA follow-up (PR and push runs): preparation, exact-source
   subset, narrow candidates and frozen regression all PASS. The narrow job is the first
   completed OPICA narrow Lean CI job since `9ccea78e`. Full release readiness FAIL (expected).
   Parent `opica-contract` FAIL and `opica-component-summary` FAIL: unauthorized tracked
   deltas for continuation files, the same as at `40fd51b`, fail-closed. `python-rhrc` FAIL:
   parent rejects the incomplete child extension. `rhkg-compiler-receipt` FAIL: canonical
   graph reports disposition drift for every unregistered `Zeta23.OPICAFollowup` module; the
   same step failed at `40fd51b`; canonical regeneration is OPEN and generated products are
   not hand-edited. All inherited research replays PASS, including post268, post-282,
   post-284, post287 WP2/WP4 and the parallel closure campaign; they create no OPICA theorem
   authority.
3. **What changed.** HT2 and CT1 are complete at narrow level. The HT2 route that Stage 4
   recorded as a LEAD is now PROVED, and the compact-extraction obstacle (Mathlib has no vague
   compactness for signed Radon measures) is no longer on the critical path.
4. **Upstream.** The parent Gaussian H1 argument holds for every translate:
   int Delta(x - y) dnu = int e^(-2 pi i y x) s(x) dnu(x). The HT2 evenness hypothesis is
   redundant. The Dirac comb `dilatedCombDistribution 0` supplies Sha as a genuine element
   of Mathlib's tempered distributions; Mathlib's derivative and multiplication operators
   then express T exactly as the contract writes it.
5. **Downstream.**
   - DERIVED rate: optimizing N ~ (1-a)^(-1/10) and d ~ (1-a)^(3/10) in the formal estimate
     gives |nu(phi)| <= C_phi C (1-a)^(1/5). CT1 realizes decay of exact order (1-a)^2:
     nu_L(phi) = L^2 T(phi) + o(L^2), 1 - e^(-L) ~ L and T(phi) = 2 for a quadratic bump.
     The worst-case Schwartz exponent therefore lies in [1/5, 2] (OPEN).
   - DERIVED: the finite measure s.nu has Fourier-Stieltjes transform bounded uniformly by
     (1-a)|nu|([-1,1]): a one-line composition of the translated identity with the
     translated triangle bound. This is a sup-norm smallness, not total variation, matching
     the HT2 scope.
   - PROVED (consumer): after normalization no common variation constant exists, and the
     normalized limit leaves the measure class. The HT2 common-constant premise is exactly
     what fails under renormalization.
6. **Resurrected routes.** The Stage 4 compactness-free LEAD is now PROVED. Its predicted
   exponent 1/5 is DERIVED from the formal estimate; the derivation itself is not formalized.
7. **New RH-relevant clue (LEAD/HYPOTHESIS, not formal).** T = (E^2 - 1/4)Sha for the unitary
   dilation generator E = x d/dx + 1/2, whose Mellin symbol is (1/2 - s)^2 - 1/4 = s(s-1).
   Formally, for Re s > 1 and the non-Schwartz test x^(-s) on (0, oo):
   T(x^(-s)) = sum_(n >= 1) ((x^2 (x^(-s))')')(n) = s(s-1) zeta(s). So the CT1 normalized limit
   inserts exactly the polynomial factor of xi(s) = (1/2) s(s-1) pi^(-s/2) Gamma(s/2) zeta(s),
   removing the pole at s = 1. Its PROVED Fourier self-duality matches the s <-> 1-s symmetry of
   s(s-1). Vacuity check: in the critical strip the zero set is that of zeta, so this
   repackages zeta and carries no new zero information. A possible use is
   explicit-formula positivity functionals in which the pole terms drop out. Turning the clue
   into a statement needs a regularized cutoff family; it is supporting research only.
8. **Falsification checks.** Non-vacuity: every CT1 term is a nonzero distribution. Boundary
   a = 1 recovers the parent separator. Origin: T = 0 near 0, matching the cancelled origin
   atom. Scaling and sign: the wrong normalization and the wrong derivative sign are rejected.
   The off-lattice premise is required by the proof (negative control), but no counterexample
   to the conclusion without it is known: -nu_L has negative off-lattice part and still tends
   to 0. Whether that premise is mathematically necessary is OPEN. Circularity: HT2 uses only
   the parent H1 regularization, the mass bound and the cubic tail.
9. **Highest-leverage next moves.** CI on the Stage 5 head, where the narrow job must run the
   two new consumer files. Then the W06 inverse, sharp gap and leakage roots, where the
   translated identity and tent estimates may transfer. Then `ProfileEulerMaclaurin`,
   `LogFourierSobolev` and the three CP1 roots, which gate most absent roots, with J5.2/MS1
   in parallel. Optional supporting work: formalize the (1-a)^(1/5) rate and the cutoff
   Mellin identity.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 or 5 and carries older counts; README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), the full workflow harvest on the Stage 5 head, the 40 absent roots,
RH, Step 4 and the independent closing inequalities.
