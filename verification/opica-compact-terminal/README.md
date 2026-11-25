# Compact arithmetic supplied Step 4 — replacement candidate for #317

**Status: SOURCE_IMPLEMENTED_CANDIDATE / NOT_KERNEL_VALIDATED / RH_OPEN.**

Base: #316 2fe4a756e8576203cfb009314861616accdb6dde (tree 4571fe6cc82466115beae5bea5037071ebec3524), which stacks #311 and #312 and contains the copied #313 historical and #315 bipolar source. The branch does not merge those PRs or promote their evidence. The frozen compact supplier is lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207 (tree 5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f), Apache-2.0, Levent Alpöge/Claude/Anthropic. Full extraction run 45712665996 was source-green (1627 blobs). Prior compact arithmetic kernel run 45713758389 remains a separate diagnostic; this branch does not wait for #317 or consume any old compiled object.

## Exact proof constructed

1. Cut compact New.Main before New.grh and omit public Main/Statements/Challenge, using the independently verified v0.6 source extraction policy. Preserve original notices.
2. PrincipalStrip.lean proves an actual weighted arithmetic bound at each fixed β in (1/2,1), on M=18480 and class 9239. It calls eventually_primeError_le_rpow and the original **conditional** entireL_ne_zero_of_primeError_le criterion, which uses finite-height twist avoidance, then specializes to the conductor-one zeta function.
3. Terminal.lean uses the bound at a tolerance chosen for each actual native zero, the existing reflection lemma, and the existing critical-line positivity of both exact physical moment slices. This derives the native C1 predicate and applies riemannHypothesis_of_cofinal_moment_slice_bounds to obtain the exact Mathlib proposition RiemannHypothesis.
4. The source target is Zeta23.OPICACompactTerminal.riemannHypothesis_step4_compact_arithmetic, with Zeta23.OPICACompactTerminal.step4C1_compact_arithmetic as the required intermediate.

This is a deliberate shorter supplied route than the uploaded v1.0 weighted-arithmetic-to-literal-energy supplement. It reuses the conditional upstream analytic criterion instead of reimplementing the paper's Taylor-moment lemma and **does not formalize the literal-ramp/energy bridge**. All-tolerance strip transport and reflection already imply critical-line confinement; this is explicitly an RH-equivalent derived intermediate, not an assumed/imported RH theorem or a new independent arithmetic proof. The native consumer is a real proof dependency, not a call to an RH-to-C1 theorem. This is NOT closure of the original independent arithmetic estimate or the old local masked survivor theorem. The paper v1.0 remains a separate legitimate formalization goal.

## Gates

- Recreate exact source cut and verify every upstream blob and every native source blob. Fresh stock Mathlib at 56a005855ea17e0b0958f73ec801ae140b0a1679, Lean 4.35.0, every transitive package pinned, separate native/supplier package options.
- Native pin preflight, common source build, exact root type, allowed axioms only, transitive proof-value/type/structural dependency inspection, required native and arithmetic dependencies, banned upstream endpoints and old analytic module origins.
- Fresh independent stock reconstruction and receipt equality. This is not an alternate kernel/Comparator verification; that and canonical admission/release review remain separately required. No automatic claim registry changes.
- A compiler failure (including common-pin port issues or global name collisions) is a failure, never a proof. No sorry or new axiom permitted. All jobs preserve receipts/logs on failures.

PR #317 is superseded as the preferred execution path; its head and prior evidence remain untouched. The previously started workflow may continue independently; it is not a dependency.
