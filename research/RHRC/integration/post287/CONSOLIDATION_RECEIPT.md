# PR #290 consolidation record — 2026-10-12

## Authority and decision

**Canonical PR:** #290 (`research/post287-wp0-wp7-integrated-20261012`), based on merged #288 `bb7c9c9d54fa2d1f82ad5b682c31148539a8f78c`.
**Superseded competing draft PRs:** #289 and #291.
**Instruction:** consolidate into #290; do not merge to main or delete source branches.
**Mathematical claim:** RH_OPEN throughout.

## What was preserved or ported

- **Retain #290's already broader WP1/WP3 Lean implementations** (reciprocal-aperture calculus/concavity and the actual strict-even #247 → #287 negative-shift ray, source normalization and prime/budget identities). Do not downgrade to the shorter versions on #289, or to the unrelated #291 reciprocal proof candidate. These still require exact-head Lean, axiom and proof-escape checks.
- **Retain #290's WP2 producer/checker**, including the later correction already made on its branch: the Q15 final rational endpoint lies *above* exact `log 16`, and the no-search checker uses `verified_cell_bounds` to verify the same domain. Its Arb evidence is not itself a Lean theorem.
- **Retain #290's richer WP4 frozen K3 feasibility checker, and WP5/WP6 probes.** The other branches contained overlapping earlier variants; they are preserved in their own historical commits and are not silently counted as independent replications.
- **Port the genuinely unique #289 GitHub Actions workflows**: `rhrc_post287_focused.yml`, `rhrc_post287_numerical.yml`, and `rhrc_post287_wp6.yml`. Adapt the K3 invocation for all frozen primary/control boxes (`--max-boxes 0`, fixed 384-bit and depth 40), report PASS/UNRESOLVED visibly, and upload results. These workflows supplement #290's existing post284 checks and isolate long WP2/K3 tasks on suitable runner time budgets.
- **Do not duplicate #291's planning document and WP5 implementation**: #290's `BUILD_CONTRACT.md` and `wp5_modified_prime_crossing_certificate.py` already cover them. Nothing unique and more formally authoritative was established by #291.
- **Preserve #289's failed focused Lean run in history** as a real failed compiler check of #289's original WP1; it neither validates nor refutes #290's different revision. Its completed WP5 and WP6 checks are bounded research results, not Lean or RH authority.

## Stop conditions

WP4 is D2 = FULL, covering **both K3 parity sectors** continuously over `[1/512, log16]`, *only if* certified. Frozen Q14 gate first, then the single authorized fourth-order Taylor-model alternative if needed. `UNRESOLVED` is neither positive nor negative and can never be passed off as the full certificate. The finite M76 grid remains insufficient. Do not extend a finite window to all cutoffs/apertures, assume RH-strength prime bounds, or promote research workflows into mathematical theorems.

**Post-consolidation status:** the canonical PR stays DRAFT pending CI and the complete WP0–WP7 work-package gates. Other PRs can now be closed as superseded, without branch deletion or merge.
