# Post-#282 contact-calculus post-green report

**Status: HARVESTED AFTER MERGED PR #284 (post-284 campaign). NOT AN RH PROOF RECEIPT.**

## Post-284 harvest (current)

- PR #284 checked head `7225489a1d60812743e419d5b9042c8dca7eef53`; merge
  `5e7253bffa570c0e07052b8d59a0949cdbcabdbe`; tree
  `96f851b45af4d3b11fef699fbd5cb274f60a9f6c`.
- Check runs on the checked head: **56/56 success across 18 workflow runs**
  (GitHub check-runs API). Per-job rows, categories (FORMAL_VALIDITY /
  REGRESSION / RESEARCH_PRODUCING) and run ids are recorded in
  `research/RHRC/integration/post284/WORKFLOW_HARVEST.json`. Green means
  workflow correctness; research jobs may record negative or unknown
  dispositions.
- Individual claim audit (`research/RHRC/integration/post284/CLAIM_MIGRATION_MATRIX.json`):
  - `R003_COMPRESSED_PRODUCTION_C2` — bound theorem
    `canonicalEvenCompressedC2_proved (K)` has no premise beyond `K`;
    axiom-audited in the merged lean-compressed-calculus job.
    **Promoted to PROVED_UNCONDITIONAL** by the deliberate post-284 migration.
  - `R003_INHERITED_FIRST_VARIATION_RESTRICTION` — bound theorem's
    hypotheses are exactly the generated strict-even contact and `n < k`;
    covered by the axiom audit's expected reports.
    **Promoted to PROVED_UNCONDITIONAL.**
  - `R003_WEIGHTED_PRODUCTION_PAIR_BALANCE` — takes
    `hF04 : ProductionContactF04DerivativeAuthority L K`. **Stays OPEN**; the
    registry note now states the F04 premise explicitly.
  - `R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER` — takes `hF04` at the
    contact aperture. **Stays OPEN**.
- Remaining F04 gap: `ProductionContactF04DerivativeAuthority` still has no
  proof constructor. The post-284 campaign compiles its prerequisite, the
  fixed-aperture regularized whole-energy identity
  (`Zeta23/CCM/CanonicalRegularizedEnergyIdentity.lean`); the moving-aperture
  differentiation remains OPEN.
- OBS-060O, odd/tie branches and RH remain OPEN.

## Original pre-merge gate text (historical)

**Historical status: PENDING CI / NOT A PROOF RECEIPT.**

Populate only after the exact final PR head is fully settled. The harvest must
record every workflow/job disposition, exact head/tree, compiler and axiom
evidence, research-result deltas, falsified mechanisms, surviving open
obligations, and the next mathematical move.

RH remains OPEN unless a literal unconditional Mathlib RH theorem separately
passes the complete claim-validation gates.

## Candidate claim promotion gate

The candidate branch now carries four **OPEN candidate bindings**:

- `R003_COMPRESSED_PRODUCTION_C2`;
- `R003_WEIGHTED_PRODUCTION_PAIR_BALANCE`;
- `R003_INHERITED_FIRST_VARIATION_RESTRICTION`;
- `R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER`.

They are candidate bindings, not yet theorem authority. After the exact final
head passes all formal and claim gates, verify each *exact theorem statement*
and axiom footprint, including every hypothesis, before any claim promotion.

- `R003_COMPRESSED_PRODUCTION_C2` can receive unconditional support if its
  exact theorem is proof-escape and axiom clean.
- `R003_INHERITED_FIRST_VARIATION_RESTRICTION` can receive unconditional
  support if its exact theorem is proof-escape and axiom clean.
- `R003_WEIGHTED_PRODUCTION_PAIR_BALANCE` currently has an explicit
  `ProductionContactF04DerivativeAuthority` premise. Green CI proves a
  *conditional implication*, not the unsupplied F04 premise. Keep the
  unconditional arithmetic balance claim OPEN.
- `R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER` likewise explicitly assumes
  `ProductionContactF04DerivativeAuthority`. Classify its conditional branch
  theorem accurately; do not promote unconditional completion.

The existing R003 contract intentionally requires OPEN candidate statuses.
A future deliberate status migration must simultaneously update its validation
and binding inventories, and must never treat compiler-green conditional
statements as premise-free results. No automatic blanket promotion to
`PROVED_UNCONDITIONAL` is permitted.

No promotion of `OBS060O_SATURATION_EXCLUSION`, `ODD_TIE_BRANCHES`, or
`RH` is permitted from this step. Those remain OPEN unless separately proved.

