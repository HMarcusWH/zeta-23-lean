# Frozen research orientation — 21 November 2026

This page describes the mathematical source and research record preserved at
[archive commit `7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9`](https://github.com/HMarcusWH/zeta-23-lean/tree/7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9).
Later documentation changes explain that snapshot. They do not retroactively
change the source to which earlier proof or experimental receipts apply.

**This repository's RH attempt remains incomplete.** Its independent Step 4
arithmetic estimates are open. This is a statement about the archived programme,
not an undated assessment of external RH research.

Start with the [README](../README.md), [project guide](PROJECT_GUIDE.md),
[reusable components](REUSABLE_COMPONENTS.md), [results and formalization](RESULTS_AND_FORMALIZATION.md)
or [reproduction recipes](REPRODUCIBILITY.md).

## Source identity and evidence identity

| Object | Identity and interpretation |
| --- | --- |
| Research and manuscript archive | Commit `7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9`, tree `9248b76d7aff60aab3bb775c4be9750dc6006003` |
| Named archive branch | `archive/2026-11-21-research-freeze`; use the commit above for an immutable citation |
| Written manuscript inventory | [43 original PDFs](../papers/README.md) and their [byte/blob manifest](../papers/MANIFEST_2026-11-21.json); two older PDFs remain elsewhere in the source |
| Current documentation | Read at the current checkout/PR commit; it is an explanation of the archive, not a new mathematical theorem checkpoint |
| Formal evidence | Declaration- and package-specific compiler, axiom and independent-consumer records; consult the [result map](RESULTS_AND_FORMALIZATION.md) and original receipts |
| Numerical and paper evidence | Individual finite ranges, methods, source pins and derivation status remain attached to each record |
| Source-policy and generated-state checks | Follow the [current authority guide](../research/RHRC/DOCUMENTATION_AUTHORITY.md); accepting the file inventory does not establish a mathematical claim |

The archive commit added manuscripts and documentation. It did not perform a
new whole-repository Lean build or independent mathematical review. A package's
old green receipt must be matched to its checked source; the later presence of
that package in a merge does not create a new receipt.

## What the final source includes

| Layer | Contents | Inspect |
| --- | --- | --- |
| Upstream Zeta23 | Zero-proportion results and analytic/linear algebra foundations with their own comparator statements | [Upstream guide](../UPSTREAM_README.md), [audit](../UPSTREAM_AUDIT.md) |
| Finite Weil / CCM and exceptional-zero programme | Exact canonical forms, boundary-flat detectors, parity and contact geometry, and the complete Step 1–3 packet | [Project guide](PROJECT_GUIDE.md), [complete output](../Zeta23/ExceptionalZero/Step123CompleteOutput.lean) |
| OPICA, follow-up and Rounds 2–4 | Obstruction transport, native fields/window rates, causal/Gram certificates, simultaneous parity negativity, source/spectral budgets and conditional closure consumers | [Integration map](../research/RHRC/integration/README.md) |
| November arithmetic frontier | Moment-slice carriers, finite certificate soundness, zero-strip rate ladder and RH-equivalent lower-bound contracts | [Frontier guide](../research/RHRC/integration/opica_round4/arithmetic_frontier/README.md), [12 November handover](../research/RHRC/integration/opica_round4/arithmetic_frontier/HANDOVER_2026-11-12.md), [ZeroFreeFloor.lean](../Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean) |
| Round 5 parity bridge | Exact moment shift, range/kernel relation, dimensions and parity-seed short exact sequence | [ParityMomentBridge.lean](../Zeta23/OPICARound5/ParityMomentBridge.lean) |
| Round 6 finite arithmetic | Native cells and shell geometry, signed costs, survivor/partner accounting, parity-deficit products and stopping trees | [Round 6 guide](../research/RHRC/integration/opica_round6/README.md), [finite typed audit](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean) |
| Supporting research system | Bounded composition, independent evidence checking, framework adapters, compiler dependency graph and arithmetic constraint graph | [Framework guide](FRAMEWORKS.md), [repository map](REPOSITORY_MAP.md) |

The arithmetic-frontier handover includes increments 6A and 6B. Its original
“current-head CI pending” language is historical evidence wording, not a live
status for this documentation branch. The original native follow-up also keeps
its separate [100-root/28-unit ledger](../research/RHRC/integration/opica_followup/continuation/2026-10-22/ROOT_LEDGER_100.json).
Later package completion does not silently complete that older acceptance scope.

## Where the mathematics stopped

The project has several alternative sufficient routes. The final source does
not require every route to succeed, and a new coordinate description is not a
new independent arithmetic input.

| Route family | Available mechanism | Missing input or boundary |
| --- | --- | --- |
| Ground/resolvent and joint-index routes | Conditional consumers, actual source identities and physical parity/ground adapters | Independent source comparisons, relevant shared-ground or singular cases, or the stated joint-index bound; read the [closure register](../research/RHRC/integration/opica_round4/CLOSURE_OBLIGATIONS.json) in its exact scope |
| Causal approximation and signed observation | Exact range/residual and quiet-observation implications | A source-specific zero residual limit or sufficiently small complete signed observation with all costs retained; see [NativeCuts.lean](../Zeta23/OPICARound2/NativeCuts.lean) |
| Moment-slice bounds | RH equivalences for cofinal, semibounded, polynomial and subexponential contracts, plus a zero-strip rate ladder | Proof of the required arithmetic bound; proving equivalence does not establish it |
| Round 6 survivor/parity-product routes | Finite algebra, native-cell transfers and paper reductions to signed arithmetic targets | The independent growing-horizon upper and formal validation of the complete paper transfer remain separate obligations |

For Round 6, [the route guide](../research/RHRC/integration/opica_round6/README.md)
explains `ACTUAL_UPPER`, `P303_OPPOSED_PRODUCT_UPPER`,
`N20_JOINT_ARITHMETIC_UPPER` and `PAPER_ROUTE_VALIDATION`.
The [constraint register](../research/RHRC/integration/opica_round6/CONSTRAINTS.json)
keeps source records, joint premises, alternative routes and context edges
separate. Finite stopping or cancellation identities do not supply the
asymptotic signed estimate.

Later manuscripts may strengthen a selected packet or remove an obstacle on a
specified subroute. Read the [result-level supersession map](RESULTS_AND_FORMALIZATION.md)
before treating an older open statement as the final formulation. Those scoped
improvements do not establish the independent Step 4 estimate.

## How to use this snapshot

To understand the attempt, follow the [four-step guide](PROJECT_GUIDE.md). To
reuse a result, choose a [component](REUSABLE_COMPONENTS.md), inspect its exact
assumptions and imports, and follow its [example](EXAMPLES.md). To reproduce
formal or finite evidence, select a [recipe](REPRODUCIBILITY.md) with the intended
scope. The default build is the inherited root, not an audit of every research
file.

The [archive overview](RESEARCH_ARCHIVE_2026-11-21.md) describes the manuscripts
and provenance. Research freeze and GitHub's administrative read-only archive
setting are separate; this page records the former and does not assert the
latter.

## Earlier orientation, preserved as history

The complete earlier page follows unchanged. Its active-PR directions, counts,
“current” headings and pending gates belong to the dated checkpoints stated
there; use the November 21 sections above for repository-wide orientation.

<details>
<summary>30 October snapshot with 2 and 7 November overlays</summary>

# Dated source and navigation snapshot — 30 October 2026

**Arithmetic frontier — 7 November 2026:** Increment 1 on PR #299 adds exact moment-slice carriers, conditional (C1) and selected-packet consumers and finite certificate consumers; see the [build specification](../research/RHRC/integration/opica_round4/arithmetic_frontier/BUILD_SPEC.md). RH and Step 4 remain OPEN.

**Superseding research handover — 2 November 2026:** current work is [PR #299, Madness?](https://github.com/HMarcusWH/zeta-23-lean/pull/299). See the [published handover](../research/RHRC/integration/opica_round4/progress/2026-11-02/HANDOVER.md). The 30 October snapshot below is preserved as history.


This page is the repository-wide orientation snapshot for the Round 4 branch.
It is **not a live CI receipt**. Use [PR #298](https://github.com/HMarcusWH/zeta-23-lean/pull/298)
for the current head, workflow attempts and review state. Return to the
[README](../README.md), [project guide](PROJECT_GUIDE.md),
[repository map](REPOSITORY_MAP.md) or [framework guide](FRAMEWORKS.md).

## Source scope

| Object | Recorded checkpoint |
| --- | --- |
| Accepted Round 3 parent | PR #297, commit `fe16565b2a31fb8b68bef916ae8f04d535880e7a`, tree `5442650eb749576e4a82e2d57460a4b97e19b5a9`. |
| Active development | Round 4 in PR #298, branch `research/opica-round4`; leave merging to the maintainer. |
| Research integration checkpoint | `4e16b9b85abe5a62618e04fab7de50ac9ec832ae`. |
| Subsequent CI portability repair | `bd95b5b5c2448c4da042702adcb6ba221c03415a`, tree `08589b17ae5e6d8ed607d0f5f4b2d02c9fa78340`. |
| This documentation revision | A descendant of that repair; obtain its exact hash from Git or the PR. It does not claim a future commit has passed CI. |

The [build manifest](../research/RHRC/integration/opica_round4/BUILD_MANIFEST.json)
closes the reviewed delta against the accepted parent. Old registries,
mathematical sources and compiler pins retain their original authority scope.
The frozen Control-v2 PR #287 blocks on older pages are preserved historical
records; they do not route the active Round 4 branch.

## What Round 4 currently contains

- Governed, bounded composition with independently reconstructed target types,
  full kernel/axiom checking, source-bound journals and eleven acceptance lanes.
- A support inventory extending the retained **397 named declarations in 40
  owned Lean modules**, including the original 98-declaration subset. Eight
  [source-constraint and error-reduction modules](../research/RHRC/integration/opica_round4/SOURCE_CONSTRAINTS.md)
  extend that scope; `ROOTS.json` records the exact current total. These are
  supporting results and conditional consumers, not a count of independent
  arithmetic restrictions or RH proofs.
- Three non-calibration composition targets: eventual closure, the actual
  signed source budget and the physical joint negative index. Their complete
  answer wrappers are withheld from the approved search menu.
- Six finite arithmetic probes with independent higher-precision reconstruction;
  these do not cover every aperture, cutoff or source configuration.
- Exact regular-cell, singular/shared-ground and source-arithmetic obligations
  retained as OPEN in the [closure register](../research/RHRC/integration/opica_round4/CLOSURE_OBLIGATIONS.json).

Read the [integration handover](../research/RHRC/integration/opica_round4/INTEGRATION_HANDOVER.md),
[math contracts](../research/RHRC/integration/opica_round4/MATH_CONTRACTS.json),
[support register](../research/RHRC/integration/opica_round4/ROOTS.json) and
[countermodel register](../research/RHRC/integration/opica_round4/COUNTERMODEL_REGISTER.json)
for the precise scope. Definitions of closing propositions prove that they are
well formed; they do not establish their independent premises.

## Validation boundary

At repair checkpoint `bd95b5b5`, local portable checks passed **156 tests in each
Python mode**, and numerical checks passed **23 tests in each mode**. The repair
[investigation](../research/RHRC/integration/opica_round4/CI_REPAIR_2026-10-28.md)
records the three confirmed prior-head failures and their regression coverage.
This navigation revision adds a closed documentation-migration regression;
the current [test inventory](../research/RHRC/integration/opica_composition/EXPECTED_TESTS.json)
is authoritative for its exact method count.

Local native checks establish only their recorded development scope.
Historical-native replay of canonical products is a structural/render check,
not fresh production qualification. Linux production isolation, all eleven
required lanes, their independent aggregate and exact-source compatibility
must pass on the actual pushed head. Inspect failed steps even when their
overall workflow is still running. Missing/skipped/stale evidence never passes.

## What remains mathematically open

RH, Step 4 and the independent source restrictions are **OPEN**. In particular,
the regular-cell chain still needs source-specific nonidentity/zero avoidance,
large-aperture separation and compatible interval selection; singular and
shared-negative-ground alternatives must be handled. The joint moving-test
arithmetic error budget is not proved. Causal approximation, complete signed
observation and the direct detector complement remain independent alternatives.

The original follow-up's [100-root ledger](../research/RHRC/integration/opica_followup/continuation/2026-10-22/ROOT_LEDGER_100.json)
has its own historical/narrow/full-release distinctions. Neither later package
numbers nor merging a PR silently discharge those original obligations.

## Updating this page

Date changes, cite exact source checkpoints, and distinguish checked receipts
from pending obligations. Do not copy live CI status into an undated claim.
Refresh this human navigation alongside package handovers; retain frozen
machine blocks and historical records. The
[documentation authority policy](../research/RHRC/DOCUMENTATION_AUTHORITY.md)
explains the precedence rules.

</details>
