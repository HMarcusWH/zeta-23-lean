# Integration packages and authority boundaries

This index covers the mathematical and research-tool packages present in the
[21 November 2026 archive](../../../docs/CURRENT_STATE.md). Begin with the
[project guide](../../../docs/PROJECT_GUIDE.md) for the argument,
[reusable components](../../../docs/REUSABLE_COMPONENTS.md) for another
application, or [reproduction recipes](../../../docs/REPRODUCIBILITY.md) for
checks. This repository's independent Step 4 estimates remain open.

| Package | Mathematical or operational role | Read first |
| --- | --- | --- |
| Step 1–3 integration | Assemble the hypothetical-zero detector and source-bound outputs | [Complete output](../../../Zeta23/ExceptionalZero/Step123CompleteOutput.lean), [project walkthrough](../../../docs/PROJECT_GUIDE.md#what-is-actually-carried-through-steps-13) |
| Original OPICA | Obstruction preservation, corrections, rates and independent-constraint interfaces | [Architecture and original programme](opica/README.md) |
| Native follow-up | Actual-source transforms, explicit formulas, rates, observations, profiles and jets | [100-root programme and scoped receipts](opica_followup/README.md) |
| Round 2 | Delayed causal probes, Gram/residual analysis, fixed filters and finite certificates | [Programme and open estimates](opica_round2/README.md) |
| Round 3 | Common-aperture parity negativity, local frames and actual newborn witnesses | [D01–D05 and finite probes](opica_round3/README.md) |
| Round 4 | Signed source/spectral budgets, ground/observation support and conditional closure consumers | [Programme](opica_round4/README.md), [contracts](opica_round4/MATH_CONTRACTS.json), [open closures](opica_round4/CLOSURE_OBLIGATIONS.json) |
| Arithmetic frontier | Moment slices, finite certificate soundness and the zero-strip/RH rate ladder | [Current package guide](opica_round4/arithmetic_frontier/README.md), [12 November handover](opica_round4/arithmetic_frontier/HANDOVER_2026-11-12.md) |
| Round 5 parity bridge | Moment shift, exact seed dimensions and the short exact sequence | [ParityMomentBridge.lean](../../../Zeta23/OPICARound5/ParityMomentBridge.lean) |
| Round 6 | Finite native-cell and prime-factor algebra, survivor costs, parity deficits, stopping trees and paper-route constraints | [Programme](opica_round6/README.md), [constraint register](opica_round6/CONSTRAINTS.json), [finite audit](../../../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean) |
| Governed composition | Bounded proof search, source-bound evidence, independent consumers and acceptance aggregation | [Runtime guide](opica_composition/README.md), [framework guide](../../../docs/FRAMEWORKS.md) |

Package rounds differ from the four mathematical steps. A later package does
not replace an earlier contract or extend its historical receipt automatically.
In particular, finite Round 6 transfers and the growing-horizon paper route
have separate validation requirements. The [result map](../../../docs/RESULTS_AND_FORMALIZATION.md)
records exact mathematical statements and source correspondence.

The [integration boundary](INTEGRATION_BOUNDARY.json) separates mathematical
authority, source-discovery evidence and framework outputs. The historical
[framework registry](FRAMEWORK_REGISTRY.json) and selected
[provider configuration](opica_composition/FRAMEWORK_PROVIDERS.json) are distinct.
Use the [current authority guide](../DOCUMENTATION_AUTHORITY.md) for source-policy
routing and the [repository map](../../../docs/REPOSITORY_MAP.md) for graph and
build surfaces.

The older foundation account below preserves the original extraction and
authority design. Its three anchor PRs and pending-work instructions belong to
those checkpoints; they are not a live acceptance receipt for this checkout.

<details>
<summary>Preserved historical account and checkpoint wording</summary>

The dates, counts, active-PR labels and next steps below belong to their original checkpoints.
Use the dated navigation above for the repository-wide reading path.

# RHRC Integration Foundation

This directory is the governed integration boundary between the exact RHKG
repository state and research frameworks such as FFBBP, OoL-MVS, Permansson,
and MCM-HMWH.

It does **not** create mathematical theorem authority.

## OPICA follow-up navigation (22 October 2026)

For draft PR #294, start with the [manual route map](../graph/OPICA_FOLLOWUP_CURRENT_STATE.md),
the [continuation guide](opica_followup/continuation/2026-10-22/README.md),
the [current root ledger](opica_followup/continuation/2026-10-22/ROOT_LEDGER_100.json) and [current module status](opica_followup/continuation/2026-10-22/MODULE_STATUS.md).
Those pages distinguish historical source-bound evidence, narrow local gates,
candidate work and absent obligations, and link the current-stage handover.
All 100 roots remain required. Aggregate/full-release acceptance, RH and Step 4
are OPEN. The anchor descriptions below preserve the earlier integration context.

## Three independent anchors

The integration layer keeps three authorities separate:

1. **Theorem authority** — merged green theorem state through PR #262.
2. **Frozen Control-v2 authority** — PR #117. Control-v2 remains an historical
   baseline and is not silently rewritten.
3. **Repository/RHKG authority** — merged semantic-closure state through PR #263.

A framework run must state the exact anchor it consumed.

## Source candidate exactification

PR #263 exposes named source declarations throughout the repository. Those
objects are source-discovery records, not compiler declarations.

The candidate exactifier takes the RH_FORMAL_CORE theorem/lemma source surface
and asks Lean to resolve each source item against the exact elaborated
environment using the exact originating module together with the source-spelled declaration
name as a suffix constraint on the compiler declaration. This handles both
unqualified source spellings such as `hasDerivAt_sourceAtomPairing` and
qualified source spellings such as
`GlobalBottomResidualState.primeTestWeight_endpoint_order_eight_of_evenStrict`
without guessing a namespace.

Resolution is fail-closed:

- `RESOLVED_UNIQUE`
- `RESOLVED_PRIVATE_OR_INTERNAL`
- `NO_COMPILER_MATCH`
- `AMBIGUOUS_COMPILER_MATCH`
- `KIND_MISMATCH`

A uniquely resolved public theorem is then compared against the sealed
registered-root compiler dependency receipt and classified as already visible
or source-only. Receipts also carry a compiler-rendered type string and digest;
that rendering is descriptive and the resolved Lean declaration identity remains
the authority-bearing identity.

`SOURCE_ONLY_PUBLIC_THEOREM` means only that the declaration is absent from
the current registered-root compiler dependency closure. It does **not** mean
the theorem is mathematically independent, useful, new, or RH-relevant.

## Authority firewall

```text
LeanSourceDeclaration              != compiler theorem authority
LeanCandidateReceipt               != registered claim
SOURCE_ONLY_PUBLIC_THEOREM          != independent mathematics
candidate dependency receipt        != registered dependency authority
FFBBP/OoL/Permansson/MCM output     != theorem
multi-framework agreement           != theorem
terminal claim                      = RH_OPEN
```

Only the existing Lean/compiler and registered claim-validation gates may
promote a mathematical statement to PROVED authority.


## FFBBP v1.6 RHKG snapshot assurance

The first post-foundation framework adapter applies FFBBP v1.6 only to a
static repository snapshot. It does **not** run the qualified RUN42C unknown-field
solver on Lean theorems.

The full reference state is the Lean-exact RH_FORMAL_CORE theorem/lemma
candidate receipt surface. The declared diagnostic is exact
`visibility_class`; the categorical research-control decision is whether a
candidate is `SOURCE_ONLY_PUBLIC_THEOREM`.

Three frozen reductions are replayed against the full reference path:

- `MODULE_ONLY_SNAPSHOT` — negative control; expected to fail because one
  module may contain candidates with different visibility decisions.
- `TYPE_DIGEST_SNAPSHOT` — current-snapshot probe; may preserve the binary
  decision while losing the fuller visibility diagnostic.
- `MODULE_VISIBILITY_SNAPSHOT` — selected post-reference cohort projection;
  retains module plus exact visibility class and is used only for navigation
  after full Lean exactification.

This imports FFBBP's v1.6 distinction between decision sufficiency, diagnostic
commutation, and stateful transition closure. Because the adapter is snapshot
Xi, autonomous transition closure is structurally not claimed.

Passing FFBBP assurance means only that the declared reduction preserves the
declared finite-snapshot diagnostic/decision surface. It does not rank theorem
importance, prove mathematical implication, inherit RUN42C qualification, or
change RH status.


## OoL RHKG Phase Atlas

After merged-green PR #265, the exact 680 source-only public theorem/lemma
declarations are available through 195 FFBBP-assured module/visibility
navigation cohorts. The next integration layer does not rank those cohorts.

OoL consumes a separate compiler dependency receipt rooted at the exact 680
Lean declarations and applies the theorem-value-erased support projection.
Contacts are tested against three disjoint registered-claim interface families
and against the exact #261 21-edge arithmetic frontier.

A contact means only that an exact declaration survives the declared support
filter. It is not theorem composition, implication, independence, usefulness,
or RH evidence. Surviving contacts must return to exact Lean theorem work.


OPICA Round 4 adds governed deduction, independently checked source probes and
new supporting mathematics. See [the Round 4 state](opica_round4/README.md) and
[the governed runner](opica_composition/README.md). The new aggregate retains
all historical scopes and requires fresh current-child compatibility.
RH and Step 4 remain OPEN.


</details>
