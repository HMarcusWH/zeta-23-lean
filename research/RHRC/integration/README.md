# RHRC Integration Foundation

This directory is the governed integration boundary between the exact RHKG
repository state and research frameworks such as FFBBP, OoL-MVS, Permansson,
and MCM-HMWH.

It does **not** create mathematical theorem authority.

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
