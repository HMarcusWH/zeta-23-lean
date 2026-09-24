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
