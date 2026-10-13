# Audited frozen-fixture provenance migration

Source reviewed: `31512dbb698dd59b90cfa32549f0e9273a5163f9`.
This migration changes **10 provenance hash fields in eight fixtures** only.
Every non-hash JSON field is exactly preserved, including all frozen centres,
schedules, target dimensions/parities, precisions, budgets, expected results,
classification rules, claim caps, authority references and no-refit policies.
None of the 28 frozen manual-campaign numerical inputs is edited.

## Why the source binding changes

The intentional canonical backend repair replaces acceptance of nonfinite
sign enclosures with fail-closed checks. AST comparison against source blob
`0a38380f5674d965aabcc0b8cbfc37c3813a180e` found exactly three existing
functions changed: `definitely_positive`, `definitely_negative` and
`definitely_nonzero`. Two helpers were added: `require_finite` and
`finite_second_order_lower`.

All 27 other existing function ASTs are identical, including the integral
kernel, pole, archimedean primitives/correction, qBasis, von Mangoldt weights,
prime sum, canonical matrix and signed-channel reconstruction. The existing
first/second derivative and sharp-trajectory module blobs remain unchanged.
Thus this is an audited acceptance/provenance migration, not a new matrix,
normalization, derivative formula, target, schedule or expected mathematical
outcome. On finite inputs the three modified sign predicates retain their
original results; indeterminate/infinite inputs are rejected.

The validators hash exact file bytes as
`SHA1("blob " + byte_length + NUL + bytes)`. Expected hashes below use
**canonical Git blob bytes**, matching Linux CI. Windows CRLF working-tree
hashes are not substituted.

## Exact changed bindings

| Fixture / hash field | Previous blob | Replacement blob |
|---|---|---|
| post190 / canonical_source_module_blob_sha | `0a38380f5674d965aabcc0b8cbfc37c3813a180e` | `701d62266ba9db89c59a9d1edef6546b77b1bfe9` |
| post192 / post192_fixture_blob_sha | `bf21458e2dd3e42c23124f3fa7b2a32e12edd05d` | `cbe48a5ec803af62bdcd63f3bc11cce797a227f5` |
| post194 / post193_fixture_blob_sha | `8c59b133b759aa7324992e929c0abaac5db3bf44` | `d3b761222c1be356b542ffa5507ca8c32717f40e` |
| post196 / inherited_post195_fixture_blob_sha | `dc81d125c01aabcf54c990b70f579ed378c30cba` | `555219cd9517c8c677938d0e573f5048ed8fd654` |
| post198 / inherited_post197_fixture_blob_sha | `7407a1d572379e3c97f9c476a6f45148ca5fba51` | `a88f9649566ceb16bea1566be55cb7ff81146030` |
| post198 / canonical_source_backend_blob_sha | `0a38380f5674d965aabcc0b8cbfc37c3813a180e` | `701d62266ba9db89c59a9d1edef6546b77b1bfe9` |
| post200 / inherited_post199_fixture_blob_sha | `2cb12b48140bd61f05b4c06de9f11e6fdb0dc393` | `83b8b0c1fe5d6a5de215a2024a4a60b237c6084f` |
| post202 / inherited_post201_fixture_blob_sha | `667feb4d5b7ab58360b506ee4d0ce71d3c1b8d4e` | `0f7e1b59e2a3d74f157d7b6233298c9fa13a64f9` |
| post214 / inherited_post202_fixture_blob_sha | `370a7c2aecb15155b2adc51a9c2f08dfcf36e1b1` | `ea427461ace70bda35efb1ec59f1320f5020e38d` |
| post214 / provenance_blobs.canonical_source_arb.py | `0a38380f5674d965aabcc0b8cbfc37c3813a180e` | `701d62266ba9db89c59a9d1edef6546b77b1bfe9` |

The dependent fixture closure is
`190 → 192 → 194 → 196 → 198 → 200 → 202 → 214`.
Refreshing only the five initial failure sites would create stale downstream
bindings in 196, 200 and 202. Those three were therefore included with the
same provenance-only restriction.

## Validation and authority

All eight unmodified scope/provenance checkers passed in a validation copy
constructed from exact Git object bytes with the migrated fixtures overlaid.
This avoids Windows line-ending conversion while running the actual validators.
Their synthetic/control dispositions and frozen scope settings remain unchanged.
Deep JSON comparison confirms exact equality of every non-hash field.

No complete historical numerical certificate was rerun in this migration pass.
Fresh exact-head CI must execute those unchanged frozen research schedules;
any changed numerical disposition must be investigated rather than fitted by
editing an expected result. Earlier invalid nonfinite-bound whole-window claims
are not restored by this provenance update. This adds no Lean theorem or RH
authority. **RH_OPEN**.
