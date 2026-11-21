# Documentation successor — 21 November 2026

This package accounts for the paper archive and the reader documentation added
after the research freeze. It provides **source-inventory checks only**. A pass
does not constitute a Lean build, mathematical review, canonical graph freshness
check, or full OPICA acceptance. The attempt's independent Step 4 inputs remain
open. Start with the [current snapshot](../../../../docs/CURRENT_STATE.md).

## What is authenticated

The chain has three explicit boundaries:

| Boundary | Check |
| --- | --- |
| Round 6 research commit `3835cc66641fa48d78db932db1d32b57687f728c` | Apply the unchanged Round 6 exact-tree policy against its Round 5 parent, including the validator's template digest. |
| Paper archive commit `7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9` | Account for all 46 additions (43 PDFs, the paper README and manifest, and the archive guide) and the sole root README edit. |
| Documentation successor | Admit only the exact added/edited paths and blob IDs in [SOURCE_SCOPE.json](SOURCE_SCOPE.json), with the policy digest bound in [source_scope.py](source_scope.py). |

The original Round 4, post299 and Round 6 validators and their policies are
unchanged. The current coordinator, service and end-to-end source consumer
dispatch through this successor. Its classification command checks the existing
Round 5/6 research roles and exactly four new audit-only file rules for the
archive, examples, scope tools and citation metadata. The entire inherited
classification order and assertions remain checked. Historical validators
continue to describe their original source objects.

The existing 77 active generated products retain the same exact path inventory
and their separate canonical freshness requirement. The four historical products
remain immutable. The successor does not make a generated product current merely
because its path is permitted. [Canonical materializer](../../tools/materialize_derived_state.py)

Each edited Markdown file retains any historical renderer block byte-for-byte.
The AGENTS instruction tail beginning “Keep the original Markdown/JSON contracts”
is also checked byte-for-byte. Papers, upstream notices, mathematical source,
compiler pins and historical evidence are inherited unchanged unless the exact
policy explicitly identifies an administrative source consumer.

## Check the scope

Run from the repository root, with the named baseline commits available locally:

```sh
python -B -m research.RHRC.integration.documentation_2026_11_21.source_scope --check
python -B -m research.RHRC.integration.documentation_2026_11_21.source_scope --check-classification
python -B -m unittest research.RHRC.integration.documentation_2026_11_21.test_source_scope
python -O -B -m unittest research.RHRC.integration.documentation_2026_11_21.test_source_scope
```

`--check` requires a clean committed checkout and verifies every tracked blob's
actual working-tree bytes without Git clean/EOL filters, including unchanged mathematical source, pins,
historical evidence and archive subjects. Missing files, `skip-worktree` and
`assume-unchanged` index states do not qualify. The returned
`PASS_SOURCE_SCOPE_ONLY` remains narrower than compiler or release acceptance.

For a read-only review of a sparse clone, use `--check-tree`. It verifies the
committed Git objects and exact policy but deliberately returns
`PASS_COMMITTED_TREE_SCOPE_ONLY`. It says nothing about the completeness of the
working tree. Production callers use `validate_descendant`, not this tree-only
mode. Neither command accepts an arbitrary path-prefix exemption.

The [documentation workflow](../../../../.github/workflows/documentation.yml)
checks the full working-tree scope, preserved renderer, reader links and exact
examples. Its separate branch-scoped canonical refresh job exports a checked
generated-state candidate patch; it never pushes or accepts the stale input
tree. Existing compiler, graph and production workflows remain independent
gates. See [reproducibility](../../../../docs/REPRODUCIBILITY.md) for their scope.

## Reviewing a future update

An unlisted document or changed approved blob fails the policy. A later edit
needs a reviewed exact policy revision or successor and updated provenance.
Recompute the validator template digest with only its single `POLICY_SHA256`
line normalized, then bind the policy's SHA-256 in that line. Review the complete
delta and negative controls before publishing. Do not update a hash to hide an
unexpected mathematical, evidence, instruction or workflow change.

The policy's `successor_human_review: PENDING` receipt field records that source
inspection is not independent human acceptance. It is not a substitute for the
repository's original release obligations.
