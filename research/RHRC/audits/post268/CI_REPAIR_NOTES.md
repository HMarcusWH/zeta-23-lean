# PR #269 CI repair log

Status: bugfix and replay evidence, not a merge-readiness or RH claim. RH remains OPEN.

## Original failure anchor

Commit `656b7b844dd225ed6b9ce173c3ac36d93273eb17`, tree
`d0fd580fd5462a492a2c588dfa034130f73ef2d2`.

- Lean/bootstrap: run `36171140637`, job `108190678754`.
- Extended shard: run `36171140589`, job `108190679012`.
- Complete harvest: run `36171140589`, job `108192347240`.

The failed harvest was correct: the post-222 independent checker had been
invoked without its required generated schedule. No result was missing or
duplicated, but one of the 44 processes failed. A successful harvest must not
ignore that failure.

## Repairs

The runner now executes the existing frozen post-222 schedule producer before
the independent checker, passing the same fixture and the actual generated
schedule. Both processes share one timeout budget. Failed producers, missing
outputs, stale schedules, checker failures, process timeouts, missing shards,
changed source identities, and altered log/schedule hashes all fail closed.
Twenty adversarial unit tests exercise these contracts, including the real
frozen schedule producer. The workflow runs those tests separately from the
44 scientific/implementation checkers.

The Lean fixes retain the intended mathematical statements:

- Use the existing `euclideanBoundaryFlatSubspace` membership predicate rather
  than the nonexistent `EuclideanBoundaryFlat` identifier.
- Make `paritySplitGroundSpace` a reducible type alias so product instances are
  inherited; use the existing `finrank_bot` lemma.
- Give the reverse-parity equivalence its explicit `1 <= K` proof in the source.
- Use the Euclidean equivalence's inverse law, exact finite coordinate reduction,
  explicit transport reduction, and rational normalization in the K=4 source
  counterexample. No numerical oracle or new axiom is introduced.

Proof repairs are now committed source, not mutations performed before CI.
The archive preparer no longer edits Lean. The proof workflow rejects any
Lean working-tree diff before compilation and uploads the source hashes,
checkout commit/tree, compiler log, and axiom-audit log even on failure.

## First replay and follow-up

At `3d0f28cf29dd0c212a8c5b9e1d4f99371bc3c864`, tree
`78077aea5b202d5a0e1c1127a4b825f3783cb39c`, run `36177818811` completed all eight
shards and the complete harvest: **44/44 successful executions**, zero missing,
extra, or duplicate results. The independent post-222 result is capped at
`IMPLEMENTATION_CROSS_CHECK_ONLY`: it compares independent finite algebra paths
at the five inherited centers; it does not establish a new positivity theorem.

The first Lean repair replay, run `36177818728`, compiled five of the seven
modules. Its remaining failures were the incorrect `Module.finrank_bot` name
and incomplete simplification of literal finite-vector coordinates. Those are
repaired in this follow-up. The direct derivative formula and its negative sign
already compiled in that replay, but the complete counterexample theorem did
not yet have a clean dependency chain. Only the subsequent complete compiler
and axiom gate can validate the full seven-module package.

## Deployment boundary

The original historical audit archive remains intact and hash-verifiable.
The separately uploaded, uncommitted integration transport from the previous
work session was tested during recovery and is corrupt (LZMA decoding failed;
concatenated SHA256 `547bdf3e52c6972adac9325ef68e227bfafe47d78d45041326df0e581578ad0e`).
It was not executed or deployed. Describing that package as ready to commit
was premature. The temporary recovery workflow has been removed.

This repair does not pretend that the unfinished final integration package has
been deployed. Plain-file materialization of the historical corpus, final
binding/scope integration and strict generated-receipt regeneration remain a
separate completion gate. While the staging materializer exists, the existing
main workflows defer some byte-current graph/integration checks; their green
status is not final merge readiness.

## Mathematical boundary

Strict-sector simplicity concerns the legal boundary-flat parity coordinates,
not the original unconstrained CCM even-simple gate. A tie is retained and
contributes at least two ground directions. The exact K=4 falsifier refutes a
carrier-wide endpoint-jet-to-interior-sign shortcut, not a ground-mode-specific
sign theorem. The cofinal certificate implication has an explicit unsupplied
infinite arithmetic premise; it is not a premise-free proof of RH.
