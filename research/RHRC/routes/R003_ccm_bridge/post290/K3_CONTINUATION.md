# D2 SECOND resource continuation

This implements RESEARCH_PROTOCOL section 5. The four scripts preserve the
historical raw intervals and immutable source/run identity, freeze eight exact
rational children per exactly adjacent component, run the fixed two SECOND
passes, and reconstruct all thirty continuous layer unions. There is no FOURTH
fallback. A process finishing successfully may still return UNRESOLVED.

`k3_resume_partition.py ARCHIVE --out PARTITION` requires the full hashchecked
archive from guarded run 38332529352, historical source 31512dbb. It checks all
thirty layers, exactly twenty-six complete and unresolved counts 7/7/11/10.
The full partition, source dependency hashes, continuation-code hashes and
Python identity are written before any numerical evaluation. The historical
manifest is consumed as evidence and is never rewritten.

`k3_resume_search.py PARTITION --out SEARCH` uses isolated processes (Arb
precision is global), with at most eight simultaneous jobs. Each first job has
256 bits, depth 40, 4096 nodes and a hard 1800-second wall limit. It writes a
coverage checkpoint before every enclosure. Every unresolved leaf is split
into four exact children for the predetermined second pass: 512 bits, depth
48, 8192 nodes, 1800 seconds, first 256 children by Q/component/left endpoint.
Remaining children are persisted as unrun. A certified negative centre stops
that mathematical branch and prevents a complete result.

`k3_assemble_complete.py candidates PARTITION SEARCH --out CANDIDATE` merges
accepted raw ancestral intervals and newly evaluated intervals, validates the
exact accepted plus unresolved partition, and makes no positivity claim.

`k3_replay_all.py CANDIDATE PARTITION --out RECEIPT` independently reconstructs
the full-interval curvature/Taylor arithmetic at 768 bits on every accepted
leaf. The canonical source backend is shared and the independent source
normalization gate is a separate condition. Before execution the partition
also freezes an operational checker wall budget of 1800 seconds per layer;
exhaustion leaves every unreplayed interval explicitly unverified. This extra
bounded checker budget limits execution and cannot relax the D2 acceptance
criteria. No current check rewrites historical receipt hashes.

`k3_assemble_complete.py final CANDIDATE RECEIPT --out DISPOSITION` is always
NON-PARTIAL. It requires thirty distinct complete layer receipts, matching
candidate hashes and endpoints, every tile freshly checked, zero unresolved,
unrun, failed or unverified intervals, finite positive enclosures, both parity
carriers and correctly bracketed logarithmic seams. Otherwise it writes
D2_OPEN and fails. The rational analytic tails count only on intersection
with their frozen-Q physical cells; the native entering atom vanishes at the
logarithmic seam by the existing normalization gate.

D2_COMPLETE has CERTIFIED_FINITE authority only. This tooling supplies no Lean
term of `hWindows`, no universal-aperture theorem and no proof of RH. RH_OPEN.

## Fresh checking across independent runner shards

When checker integrity repairs postdate the producer, preserve the old
partition and candidate bytes. `k3_source_revalidation.py PARTITION --out REVIEW`
checks exact raw equality of canonical dependencies, unchanged SECOND search,
partition functions, resource constants, independent SECOND arithmetic and
exact dyadic endpoint serialization against the original pinned Git object.
The new source and an explicit integrity-code delta inventory go in a separate
review receipt. No historical source field is rewritten.

`k3_replay_shards.py freeze CANDIDATE PARTITION REVIEW --out PLAN` freezes every
original accepted leaf into exact ordinal chunks of at most 512 leaves under
`SECOND_FRESH_768_SHARDED_v1`. Each parent layer and candidate manifest is hashed;
checking remains SECOND at 768 bits, with 1800 seconds per chunk. The separate
workflow permits at most eight simultaneously active checker runner shards.
Each worker persists verified and still unverified geometry before evaluation.
All chunks must be accounted for before the full thirty-layer assembler runs.
Missing chunks become explicit unverified original leaves. They cannot be
removed from the target or labelled accepted. If more than 256 chunks are
required, the current single matrix refuses execution without dropping a leaf.

The final command receives `--source-revalidation REVIEW`, validates both
producer and checking source identities, and consumes the full independently
reconstructed receipt. It remains NON-PARTIAL. This checker partition changes
only the scheduling of fresh checking; original search resources, endpoints,
source and SECOND mathematical representation remain fixed.
