# D2 — preserve the already approved execution; do not restart it

## 1. Identities

- Active approved execution: GitHub run **38569316691**.
- Producer head: **a55fbeeed6500bffe2ccac3960258ca5c590c7ee**.
- Producer tree: **7ffdf5095db2d54ef97897c19797886d145b65d2**.
- Frozen plan SHA256: **433107bbfe412625223fe1f08da36ca7d837bd82e7a536fc50a2d447886cf6ef**.
- Ancestral campaign run 38461259594 at `4789c93f…` was cancelled during its independent checker; its final NON-PARTIAL gate failed because that checker receipt was absent.
- Ancestor archive: **artifact 11865755269**, SHA256 **0077e514187a0cb326170b7b13e9e699d898a2ba10d8b4b20fa75a5cd6072b92**. Do not infer an artifact ID from a title or increment.

The historical archive records 256 completed SECOND children, 288 old receipt hashes, 66,395 accepted leaves and 460 unrun children. An unrun child is not a failed attempted child eligible for an implicit retry.

## 2. Fixed approved bounds

460 original unique children: Q13 eight, Q14 244, Q15 208. Two sequential waves 256 + 204. Same corrected SECOND algorithm. 512-bit producer; maximum depth 48; 8192 nodes; 1800 supervisor seconds per unique child. Maximum 8 workers globally, 230 additional search runner-hours. Checkpoints every 45 seconds. Durable claim before process launch. Supervisor clock starts before Popen. A failed upload stops further work; a certified negative triggers the prescribed global stop.

No same-child timeout retry, budget reset, geometry substitution, new fourth-order fallback or competing historical shard workflow is authorized. This review performs no dispatch/cancel/retry. If the existing authorized run needs a new action outside the protocol, stop and obtain a new explicit scope/budget decision.

## 3. Read-only reconciliation first

Fetch the actual run and paginate ALL jobs, artifacts and child receipts. The connector convenience wrapper exposes only its first page; do not stop there. Use exact artifact names plus immutable IDs and verify their returned digests. Filter the known protocol artifacts; do not select a latest similarly named artifact belonging to another head.

Build a 460-row table before scheduling any still-authorized work: childID, original rational interval, claimed_at, worker/supervisorelapsed, source/planhash, finaldisposition, acceptedleaves, unresolvedpieces, artifactID/digest and whether it consumed its unique attempt. Every child must appear once. A missing artifact stays missing, not a success or an unclaimed reset.

Reconcile global resource accounting across both waves and all retries/interruptions, including reservations held by claimed but unfinished children. Never reset the eight-worker limit independently for each matrix or process. The old proof workflow and observer jobs do not license additional arithmetic attempts.

## 4. Completion conditions

Reassembly preserves all old accepted leaves and includes only actually returned new accepted coverage. Exact rational endpoints and ancestors are retained. Verify every gap, overlap, duplicated child, uncovered seam and zero-dimensional edge case.

A separate no-search checker reevaluates every accepted leaf at 768 bits against the exact native mathematical source. It covers all 30 layers, both parities and the continuous domain [1/512, log 16]. The log16 bracket has a proved correct orientation. A symbolic seam value equal to zero is not a claim that every point of an Arb interval uses the same prime cutoff; the checker must retain its seam-aware source contract.

Accept D2 only if:

- all 30 layer payloads are present;
- all 460 child geometries and their accounting reconcile;
- no unrun, missing, unresolved, unverified or nonfinite leaves remain;
- the whole mathematical cover is reevaluated at 768 bits;
- every source/hash/ancestor/plan relation matches;
- the NON-PARTIAL gate explicitly succeeds.

Search success, candidate assembly, 18 feasibility boxes, a point grid, or old 26/30 coverage does not satisfy this gate. A successful diagnostic job may report UNRESOLVED; preserve that exact scientific disposition.

## 5. Authority and new final source

D2 is CERTIFIED FINITE only after the complete independent checker. It is not automatically a Lean theorem or a term of `hWindows`. A formal checker bridge is a separate mathematical deliverable not silently added to this continuation.

The D2 producer head differs from the proof head. If later proof/metadata changes leave the numerical source blobs unchanged, record the exact checked source equivalence. If the mathematical source changes, do not replace old hashes with new ones; the final certificate must be revalidated under an explicitly approved plan. No raw historical receipt is edited to appear freshly produced.

Final proof and numerical release evidence are separate gates, joined only by the final source-equivalence/lineage audit. Neither gates the other's mathematical theorem as an assumption.
