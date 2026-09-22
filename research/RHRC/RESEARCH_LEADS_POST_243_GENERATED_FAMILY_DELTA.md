# Post-#243 research delta — generated family becomes the final gate

## What became formally true

Merged PR #243 preserves the counterexample provenance that the previous terminal
interface discarded.

Validated object:
- PR: #243
- head: `7b9cc503c50478000ce4ac53c61d4a96ed2d4050`
- merge: `be58e98a843ceeceb93a7729d95a3fb6bb0b60df`
- tree: `abf8ff5b429adea4adaaec28e182dc30495b1ba8`
- attached workflows: 11/11 successful

The flagship theorem is:

```lean
Zeta23.ExceptionalZero.
  exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero
```

It proves:

```text
off-line zero
  -> for every real A,
     some whole-cell bi-regular retained negative-energy certificate
     has retained aperture L > A.
```

This is stronger provenance than a single retained certificate and weaker than
claiming any universal certificate exclusion.

RH remains OPEN.

## Workflow harvest

All 11 attached workflows completed successfully.

Formal/control:
- CCM build — SUCCESS
- ExceptionalZero build — SUCCESS
- forbidden-placeholder gate — SUCCESS
- claim lint / registry lint / promoted-binding lint — SUCCESS
- Control-v2 suite — SUCCESS
- R003 normalization audit — SUCCESS
- Permansson formal verification — SUCCESS

Research/regression:
- post-190 — general canonical realizability remains unresolved after the
  scalar-aperture exclusion of the original reflected witness;
- post-192 — `TRAJECTORY_RIGIDITY_UNRESOLVED`;
- post-194 — `PARTIAL_TRAJECTORY_ORIENTATION`;
- post-196 — `GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE`;
- post-198 — `SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED`;
- post-200 — `DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED /
  NO_UNIQUE_PRIMARY_LOCK`;
- post-202 — `COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`;
- post-214 — full-space dual independence/sign-indefiniteness preserved;
- post-222 — `NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED`.

No research replay promotes a theorem or proves RH.

## What changed

The active question is no longer how to preserve off-line provenance. #243 does
that.

The active question is now one exact generated-family incompatibility:

```text
Can whole-cell bi-regular retained negative-energy certificates
exist at arbitrarily large aperture?
```

A negative answer is already sufficient because #243 produces such a family
from any off-line zero and #242 already closes the Mathlib RH statement seam.

The universal endpoint `NoRegularFirstBadCertificates` remains a valid strong
sufficient condition but is no longer the preferred target.

## Upstream implications

The counterexample image can now be attacked using only properties that hold on
the generated family. We do not need a uniform theorem over every abstract
retained certificate.

The cheapest closing statement is an eventual retained-aperture upper bound:

```text
exists A such that every WholeCellBiRegularNegativeEnergyCertificate
has retained L <= A.
```

Any equivalent generated-family-specific contradiction is equally acceptable.

## Downstream implications

Once that one bound is proved:

```text
eventual generated-family exclusion
  + #243 arbitrary-large family from off-line zero
  -> no off-line zero
  + #242 terminal seam
  -> Mathlib.RiemannHypothesis.
```

No new contact theory, parity topology, or terminal translation is required.

## Resurrected routes

Large-aperture production geometry becomes the first-line route because #243
allows the retained aperture to be pushed arbitrarily far out.

The exact production decomposition and the explicit `-log L` scalar extraction
are existing theoremized ingredients worth testing first.

Contact-locus geometry remains a fallback only if the direct eventual-bound
route fails.

## New RH-relevant clues

The final gate may be much weaker than any branch-by-branch contradiction:
one eventual upper bound on generated retained aperture suffices.

This is the most compressed RH-facing interface currently present in the repo.

## Falsification checks

- Do not infer an eventual bound merely from the explicit `-log L` term; the
  discrepancy and reduced archimedean channels may compensate.
- Do not assume `D > 0`, Gamma positivity, simultaneous-bad exclusion, or
  odd-selected closure.
- If the direct large-`L` route reduces to an uncontrolled exact term, record
  that exact term as the final missing inequality rather than building a broad
  new theory around it.
- RH remains OPEN until the generated-family gate itself is proved.

## Highest-leverage next moves

1. Formalize the generated-family aperture-bound proposition as the exact final gate.
2. Prove it composes directly to no off-line zero and then to Mathlib RH.
3. Test the existing canonical large-`L` decomposition against the generated
   retained state.
4. If one exact term remains uncontrolled, isolate only that inequality.

## Standing questions

What exact theorem would make the generated retained aperture bounded?

Does the current production decomposition already imply such a bound?

If not, what single exact retained-state term prevents the contradiction?

What is the smallest theorem that controls that term without restating RH?

**RH remains OPEN.**
