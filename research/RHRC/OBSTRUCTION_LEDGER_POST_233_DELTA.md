# Obstruction ledger delta after PR #233

> **RH remains OPEN.**

## What became formally true

PR #233 closes the target `RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK` on the
retained selected-even / odd-good branch. The exact sharp radius keeps the
negative-shift term `lam * ||R a||^2` before any outer relaxation.

## Workflow harvest

The validated #233 head completed 11/11 attached workflows green. Formal Lean
validity, no-placeholder/project-axiom gates, and all attached research
replays passed. No bounded research replay was upgraded to a theorem.

## What changed

`OBS-059I` remains OPEN, but its descriptive target changes.

Consumed target:

```text
RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK = PROVED_PR_233
```

New active target:

```text
RETAINED_SOURCE_DISK_SECULAR_INTERSECTION
```

Required new information:

```text
M4_FREE_RETAINED_DISK_HALFPLANE_COMPATIBILITY
```

The one-step-domination certificate is no longer independent information when
sector goodness is already assumed.

## Upstream implications

Any dependency graph counting both `not ParityBad` and
`canonicalOneStepDomination` as separate constraints must be compressed.

No control-semantic authority moves: PR #117 remains the selected first-break
anchor.

## Downstream implications

The next obstruction is whether the same retained point can simultaneously
satisfy the completed odd-secular half-plane and the #233 sharp disk.

A successful intersection theorem should remove `M4` from its final
necessary condition rather than introduce a new free overlap.

## Resurrected routes

Three-vector Gram geometry remains a secondary lead if the disk/half-plane
composition is insufficient. It should not be the next default because it
introduces mixed overlaps that are not yet theorem-controlled.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** the retained source state may be compressed to a
source-phase/radius alternative involving only `lam`, `S`, shell geometry,
`Ec`, `C`, `R a`, and the odd secular trial norm.

This would be the first retained constraint in this sequence where `M4`
drops out entirely.

## Falsification checks

Do not infer emptiness from intersection.

Do not use the outer disk in place of the sharp disk until the sharp
composition is theorem-locked.

Do not infer `Re(S)>0` unless the radius-compensation branch has separately
been excluded.

Do not transfer the selected-even result to odd-selected by symmetry without
an exact theorem.

## Highest-leverage next moves

Formalize and validate the exact disk/half-plane intersection, then adversarially
test whether the resulting `M4`-free condition is genuinely stronger than
the existing secular and Gram inequalities separately.

## Standing questions

Given everything now formally true, what becomes possible that was not
possible before?

Where does the new Gram radius propagate when composed with the retained
secular budget?

What is the cheapest exact countermodel or canonical-kernel test that decides
whether the `M4`-free compatibility law carries independent information?
