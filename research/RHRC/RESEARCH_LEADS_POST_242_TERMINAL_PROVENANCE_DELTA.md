# Post-#242 research delta — terminal seam closed, provenance becomes primary

## What became formally true

Merged PR #242 is the exact theorem authority for the terminal Mathlib statement seam.

Validated object:
- PR: #242
- head: `d4ccbd67223278e95e3aef728f0f42891aff6fd7`
- merge: `d2ba055243cdf0765a58ce2068a98744b7ae9432`
- tree: `0f4f82b5fc43024c52c75ec8940108830ceaf7c1`
- attached workflows: 11/11 successful

The flagship theorem is:

```lean
Zeta23.ExceptionalZero.riemannHypothesis_of_noRegularFirstBadCertificates
  (hno : NoRegularFirstBadCertificates) :
  RiemannHypothesis
```

The terminal theorem prints only the normal Lean foundations `propext`,
`Classical.choice`, and `Quot.sound`; there is no project axiom or
`sorryAx` in the promoted terminal chain.

The antecedent `NoRegularFirstBadCertificates` is **OPEN**. RH remains OPEN.

## Workflow harvest

All 11 workflows attached to the validated #242 head completed successfully.

Formal/control gates:
- CCM build — SUCCESS
- exceptional-zero build — SUCCESS
- forbidden-placeholder rejection — SUCCESS
- Python RHRC suite — SUCCESS
- R003 normalization audit — SUCCESS
- Permansson formal verification — SUCCESS

Research/regression replays preserve their previous dispositions:
- post-192 — `TRAJECTORY_RIGIDITY_UNRESOLVED`
- post-194 — `PARTIAL_TRAJECTORY_ORIENTATION`
- post-196 — `GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE`
- post-198 — `SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED`
- post-200 — `DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED`
- post-202 — `COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`
- post-214 — `FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED / FULL_SPACE_SIGN_INDEFINITE_CERTIFIED`
- post-222 — `NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED`

No research replay promotes a theorem or proves RH.

## What changed

PR #239 already closed generic safe negative-shift conjugation and real transfer
geometry. PR #240 then proved the retained Gamma/Alpha obstruction normal form,
including the conditional positive-center-deficit escape classification.

Therefore these older "next" labels are stale:
- generic safe-shift transfer reality — no longer open;
- real Gamma/Alpha theoremization — no longer open;
- terminal Mathlib RH seam — no longer open.

The live residual finite problem is narrower:
- simultaneous odd-bad exclusion remains open;
- odd-selected has an exact cross-parity negative-root endpoint, but lacks the
  downstream orientation package developed for selected-even;
- on selected-even/odd-good, #240 does **not** prove `D > 0`; the real scalar
  corridor is compressed but not contradictory.

Most importantly, #242 uses a deliberately strong sufficient antecedent. An
actual off-line zero carries stronger aperture-family ancestry than an arbitrary
`RegularCellMinimalNegativeEnergyCertificate`.

## Upstream implications

The off-line-zero route already proves:
- every sufficiently large aperture is bad at some finite size;
- every sufficiently large aperture admits a global first-bad size;
- one strict negative witness persists locally inside a fixed physical cell;
- cell-minimality is uniform for smaller sizes;
- simultaneous predecessor regularity can be selected at one retained aperture.

The next theoremization should preserve this ancestry rather than universalize
to every abstract retained certificate.

Current target:
`OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY`.

Required new information:
`PRESERVE_ARBITRARILY_LARGE_APERTURE_AND_WHOLE_CELL_BADNESS_THROUGH_BIREGULAR_SELECTION`.

## Downstream implications

Once whole-cell provenance is retained, the next mathematical question is not a
new terminal wrapper. It is whether the generated family forces an additional
canonical constraint:

```text
whole-cell badness + cell minimum + arbitrary-large aperture
    -> contact / persistent-minimum / scalar orientation / asymptotic obstruction?
```

The mature #239/#240 scalars `D`, `Gamma`, `Alpha`, `Rsharp/q^2`, and
the Riesz endpoint factors should be studied along that generated family, not
universally over arbitrary certificates.

## Resurrected routes

The contact-locus route is **RESURRECTED AS A LEAD**, not proved.

Historically the retained object was only one negative secular state, so fixed-cell
negativity did not supply a zero crossing. Whole-cell generated ancestry may
create a new dichotomy: the cell-minimal size remains bad throughout the whole
cell, or its bad locus terminates and exposes boundary/contact geometry.

This is a hypothesis for the next investigation, not theorem authority.

## New RH-relevant clues

1. The terminal seam is no longer a research problem.
2. `NoRegularFirstBadCertificates` is stronger than RH requires.
3. Off-line-zero provenance allows retained states at arbitrarily large
   apertures.
4. Odd-selected already has an exact negative-root cross-parity endpoint; it is
   an orientation problem, not a blank branch.
5. The #240 scalar system is not algebraically self-contradictory without new
   canonical information.

## Falsification checks

- Do not call whole-cell badness persistence of one fixed size or witness.
- Do not infer `D > 0`; #240's escape theorem assumes it.
- Do not infer Gamma positivity from Gamma reality.
- Do not use post-222 frozen failure to certify arbitrary retained-state exclusion.
- Generic simultaneous-bad countermodels remain a firewall: any exclusion must
  spend actual canonical arithmetic.
- A contact route still requires an exact theorem; topology alone is not enough.
- RH remains OPEN.

## Highest-leverage next moves

1. Formalize whole-cell badness as a finite CCM property.
2. Combine it with the existing bi-regular retained negative-energy certificate.
3. Prove an off-line zero generates such states in every sufficiently far-out
   cutoff cell.
4. Export arbitrary-large-aperture retained states.
5. Only then attack contact/persistence or large-`L` orientation.

Do **not** spend the next PR proving a stronger universal
`NoBiRegularFirstBadCertificates` wrapper.

## Standing questions

Given everything now formally true, what becomes possible that was not possible before?

We can optimize the finite antecedent around the actual image of the off-line-zero
construction because the downstream Mathlib seam is already compiler-checked.

If this contains a clue toward RH, where does it propagate?

Upstream into aperture freedom and whole-cell selection; downstream into the
#239/#240 scalar corridor and the remaining parity branches.

What experiment, lemma, reformulation, or connection most efficiently tells us whether the clue is real?

Preserve the whole-cell/arbitrary-large-`L` provenance in Lean first. Then test
whether that generated family supplies a canonical constraint unavailable for
arbitrary retained certificates.

**RH remains OPEN.**
