# Post-#245 obstruction ledger delta

## What became formally true

PR #245 proves `NoRegularFirstBadCertificates ↔ RiemannHypothesis` and
`NoArbitrarilyLargeWholeCellRetainedFamily ↔ RiemannHypothesis`.

The post-#245 arithmetic-criterion PR (candidate) proves the arithmetic normal
form

```text
canonicalSourceChannelEnergy L K x
  = -canonicalPrimeRemainderEnergy L K x - canonicalPrimeFreeBudget L K x
```

and that `CanonicalPrimeRemainderDominance`, canonical finite Weil positivity,
order-six Riesz positivity, and eventual generated retained Riesz-six
nonnegativity are each equivalent to `RiemannHypothesis`.

## Workflow harvest

All 11 workflows attached to the #245 head completed successfully. post-200
remains `DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED`; post-202 remains
`COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`. No replay promotes a theorem.

## What changed

`OBS-059I` now has the following compressed terminal view:

```text
terminal Mathlib statement seam                      CLOSED / #242
whole-cell off-line provenance                       CLOSED / #243
arbitrarily-large generated retained family          CLOSED / #243

NoRegularFirstBadCertificates                         RH-EQUIVALENT / #245
generated-family eventual aperture bound              RH-EQUIVALENT / #245
generated retained Riesz-six nonnegativity            RH-EQUIVALENT / candidate
canonical prime-remainder dominance                   RH-EQUIVALENT / candidate
sub-RH gate remaining on this route                   NONE
RH                                                     OPEN
```

The obstruction is no longer a missing lemma inside the finite canonical
machinery. It is RH, expressed as one linear inequality in the classical
remainder `R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x`.

## Upstream implications

The unconditional arithmetic libraries (`ChebyshevMertens`, `GammaFacts`) are
fully theoremized but supply magnitude, not the RH-strength cancellation the
inequality requires. `MediumPNT.lean` is not in the verified build graph.

## Downstream implications

A proof of the dominance inequality composes to Mathlib's `RiemannHypothesis`
through already-compiled theorems. Nothing else is needed downstream, and
nothing downstream can substitute for it.

## Resurrected routes

None. Contact theory remains fallback only; its terminal is again certificate
exclusion and therefore RH-equivalent.

## New RH-relevant clues

The prime-free budget is explicit. All arithmetic enters through `R` on
`[1, e^L]`, weighted by the smooth source-atom derivative of the retained
carrier.

## Falsification checks

The exact first failed inequality is compiled:
`exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero`.
Any argument claiming to rule it out must be checked against the #245
equivalence: it is a claimed proof of RH and must contain RH-strength
information about `R`.

## Highest-leverage next moves

Do not open another terminal-gate PR. Either supply genuinely new
RH-strength arithmetic about `R`, or treat this route as fully reduced.

## Standing questions

Can the retained-state provenance restrict which scales of `R` the canonical
carrier probes? Any answer remains RH-equivalent at the terminal, but could
sharpen the quantitative picture.

**RH remains OPEN.**
