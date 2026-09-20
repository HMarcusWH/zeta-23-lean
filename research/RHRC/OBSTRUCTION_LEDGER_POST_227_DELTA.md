# Obstruction ledger delta after PR #227

> **Claim firewall: RH remains OPEN.**

## What became formally true

**PROVED.** PR #226 closes predecessor-correction proportionality:
`a_N=-((2N-1)/6)d_N`.

**PROVED.** PR #227 closes independent alpha/Gamma freedom in the current cross-parity transfer:
`Gamma=1+kappa(1-alpha)`, including denominator-free safe and zero-shift one-coefficient forms, kernel-direction collapse, and the selected-even bi-regular normal form.

## What changed

The previous post-#224 obstruction
```text
PREDECESSOR-CORRECTION PROPORTIONALITY REQUIRED
```
is closed by #226.

The previous conditional alpha/Gamma and zero-shift consequences are formalized by #227.

The active obstruction is now:
```text
OBS-059I
  OPEN
  one-coefficient transfer proved
  generic correction-functional Riesz representation not yet exported
  canonical mixed-resolvent control still required
```

## Upstream implications

The correction functional should be represented once by the safe-resolvent vector `R b` rather than handled through separate alpha/Gamma calculations. This is a dependency-graph compression opportunity.

## Downstream implications

After
`chi(y)=<R b,y>/<c,c>`
is formalized, alpha becomes a direct mixed-pairing corollary and quantitative norm bounds become available without a sign assumption.

## Resurrected routes

A retained-state Gram/angle comparison between `R b`, the transported-index correction `d`, and source-functional covectors is worth retesting. Universal full-carrier sign/proportionality remains dead at the #215 scope.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** the obstruction may reduce to canonical phase/alignment information for one mixed resolvent pairing rather than a two-coefficient transfer problem.

**OPEN:** no theorem currently supplies that phase/alignment information.

## Falsification checks

- Mixed resolvent pairing is not automatically real or positive.
- Generic geometry remains insufficient by #205.
- Negative-shift and zero-shift states are not interchangeable by #216.
- Selected-even remains an assumption.
- No division by alpha, Gamma, source moment, or overlap is permitted without a nonzeroness theorem.

## Highest-leverage next moves

1. Formalize `CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION`.
2. Specialize to alpha and derive a safe magnitude bound.
3. Attack the canonical `b`/`d` angle and Gram structure adversarially.
4. Compose only surviving constraints with the retained complete-source functional.
5. Keep odd-selected closure and the terminal Mathlib RH seam explicit.

## Ledger update

Closed:
- post-#224 predecessor-correction proportionality obstruction;
- independent alpha/Gamma transfer freedom.

Open:
- generic correction-functional Riesz representation;
- canonical mixed-pairing control;
- simultaneous odd-bad exclusion;
- odd-selected closure;
- parity-complete retained-state exclusion;
- terminal Mathlib RH seam;
- RH.
