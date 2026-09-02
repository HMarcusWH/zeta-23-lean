# Research leads delta after PR #94 / F1

Date: 2026-09-02

Authority at creation:

~~~text
main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
PR #94 head = d357c1511dba8678eb3a3a10944596c33a65fa11
RHRC #667 = SUCCESS
Permansson #440 = SUCCESS
RH = OPEN
~~~

This is a post-green delta. Lean/compiler authority remains primary.

## Promoted

- **R003_BOUNDARY_FLAT_WCONT_APPROXIMATION** — PR #93 closes legal fixed-aperture approximation in the exact WCONT topology.
- **R003_STRICT_FINITE_NEGATIVE_WEIL_TRANSFER** — PR #94 preserves strict negative genuine-W value in one legal boundary-flat finite vector.
- **R003_FINITE_CANONICAL_NEGATIVE_OBSTRUCTION** — PR #94 / F1 forces a negative canonical finite direction with M0=M1=M2=0 from any off-line zero.

## Dependency graph change

The primary bottleneck moved from analytic/legalization to finite structural exclusion.

The old automatic order

~~~text
K0 parity -> K1 aperture -> K2 displacement -> K3 arithmetic
~~~

is no longer binding.

## New active lead — K0-F1 constrained canonical sector

PROVED inputs:

~~~text
BoundaryFlatCoefficients N u
[D,M] = g 1^T - 1 g^T.
~~~

DERIVED:

~~~text
1^T u = 0
1^T D u = 0
1^T D^2 u = 0.
~~~

Expected exact consequence:

~~~text
[D,M] D^k u lies in span{1},  k=0,1,2.
~~~

This remains a LEAD until theorem-locked.

## New active lead — constrained compression / KKT

After canonical Hermitianity and the constrained subspace are packaged, test whether F1 yields a negative compressed eigenvalue/minimizer.

Candidate forms:

~~~text
P_V M P_V u = lambda u, lambda < 0
~~~

or an equivalent KKT equation.

This is a LEAD, not a theorem.

## Falsification guardrails

- D need not preserve the full boundary-flat sector.
- only moments 0,1,2 vanish;
- an F1 witness is not automatically a full eigenvector;
- low displacement rank alone is insufficient;
- DR-010 remains dead;
- universal constrained positivity would be RH-relevant terminal-strength mathematics.

**RH remains OPEN.**
