# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after merged PR #159 = 63862cd80501754c6c6599ffea09b874a327dae4
live main tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
latest theorem-bearing PR = #159
validated theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant
#140-#150 regular-aperture / retained selected first bad
#152 interval-certified selected-residual harness
#153 retained first-bad negative-energy certificate + exact discrepancy
#155 legal generic Riesz smoothing + source oddness/even jets
#157 complex production D transport + exact complete Riesz 6/even 8 + retained negativity
#159 general moment-prefix odd jets + exact signed Riesz boundary recurrence
```

## What #159 adds

**PROVED:** exact first complex source-energy jet and a general moment-prefix odd-jet theorem.

**PROVED:**

```text
g^(7)(0) = -2*(2*pi)^6*normSq(M3)
```

for boundary-flat carriers, and

```text
g^(9)(0) = 2*(2*pi)^8*normSq(M4)
```

for even boundary-flat carriers.

**PROVED:** generic signed Riesz boundary recurrence for the pole-prime and complete transformed channels.

**PROVED:** retained R6->R7 and, under even parity, R8->R9 exact moment-square boundary decompositions.

**NOT PROVED:** endpoint-scalar positivity, same-state shifted Riesz/cross-parity source composition, mixed source-pairing seventh jet, an opposing arithmetic sign, negative-root exclusion, or RH.

## Current frontier

```text
FB-01 retained certificate                                      PROVED / #153
FB-02 exact discrepancy                                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                  PROVED / #155
FB-03E-F complex transport / retained transformed negativity    PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence            PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source           OPEN / NOW
FB-04C mixed source-pairing jet -> M4                           DERIVED / OPEN
FB-05 independent contradiction-producing arithmetic restriction OPEN
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Post-green clue

The first Riesz boundary term is no longer merely a clue; its exact self-energy form is theorem-backed. The stronger new clue comes from composing it with the existing cross-parity source stack.

At an even negative secular root the existing theorem gives

```text
odd secular scalar
  = overlap * evenQuadraticSourceMoment(even shifted trial),
```

with `evenQuadraticSourceMoment = explicitCanonicalSourceMoment` theorem-backed.

Global first-bad ancestry already gives smaller-size predecessor nonnegativity in both parities. The next theorem should therefore align the even negative secular trial with #159's Riesz-8/Riesz-9 boundary and derive

```text
odd successor bad
OR
explicit canonical source moment != 0.
```

The subsequent mixed-jet lead is

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
```

for the quadratic-normal source pairing. This remains **DERIVED / OPEN IN LEAN**.

## Exact falsification memory

The K=2 boundary-flat vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

still kill the universal pointwise fixed-sign smoothed-integrand route. The exact integrated recurrence survives.

## Next theorem-bearing slice after this sync

Preferred design:

```text
CCM: couple even first-bad secular roots to Riesz and cross-parity source obstruction
```

It should use existing theorem interfaces rather than introduce simultaneous zero-shift regularity or a parallel certificate. No source factor may be divided out without a separate theorem.

## Documentation state

Current living synthesis:

```text
research/RHRC/RESEARCH_LEADS.md
research/RHRC/RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md
research/RHRC/CURRENT_RESEARCH_PLAN.md
research/RHRC/OBSTRUCTION_LEDGER.md
research/RHRC/DEAD_ROUTES.md
```

## Firewalls

- RH remains OPEN.
- theorem authority is through #159 only.
- machine claim promotion remains separate.
- retained transformed negativity is not a contradiction.
- exact Riesz boundary identities are not sign theorems.
- R8/R9 results remain conditional on even parity where stated.
- #159's self-energy moment jets do not prove the mixed source-pairing jet.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothing remains dead.
- `D` remains algebraic, not unitary/isometric.

**RH remains OPEN.**
