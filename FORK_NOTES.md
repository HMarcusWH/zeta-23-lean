# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

Live GitHub head + exact compiler/CI are authoritative dynamically.

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
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
#161 same-state shifted Riesz x cross-parity source obstruction
#163 mixed quadratic-normal source jet x retained Riesz boundary coupling
```

No theorem-bearing PR has superseded #163.

## Research packages since theorem authority

```text
#165 exact executable Riesz-8 endpoint-scalar audit
#166 theorem-aligned shifted-state discriminator
#167 Q16 near-critical scalar-barrier / interval-method audit
#168 log17 boundary-flat threshold-jet / Q17 microscope
#170 theorem-aligned Schur visibility / background-drift audit
#172 threshold-to-threshold Schur barrier falsification / q13 near-critical target
```

### #172

The threshold-to-threshold research pass tested genuine nonzero von-Mangoldt intervals across several q/N/parity states. No sampled bad successor was found, but the arithmetic-entry heuristic changed materially.

Finite Arb replay now contains both signs:

```text
q9 / even   current-q entry lift  NEGATIVE_CERTIFIED
q13 / even  current-q entry lift  NEGATIVE_CERTIFIED
q16 / odd   current-q entry lift  POSITIVE_CERTIFIED
```

The most dangerous sampled state is `q=13 -> 16, N=2, K*=3, even`. At the quantized near-minimum, Arb certifies

```text
full unit-shell pivot      ~= +5.8401616e-12
q-removed background       ~= +1.2217611e-11
q13 entry lift             ~= -6.3774491e-12
```

with H1 predecessor positivity certified there.

So the isolated arithmetic entry is not universal "replenishment". The current object is the complete physical scalar barrier.

## Current frontier

```text
FB-01 retained certificate                                      PROVED / #153
FB-02 exact discrepancy                                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                  PROVED / #155
FB-03E-F complex transport / retained transformed negativity    PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence           PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source           PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling     PROVED / #163
FB-05 independent contradiction-producing arithmetic restriction OPEN / NOW
  current research slice: q13/N2/K3/even 2x2 scalar determinant barrier
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Current post-green clue

At `N=2 -> K*=3`, the exact executable parity carrier has dimensions 1 -> 2. In theorem-aligned `[W|c]` coordinates,

```text
H(L) = [[a,b],[b,d]]
H1   <-> a > 0
P    = d - b^2/a
Delta_2 = a*d - b^2
```

and therefore, in H1 scope,

```text
sign P = sign Delta_2.
```

This makes the q13/even target a genuinely dependency-reduced finite laboratory.

The next pass should rigorously resolve whether `Delta_2` can cross zero while `a>0` across `log13 <= L <= log16`.

Because the production backend tracks `Q=floor(exp L)`, the rigorous interval must respect physical subcells `[log13,log14]`, `[log14,log15]`, `[log15,log16]` unless zero-weight Q=14/15 inertness is separately certified.

## Important non-revivals

This is **not**:

```text
global aperture Loewner monotonicity
global minimizing-Schur monotonicity
brute dependency-heavy full-matrix Arb subdivision
endpoint-scalar positivity as a standalone contradiction
prime-sample -> local-jet implication by analogy
summing independent channel Schur pivots
universal positive arithmetic threshold replenishment
```

The q13 2x2 scalar route instead satisfies the existing escape condition from the failed #167 full-matrix interval representation: reduce the dependency-heavy matrix problem to a better-conditioned scalar formulation.

## Next theorem-bearing slice

Do not theoremize the q13 finite cell merely because a rigorous scalar certificate becomes possible. A positive q13-cell certificate would be a method/structure result, not global FB-05 closure.

First identify why the low-dimensional scalar stays positive or find a certified H1 crossing. If the resulting arithmetic inequality generalizes beyond this one finite cell and supplies independent information rather than restating successor positivity, then theoremize the weakest useful statement and compose it with the exact #161/#163 retained state.

## Permanent firewalls

- research evidence through #172 does not move theorem authority beyond #163;
- endpoint-scalar positivity alone is not first-bad exclusion;
- arithmetic entry lift is sign-indefinite in the tested finite canonical states;
- physical H1 does not imply q-removed-background H1;
- q13 whole-cell positivity alone would not close FB-05;
- large channel cancellation makes coarse component-sign reasoning unsafe;
- finite differences/quadrature are not derivative theorems;
- exact executable algebra is not a Lean theorem;
- finite Arb evidence is scoped only to its certified points/intervals;
- sourceMoment nonzero does not imply `M4` nonzero, nor conversely;
- simultaneous parity badness remains open;
- selected parity is not even WLOG;
- `UNRESOLVED` is not sign evidence;
- negative-root exclusion and RH remain open.

**RH remains OPEN.**
