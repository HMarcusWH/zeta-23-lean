# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after merged PR #161 = ef29b45de683962122c1e898ed31bf9417757125
live main tree = b080572e87068889a72b4e612f99ddf0bd67f482
latest theorem-bearing PR = #161
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS
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
#161 same-state shifted Riesz x cross-parity source obstruction
```

## What #161 adds

**PROVED:** `parityBad_of_negative_eigenmode` and arbitrary-parity predecessor nonnegativity from retained first-bad ancestry.

**PROVED:** a genuine negative secular-root trial has exact negative canonical/source-channel energy; in the even sector the same trial has strict complete Riesz-8 negativity and the exact Riesz-9 / `M4` boundary inequality.

**PROVED:** under opposite-parity goodness the odd secular scalar is nonzero.

**PROVED:** at the retained even first-bad root,

```text
odd secular scalar
  = Gamma * explicitCanonicalSourceMoment(even shifted trial).
```

**PROVED:**

```text
odd-good -> explicitCanonicalSourceMoment != 0
```

and therefore

```text
odd successor bad
OR
explicitCanonicalSourceMoment(even shifted trial) != 0.
```

**NOT PROVED:** mixed source-pairing seventh jet, a sourceMoment/M4 coupling theorem, simultaneous-parity-bad exclusion, odd-selected branch closure, an opposing arithmetic sign/rigidity theorem, negative-root exclusion, or RH.

## Current frontier

```text
FB-01 retained certificate                                      PROVED / #153
FB-02 exact discrepancy                                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                  PROVED / #155
FB-03E-F complex transport / retained transformed negativity    PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence            PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source           PROVED / #161
FB-04C mixed source-pairing jet -> M4 rigidity                  DERIVED / OPEN / NOW
FB-05 independent contradiction-producing arithmetic restriction OPEN
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Post-green clue

The same retained even shifted negative state now carries three exact views:

```text
R8(u_lambda) < 0
R9(u_lambda) < -2*(2*pi)^8*S8(L)*|M4(u_lambda)|^2
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda).
```

This converts the previous composition question into a rigidity question: what extra canonical arithmetic relation can make those simultaneous constraints impossible?

The next theorem lead is the mixed quadratic-normal source observable expected to satisfy

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
```

for even boundary-flat `v`. This remains **DERIVED / OPEN IN LEAN**.

## Exact falsification memory

The K=2 boundary-flat vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

still kill the universal pointwise fixed-sign smoothed-integrand route. The exact integrated recurrence and same-state composition survive.

## Next theorem-bearing slice after this sync

Preferred design:

```text
CCM: prove mixed quadratic-normal source jets and connect M4 to the shifted source defect
```

Before strong theorem investment, falsify simultaneous even+odd badness in exact generic/rank-one controls and test whether nonzero explicit source moment and nonzero `M4` can separate on canonical shifted states.

## Documentation state

Current living synthesis:

```text
research/RHRC/RESEARCH_LEADS.md
research/RHRC/RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md
research/RHRC/CURRENT_RESEARCH_PLAN.md
research/RHRC/OBSTRUCTION_LEDGER.md
research/RHRC/DEAD_ROUTES.md
```

## Firewalls

- RH remains OPEN.
- theorem authority is through #161 only.
- machine claim promotion remains separate.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz boundary identities are not sign theorems.
- R8/R9 results remain conditional on even parity where stated.
- #159's self-energy moment jets do not prove the mixed source-pairing jet.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely.
- simultaneous even/odd badness remains open.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothing remains dead.
- `D` remains algebraic, not unitary/isometric.

**RH remains OPEN.**
