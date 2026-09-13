# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after merged PR #163 = bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd
live main tree = c397b3a015ea54e38ecfe626d6e29556fe963839
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
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
#163 mixed quadratic-normal source jet x retained Riesz boundary coupling
```

## What #163 adds

**PROVED:** the exact production mixed quadratic-normal observable has seventh source-coordinate jet

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v)
```

for even boundary-flat carriers, with the corresponding norm-square identity.

**PROVED:** the finite-prime contribution to `explicitCanonicalSourceMoment` samples the same `quadraticNormalSourceAtom` at the production prime-source coordinates.

**PROVED:**

```text
2*(2*pi)^4*(R8-R9) = S8(L)*|h_v^(7)(0)|^2
```

for the exact complete-channel Riesz energies.

**PROVED:** on the retained even-shifted trial, the same identity holds and strict R8 negativity yields

```text
2*(2*pi)^4*R9 < -S8(L)*|h^(7)(0)|^2
```

without assuming any sign for `S8(L)`.

**PROVED:** under even-selected + odd-good, `crossParityGamma != 0`.

**NOT PROVED:** a global sourceMoment/M4 equivalence or implication, finite-sample determination of the seventh jet, endpoint-scalar sign/nonvanishing, simultaneous-parity-bad exclusion, odd-selected branch closure, an opposing arithmetic sign/rigidity theorem, negative-root exclusion, or RH.

## Current frontier

```text
FB-01 retained certificate                                      PROVED / #153
FB-02 exact discrepancy                                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                  PROVED / #155
FB-03E-F complex transport / retained transformed negativity    PROVED / #157
FB-04A moment jets + signed Riesz boundary recurrence            PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source           PROVED / #161
FB-04C mixed quadratic-normal jet x Riesz boundary coupling     PROVED / #163
FB-05 independent contradiction-producing arithmetic restriction OPEN / NOW
FB-06 negative-root exclusion                                   OPEN
FB-07 terminal Mathlib RH seam                                  OPEN
RH                                                               OPEN
```

## Post-green clue

The same retained even shifted negative state now carries four exact views:

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda)*explicitCanonicalSourceMoment(u_lambda)
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2.
```

The arithmetic obstruction is now exposed rather than hidden in the analytic coupling. The open problem is: what independent canonical arithmetic feature makes these constraints incompatible?

## Exact falsification memory

The K=2 boundary-flat vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

still kill the universal pointwise fixed-sign smoothed-integrand route. The exact integrated recurrence, same-state composition and mixed-jet boundary rewrite survive.

## Next theorem-bearing slice after this sync

Do not pre-commit to a positivity theorem. First falsify the principal FB-05 candidates:

```text
canonicalPolePrimeRieszEndpointScalar L 8 sign/nonvanishing
production prime-sample -> seventh-jet rigidity
simultaneous even+odd badness under exact arithmetic
odd-selected branch closure
```

If endpoint-scalar positivity or nonvanishing survives the exact Lean-normalized sweep, formalize the weakest true statement. If it fails, pivot immediately rather than building a false sign route.

## Documentation state

Current living synthesis:

```text
research/RHRC/RESEARCH_LEADS.md
research/RHRC/RESEARCH_LEADS_POST_163_MIXED_SOURCE_RIESZ_ARITHMETIC_FRONTIER_DELTA.md
research/RHRC/CURRENT_RESEARCH_PLAN.md
research/RHRC/OBSTRUCTION_LEDGER.md
research/RHRC/DEAD_ROUTES.md
```

## Firewalls

- RH remains OPEN.
- theorem authority is through #163 only.
- machine claim promotion remains separate.
- retained/shifted transformed negativity is not a contradiction.
- exact Riesz boundary identities are not sign theorems.
- R8/R9 results remain conditional on even parity where stated.
- #159's self-energy moment jets are distinct from #163's independently proved mixed source-pairing jet.
- `explicitCanonicalSourceMoment != 0` does not imply `M4 != 0`, nor conversely.
- exact finite-prime samples do not by themselves determine the local seventh jet.
- endpoint-scalar sign/nonvanishing remains open.
- simultaneous even/odd badness remains open.
- selected parity cannot be assumed even WLOG.
- no division by alpha/Gamma/overlap/source moment without theorem-backed nonzeroness.
- pointwise fixed-sign smoothing remains dead.
- `D` remains algebraic, not unitary/isometric.

**RH remains OPEN.**
