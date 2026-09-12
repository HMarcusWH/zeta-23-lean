# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after merged PR #155 = 7bd3f1028d42272fcadc347c43371b992d9c0bd7
live main tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de

latest theorem-bearing PR = #155
validated theorem head = ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
validated theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
RHRC #1005 / run 34720946254 = SUCCESS
Permansson #778 / run 34720946242 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

The validated #155 PR head and merged main are distinct commits with the same theorem tree.

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant + sign-failure endpoint
#140-#150 regular-aperture / retained negative selected state
#152 interval-certified selected-residual falsification/certification harness
#153 retained first-bad / negative-energy certificate + exact pole-prime discrepancy
#155 discrepancy integrability + generic legal Riesz smoothing
#155 source-coordinate oddness + all even jets + even M3=0
```

## What #155 adds

**PROVED:** finite prime, pole and exact pole-prime discrepancy interval integrability.

**PROVED:** left-anchored iterated discrepancy primitives, positive-order absolute continuity, and the a.e. derivative relation that recovers the previous primitive without differentiating the prime staircase.

**PROVED:** smooth source-energy composed jets and one legal integration-by-parts step; by iteration, the generic arbitrary-order Riesz identity is available under explicit endpoint-jet hypotheses.

**PROVED:** production `sourceAtomRealEnergy` is odd in the source coordinate, so all even endpoint derivatives at zero vanish.

**PROVED:** even reversal parity kills centered moment `M3`.

**NOT PROVED:** the odd endpoint derivatives required for unconditional production order-6 or order-8 Riesz specialization.

## Current frontier

```text
FB-01 retained whole-cell/Schur certificate                        PROVED / #153
FB-02 exact finite pole-prime discrepancy                          PROVED / #153
FB-03A finite discrepancy integrability                            PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic legal repeated IBP / conditional Riesz              PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + production odd jets + Riesz 6/8       OPEN / NOW
FB-03F retained transformed-negative wrapper                        OPEN
FB-04 complete transformed-residual arithmetic mechanism            OPEN
FB-05 scoped regular selected-residual nonnegative sign              OPEN
FB-06 same-state contradiction / negative-root exclusion             OPEN
FB-07 outside-strip/trivial-zero + terminal Mathlib RH seam          OPEN
RH                                                                  OPEN
```

## Current derived bridge

For production source energy `g_u`, the audited post-green calculation gives

```text
M0(u)=0 -> g_u''(omega) = -(2*pi)^2 g_(D u)(omega).
```

Together with the existing theorem `M_k(Du)=M_(k+1)(u)`, this suggests

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega) = (-1)^r*(2*pi)^(2r)*g_(D^r u)(omega)
  -> g_u^(2r+1)(0) = 2*(-1)^r*(2*pi)^(2r)*|M_r|^2.
```

**Status: DERIVED / OPEN IN LEAN.**

The next theorem PR must prove this on the genuine complex production energy, not only on a real contraction helper.

## Exact falsification memory

The legal boundary-flat `K=2` fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show that the relevant seventh/ninth source derivatives change sign. Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is a dead universal route.

The surviving target is a sign for the **complete integrated discrepancy minus archimedean/scalar residual**, or another genuinely arithmetic mechanism using the retained whole-cell ancestry.

## Next theorem-bearing slice

```text
CCM: prove source-coordinate D transport and close production Riesz jets
```

Implementation firewall:

```text
sourceEntrySecondDerivative
  -> entrywise rank-two identity
  -> complex source-matrix identity
  -> contract against conj(u_i)*u_j
  -> kill the rank-two correction using sum u_i=0
  -> identify D A D with source energy of indexMatrix *ᵥ u.
```

Expected production consequences remain DERIVED until Lean validates them:

```text
boundary-flat: jets 1..6 vanish
even boundary-flat: jets 1..8 vanish
```

## Documentation state

Current living synthesis:

```text
research/RHRC/RESEARCH_LEADS.md
research/RHRC/RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md
research/RHRC/CURRENT_RESEARCH_PLAN.md
research/RHRC/OBSTRUCTION_LEDGER.md
research/RHRC/DEAD_ROUTES.md
```

External reviewer material remains discovery evidence unless independently reproduced or theoremized.

## Firewalls

- RH remains OPEN.
- theorem authority is through #155 only.
- machine claim promotion remains separate.
- a retained negative source-channel energy is not a contradiction.
- generic Riesz smoothing does not itself prove production order 6/8.
- complex production transport must not be inferred from real contraction theorems.
- pointwise smoothed-integrand positivity is falsified as a universal mechanism.
- the #152 harness is scoped falsification/certification infrastructure, not theorem authority.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib RH wrapper without explicit final bookkeeping.

**RH remains OPEN.**
