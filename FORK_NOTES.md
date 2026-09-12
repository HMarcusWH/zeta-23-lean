# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after merged PR #153 = 474a88d76ecd2f4eee6178685b2e8d8b104171ca
live main tree = dd69f1c612047f2d2f15a7ba158664634284b42e

theorem-state anchor = PR #153 merge 474a88d76ecd2f4eee6178685b2e8d8b104171ca
validated theorem head = b6622dadab911008c0a7238e9dc711c6f9946302
validated theorem tree = dd69f1c612047f2d2f15a7ba158664634284b42e
RHRC #994 / run 34709905190 = SUCCESS
Permansson #767 / run 34709905198 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant + sign-failure endpoint
#140 eventual aperture freedom + predecessor regularity scaffold
#142 fixed-cell continuity + same-witness persistence
#144 exact frozen production source/predecessor + logarithmic-cover scaffold
#145-#146 removable scalar analyticity + production bridge
#148 fixed-unit alpha/beta/gamma parameter holomorphy
#150 assembled source/predecessor holomorphy + determinant rigidity
#150 open-interval actual predecessor regularity
#150 cell-minimal regular first bad + exact negative source-channel energy
#152 interval-certified selected-residual falsification/certification harness
#153 retained first-bad / negative-energy certificate structures
#153 exact finite pole-prime discrepancy and full-channel normal form
```

## What #153 adds

**PROVED:** `RegularCellMinimalFirstBadCertificate` retains the whole-cell least-bad ancestry and selected-aperture smaller-size goodness together with the actual selected regular predecessor.

**PROVED:** `RegularCellMinimalNegativeEnergyCertificate` retains predecessor nonnegativity, the safe negative explicit root, exact root equation, unique zero-shift preimage `A x0=b`, strict parity energy negativity and strict production source-channel negativity.

**PROVED:** `exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero` propagates a hypothetical off-line zero directly to that retained certificate.

**PROVED:** `sourceAtomRealEnergy` is smooth in the source coordinate.

**PROVED:** the production pole energy and finite prime energy have exact derivative-integral representations against the same source-atom derivative.

**PROVED:**

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy
```

replace the individually large pole and prime channels by one finite cumulative discrepancy before the remaining archimedean/scalar terms are subtracted.

No theorem proves a sign for that discrepancy pairing, the actual high-order endpoint jets, selected residual nonnegativity, negative-root exclusion or RH.

## Current frontier

```text
A4b1 absolute canonical source energy                             PROVED / #136
A4b2a one-step determinant/sufficiency reduction                  PROVED / #137
A4R regular first-bad selection                                  PROVED / #140-#150
A4b2r exact regular negative selected residual                    PROVED / #150
FB-01 retained whole-cell/Schur certificate                       PROVED / #153
FB-02 exact finite pole-prime discrepancy                         PROVED / #153
FB-03 actual source-energy endpoint jets                          OPEN / NOW
FB-03b generic repeated-IBP / iterated-primitive representation   OPEN
FB-04 transformed arithmetic falsification                        OPEN
A4b2r independent selected-residual nonnegative sign              OPEN
A4b2b universal one-step domination                               OPEN / BROAD FALLBACK
global negative-root exclusion                                    OPEN
outside-strip/trivial-zero + terminal Mathlib RH wrapper           OPEN
RH                                                                OPEN
```

## Current research reduction

The active finite state is the exact selected zero-shift residual `u0=c-x0`, with `A x0=b` uniquely at the regular predecessor and

```text
canonicalSourceChannelEnergy(u0) < 0.
```

PR #153 rewrites its pole-minus-prime component through the exact finite discrepancy

```text
D_L(t)=4*sinh(t/2)
  - sum_{2 <= q <= floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

The next job is **not** to assume the historical order-seven/order-nine Taylor calculation. It is to prove the actual endpoint jets of `sourceAtomRealEnergy` from the exact theorem-backed boundary-flat/parity hypotheses, then build a generic repeated-integration-by-parts interface and instantiate it only to the order Lean establishes.

The post-#150 sixth/eighth-order Riesz formulas remain valuable historical leads, but their derivative order is not yet theorem authority.

## Valuable state now retained

The information-loss issue identified after #150 is closed for the selected state. The certificate now retains:

```text
whole-cell K* minimality
selected-aperture smaller-size goodness
selected parity predecessor regularity
predecessor nonnegativity
negative explicit root + exact root equation
unique A x0=b
exact negative parity energy
exact negative production source-channel energy.
```

A separate simultaneous-both-parity / finite-tower regularity strengthening remains optional support work, not a prerequisite for the current endpoint-jet route.

## Current falsification firewalls

- raw aperture Loewner monotonicity is not supported by canonical experiments;
- scalar zero-shift Schur monotonicity is not supported globally;
- elementary atom energy is signed in tested states;
- independent loose channel bounds are conditioning-hostile;
- after #153, separately bounding pole and prime without spending the exact discrepancy identity explicitly discards theorem-backed cancellation;
- coth aperture singularities and log-cover deck translations live in different coordinates;
- finite Arb certification is scoped numerical falsification evidence, not Lean theorem authority.

## Documentation state

Current living synthesis:

`research/RHRC/RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md`

Older dated deltas and external reviews remain historical. The large accumulated `RESEARCH_LEADS.md` / `OBSTRUCTION_LEDGER.md` inventories are not current-anchor SSOTs; their reusable history is preserved and superseded where necessary by the living plan and newest dated delta.

## Firewalls

- RH remains OPEN.
- theorem authority is through #153 only.
- machine claim promotion remains separate.
- a retained negative source-channel energy is not a contradiction.
- exact discrepancy identity != discrepancy positivity.
- `C^∞` source-atom energy != high-order endpoint vanishing.
- boundary-flat moment bridges != order-seven/order-nine source-energy theorem.
- Riesz smoothing != arithmetic sign.
- no factorwise division by unproved transfer quantities.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib RH wrapper without explicit final bookkeeping.

**RH remains OPEN.**
