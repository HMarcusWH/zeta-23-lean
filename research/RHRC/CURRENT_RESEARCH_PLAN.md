# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

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

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## One-screen frontier

```text
DONE THROUGH #150
  finite legal off-line-zero reduction
  canonical finite negative obstruction
  N-flow / parity / first-bad / KKT / one-dimensional shell
  shifted and zero-shift Schur machinery
  source-explicit transfer and exact source-moment decomposition
  denominator-free zero-shift source transport
  scalar-sensitive absolute canonical source energy
  exact source pairing and one-step determinant
  eventual aperture freedom
  fixed-cell negative persistence
  exact frozen/log-cover predecessor scaffold
  scalar removable layer + production bridge
  full source/predecessor holomorphy
  deck-forced determinant nonidentity
  actual regular predecessor in every nonempty open cell interval
  whole-cell least bad size + regular selected first bad
  unique A x0=b and exact canonical source-channel energy < 0

DONE / #152 — FALSIFICATION TOOLING
  exact rational finite geometry
  fast production-canonical discovery backend
  independent Arb reconstruction/replay
  H0-H3 selected-aperture scope classification
  deterministic CI plumbing
  no theorem or RH authority created

DONE / #153 — FB-01 + FB-02
  first-class RegularCellMinimalFirstBadCertificate
  first-class RegularCellMinimalNegativeEnergyCertificate
  whole-cell minimality retained through the negative-energy wrapper
  predecessor nonnegativity / root equation / preimage retained
  off-line zero -> retained certificate
  C-infinity sourceAtomRealEnergy
  exact pole derivative-integral form
  exact prime cumulative derivative-integral form
  exact finite pole-prime discrepancy identity
  full source-channel discrepancy normal form

NOW — FB-03 ENDPOINT-JET DISCOVERY
  determine the actual endpoint jets of sourceAtomRealEnergy at omega=0
  under exact boundary-flat constraints
  test whether parity yields additional vanishing
  do not assume order seven / order nine in advance
  build a generic iterated-primitive / repeated-integration-by-parts theorem
  instantiate only up to the Lean-proved jet order

THEN — FB-04
  use the exact FB-03 transformed representation in the #152 harness
  interval-certify/falsify candidate arithmetic sign mechanisms
  include both parity sectors where relevant
  keep the reduced archimedean/scalar budget coupled to the exact discrepancy scale

DECISIVE OPEN ARITHMETIC TARGET
  prove on the exact forced retained state

    Ecanonical(c-x0) >= 0

  equivalently, once regularity justifies inverse shorthand,

    <b,A^-1 b> <= q_c.

TARGET
  same-state contradiction with #153 exact negative energy
  -> negative-root exclusion
  -> explicit outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact #153 theorem package consumed by the new frontier

### Retained first-bad state

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalFirstBadCertificate.L_pos
exists_regular_cellMinimal_firstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
```

The certificate retains whole-cell bad-size minimality rather than only its selected-aperture projection.

### Smooth source-atom interface

```text
sourceAtomRealEnergy
sourceAtomRealEnergy_zero
contDiff_sourceEntry
contDiff_sourceAtomRealEnergy
```

`contDiff_sourceAtomRealEnergy` proves smoothness only. It does **not** prove the historical suggested high-order endpoint zero.

### Exact finite discrepancy interface

```text
canonicalPrimeCumulativeWeight
canonicalPoleCumulativeWeight
matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral
matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral
canonicalPolePrimeDiscrepancy
canonicalPolePrimeDiscrepancyEnergy
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy
```

For positive `L`:

```text
E_pole(x)-E_prime(x)
 = (1/L) * integral_0^L
     D_L(t) * deriv(sourceAtomRealEnergy K x)(1-t/L) dt,
```

where

```text
D_L(t)
 = 4*sinh(t/2)
   - sum_{q in Icc 2 floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

This is now PROVED and should be the default pole/prime arithmetic interface.

## FB-03 — exact design

The old roadmap said “prove order-seven/order-nine Taylor annihilation, then sixth/eighth-order Riesz smoothing.” That is now too assumption-heavy.

The corrected task is discovery-first.

### FB-03A — transfer exact boundary-flat information

Start from the existing finite-function / centered-moment bridge, including the already available zero/first/second endpoint information. Establish the exact hypotheses on the selected `cubicZeroShiftTrialVector` needed by the source-atom jet calculation.

Do not silently replace the selected vector by a generic coefficient vector with stronger constraints.

### FB-03B — determine actual source-energy jets

For

```text
g(omega) = sourceAtomRealEnergy K x omega
```

prove as many exact statements of the form

```text
deriv^[j] g 0 = 0
```

as follow from the theorem-backed boundary-flat/parity hypotheses.

The theorem should be stated at the strongest natural generality Lean supports cheaply, but the project must accept a lower order if that is what the exact production formula yields.

The historical calculations

```text
g(omega) ~ -(8*pi^6/315)|M3|^2 omega^7
```

and the proposed even-parity order-nine upgrade remain **DERIVED / LEAD** until this step is green.

### FB-03C — generic iterated primitives

Define an iterated primitive API such as

```text
D^[0] = D
D^[r+1](t) = integral_0^t D^[r](s) ds.
```

Prove left-endpoint vanishing structurally. Prove a generic repeated integration-by-parts theorem with every boundary term explicit.

The point is to integrate the finite staircase, not differentiate it.

### FB-03D — instantiate only to proved order

Use the exact endpoint-jet theorem to remove the right-endpoint terms that are actually licensed. The resulting transformed discrepancy identity — whatever its order — becomes the theorem-backed input to FB-04.

No sign theorem belongs in FB-03.

## FB-04 — falsification before proof investment

The #152 harness already distinguishes finite selected-aperture scopes H0-H3 and can rigorously replay checked-in candidates using Arb.

Once FB-03 supplies the exact transformed object:

1. extend the discovery observable to the theorem-backed transformed discrepancy;
2. retain the full arch/scalar budget rather than studying discrepancy sign in isolation unless a theorem justifies the separation;
3. test both parity sectors and cutoff-cell/prime-threshold sensitivity;
4. promote only interval-certified finite failures to rigorous finite falsification evidence;
5. remember that even H3 does not automatically certify the stronger whole-cell ancestry retained by #153.

A finite failure can kill an overbroad candidate inequality. A finite success does not prove the sign.

## Broad fallback

Universal `canonicalOneStepDomination` remains sufficient but is not a research reduction if its proof simply restates positivity of the successor block or absence of the negative root.

It should become primary only if a genuinely independent canonical arithmetic mechanism appears.

## Parallel/supportive work

These remain secondary to FB-03:

```text
simultaneous both-parity / finite-tower regularity
cross-parity source transfer at a fully regular state
low-rank displacement compression of <b,A^-1b>
Schur residual envelope derivative
positive-pivot / first-sign-flip recurrence search
prime-threshold and aperture sensitivity probes
```

The retained #153 certificate makes several of these easier to state without reconstructing lost ancestry, but none should displace the endpoint-jet discovery unless it yields higher mathematical information gain.

## Falsification gates

Current quarantines remain:

1. global aperture Loewner monotonicity;
2. global minimizing-trial Schur monotonicity;
3. universal positive elementary source-atom energy;
4. independent coarse pole/prime/arch/scalar majorants;
5. direct coth/deck common-lattice identification.

A sixth firewall is now explicit:

6. **Do not assume the order-seven/order-nine source-energy endpoint zero merely because coefficient-level boundary-flat moments suggest it.** The admissible repeated-IBP order is a theorem output.

## Semantic work packages

Use semantic IDs rather than predicted PR numbers:

```text
FB-01  retained full first-bad certificate                     PROVED
FB-02  exact finite pole-prime discrepancy                     PROVED
FB-03  endpoint jets + generic discrepancy smoothing           OPEN / NEXT
FB-04  interval-certified transformed arithmetic falsification OPEN
FB-05  scoped regular selected-residual nonnegativity          OPEN
FB-06  same-state contradiction / negative-root exclusion      OPEN
FB-07  terminal zeta/Mathlib seam                              OPEN
```

PR numbers are execution history, not mathematical dependencies.

## Permanent firewalls

1. A retained negative certificate is not a contradiction.
2. Exact discrepancy identity is not discrepancy positivity.
3. `C^∞` source-atom energy is not endpoint flatness.
4. Boundary-flat moments do not automatically license the historical 6/8-fold Riesz formulas.
5. Riesz smoothing is not a sign theorem.
6. Interval-certified finite numerics are not Lean theorem authority.
7. Regular predecessor is not a positive successor.
8. `A>=0` + regular gives `A>0` only as DERIVED unless separately packaged.
9. Machine claim promotion remains separate from compiler theorem validity.
10. Negative-root exclusion is still not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md`

**RH remains OPEN.**
