# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

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

Live GitHub head + exact Lean/compiler/CI remain authoritative. The #155 validated head and merged `main` share the theorem tree but not the commit SHA.

## One-screen frontier

```text
DONE THROUGH #153
  off-line zero -> retained regular cell-minimal first-bad certificate
  exact negative canonical source-channel energy on that retained state
  exact finite pole-prime discrepancy and full-channel normal form

DONE / #155 — ANALYTIC LEGALITY + EVEN-JET PACKAGE
  finite discrepancy interval integrability
  anchored iterated discrepancy primitives
  positive-order absolute continuity
  a.e. derivative = previous primitive
  smooth pulled-back source-energy jets
  legal generic repeated integration by parts
  arbitrary-order conditional Riesz energy identity
  source-coordinate oddness
  all even endpoint derivatives vanish
  even reversal parity -> M3 = 0

NOW — FB-03E COMPLEX D-TRANSPORT / PRODUCTION ODD JETS
  prove on genuine production sourceAtomRealEnergy:

    M0(u)=0 -> g_u''(omega)=-(2*pi)^2 g_(D u)(omega)

  then compose with M_k(Du)=M_(k+1)(u)
  derive the moment-prefix recursion
  close the odd endpoint jets actually needed by the #155 Riesz theorem
  instantiate exact production Riesz order 6
  instantiate exact even-parity production Riesz order 8

NEXT — FB-03F RETAINED TRANSFORMED-NEGATIVE WRAPPER
  compose Riesz 6/8 with the retained #153 first-bad certificate
  export the transformed negative residual through ExceptionalZero
  add no new analytic or arithmetic sign hypothesis

THEN — FB-04 ARITHMETIC-MECHANISM FALSIFICATION
  formulate a specific candidate inequality / transfer mechanism
  for the COMPLETE transformed discrepancy-archimedean-scalar residual
  use the #152 harness to try to falsify that mechanism
  do not merely rescan for negative total energy

DECISIVE OPEN ARITHMETIC TARGET
  prove on the exact forced retained state

    complete transformed residual >= 0

  equivalently, after legal composition, contradict the exact retained
  transformed negative residual.

TARGET
  same-state contradiction
  -> negative-root exclusion
  -> explicit outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact #155 theorem package consumed by the new frontier

### FB-03A — discrepancy integrability

**PROVED / #155**

```text
intervalIntegrable_canonicalPrimeCumulativeWeight
intervalIntegrable_canonicalPoleCumulativeWeight
intervalIntegrable_canonicalPolePrimeDiscrepancy
```

### FB-03B — anchored Riesz primitives

**PROVED / #155**

```text
canonicalPolePrimeRieszPrimitive
intervalIntegrable_canonicalPolePrimeRieszPrimitive
absolutelyContinuousOnInterval_canonicalPolePrimeRieszPrimitive_succ
ae_deriv_canonicalPolePrimeRieszPrimitive_succ
```

The prime staircase is integrated, not differentiated.

### FB-03C — generic legal repeated integration by parts

**PROVED / #155**

The source-energy composed jets are smooth, the affine-chain derivative is exact, and the generic Riesz energy equality is available under explicit endpoint-jet hypotheses

```text
forall j, 1 <= j -> j <= r ->
  iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0.
```

No production order is implied until those odd jets are discharged.

### FB-03D — source parity/even jets

**PROVED / #155**

```text
sourceAtomRealEnergy_neg_sourceCoordinate
iteratedDeriv_even_sourceAtomRealEnergy_zero
centeredMoment_three_eq_zero_of_even
```

Thus every even source-coordinate derivative at zero vanishes. Even reversal parity also forces `M3=0`.

## FB-03E — exact design

The new primary theorem is not the full arbitrary Taylor convolution. It is the smaller reusable production transport identity.

### E1 — entrywise matrix identity

Use the existing `sourceEntrySecondDerivative` machinery, including the diagonal case, to prove the source-entry second-derivative identity. Package the matrix defect as rank at most two.

Expected form:

```text
A''(omega) + (2*pi)^2 D A(omega) D
  = rank-two correction built from 1 and the sine profile.
```

### E2 — complex production quadratic-form cancellation

Lift the identity to the complex source matrix and sum against

```text
conj(u_i) * u_j.
```

Under `sum u_i = 0`, both rank-two correction terms vanish because each contains `sum u` or its conjugate.

Prove exactly:

```text
sourceAtomRealEnergy''(u,omega)
  = -(2*pi)^2 sourceAtomRealEnergy(Du,omega).
```

**Firewall:** the existing contraction-level derivative lemmas are real-vector results. They may help entrywise, but they do not by themselves prove this complex production theorem.

### E3 — moment-prefix recursion

Use the already theorem-backed shift

```text
M_k(Du)=M_(k+1)(u)
```

to iterate the transport under

```text
M0=...=M(r-1)=0.
```

Target general theorem:

```text
g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega).
```

Then combine with the existing rank-one first derivative at zero to derive

```text
g_u^(2r+1)(0)=2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

### E4 — production specializations

Boundary-flat production vectors satisfy `M0=M1=M2=0`, so derive jets 1..6 vanish and

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2.
```

For even reversal parity, #155 gives `M3=0`, so derive jets 1..8 vanish and

```text
g^(9)(0) = 2*(2*pi)^8*|M4|^2.
```

These formulas remain **DERIVED / OPEN IN LEAN** until FB-03E is green.

### E5 — exact Riesz 6/8 corollaries

Instantiate the already-proved generic #155 theorem:

```text
boundary-flat -> exact order-6 Riesz identity
even boundary-flat -> exact order-8 Riesz identity.
```

No sign theorem belongs in FB-03E.

## FB-03F — retained transformed-negative state

Compose the production Riesz identity with

```text
RegularCellMinimalNegativeEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
```

so a hypothetical off-line zero exports the same retained first-bad ancestry plus an exact transformed negative residual.

Acceptance rule: no new boundary-flat/parity/regularity hypothesis may be inserted if it is not already available on the retained state or proved from it.

## FB-04 — falsification before proof investment

The #152 harness should not be modified until FB-03E/F define the exact theorem-backed transformed observable.

Once they do:

1. implement the exact Lean residual, not a historical proxy;
2. test candidate **mechanisms**, not merely sign frequency;
3. preserve the full discrepancy/archimedean/scalar cancellation scale;
4. test both parity sectors and prime-power threshold behavior;
5. interval-certify finite failures before classifying a mechanism as falsified.

A finite failure can kill an overbroad candidate inequality. Finite success does not prove the sign.

## Dead route — pointwise smoothed-integrand positivity

Exact boundary-flat `K=2` fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show the relevant seventh/ninth derivatives change sign. Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is dead as a universal route.

The surviving target is the sign of the complete integrated residual or another genuinely arithmetic/global mechanism.

## Lead — combined parity

The first surviving local cutoff contribution has opposite signs in the two parity sectors. This motivates, but does not prove usefulness of,

```text
S_even + S_odd
S_even * S_odd
```

or another cross-parity invariant.

**Status: LEAD / HYPOTHESIS.** Cheapest next action is numerical falsification across prime-power thresholds and within fixed cells before Lean investment.

## Broad fallback

Universal `canonicalOneStepDomination` remains sufficient but is not a research reduction if its proof merely restates positivity of the successor block or absence of the negative root.

It should become primary only if a genuinely independent canonical arithmetic mechanism appears.

## Semantic work packages

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A finite discrepancy integrability                            PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic repeated IBP / conditional Riesz                    PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + odd jets + exact Riesz 6/8            OPEN / NEXT
FB-03F retained transformed-negative wrapper                        OPEN
FB-04  transformed arithmetic-mechanism falsification               OPEN
FB-05  scoped complete-residual nonnegative sign                     OPEN
FB-06  same-state contradiction / negative-root exclusion            OPEN
FB-07  terminal zeta/Mathlib seam                                    OPEN
```

PR numbers are execution history, not mathematical dependencies.

## Permanent firewalls

1. A retained negative certificate is not a contradiction.
2. Exact discrepancy identity is not discrepancy positivity.
3. Generic legal smoothing is not unconditional production order 6/8.
4. Real-contraction derivative transport is not the complex production theorem.
5. Riesz smoothing is not a sign theorem.
6. Pointwise fixed-sign smoothed integrand is falsified as a universal mechanism.
7. Interval-certified finite numerics are not Lean theorem authority.
8. Regular predecessor is not a positive successor.
9. Machine claim promotion remains separate from compiler theorem validity.
10. Negative-root exclusion is still not the terminal Mathlib RH statement without the final seam.

Newest research delta:

`RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md`

**RH remains OPEN.**
