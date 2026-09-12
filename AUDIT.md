# RHRC formal audit — theorem authority through PR #155; production D-transport frontier

> **RH remains OPEN.**

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

Live GitHub head + exact compiler/CI evidence outrank this prose. The validated #155 head and merged main are distinct commits that share the same theorem tree.

## Exact validation evidence for #155

At validated theorem head

```text
ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
```

RHRC run #1005 (`34720946254`) completed successfully. Permansson run #778 (`34720946242`) also completed successfully.

The successful theorem-bearing closure includes the aggregate CCM build, ExceptionalZero build, R003 normalization/source firewalls, no-sorry/no-project-axiom checks, and the independent Permansson verification lane.

## Exact theorem-state progression relevant to #155

### PR #150 — regular negative endpoint

**PROVED:** actual regular cell-minimal first-bad selection and strict negative exact canonical source-channel energy under a hypothetical off-line zero.

### PR #152 — falsification/certification harness

**TOOLING / NOT THEOREM AUTHORITY:** exact finite geometry, production scout, independent Arb replay, H0-H3 scope classification, deterministic CI plumbing.

### PR #153 — retained certificate + exact finite discrepancy

**PROVED:**

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
canonicalPolePrimeDiscrepancy
canonicalPolePrimeDiscrepancyEnergy
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy
```

The whole-cell ancestry and full regular negative-energy state are retained and the pole-minus-prime channel is rewritten through one exact finite discrepancy before the remaining archimedean/scalar terms are subtracted.

### PR #155 — discrepancy integrability seam

**PROVED:**

```text
intervalIntegrable_canonicalPrimeCumulativeWeight
intervalIntegrable_canonicalPoleCumulativeWeight
intervalIntegrable_canonicalPolePrimeDiscrepancy
```

The finite prime staircase is integrated, not differentiated.

### PR #155 — anchored Riesz primitives and legal smoothing

**PROVED:**

```text
canonicalPolePrimeRieszPrimitive
intervalIntegrable_canonicalPolePrimeRieszPrimitive
absolutelyContinuousOnInterval_canonicalPolePrimeRieszPrimitive_succ
ae_deriv_canonicalPolePrimeRieszPrimitive_succ
sourceAtomComposedJet
contDiff_one_sourceAtomComposedJet
deriv_sourceAtomComposedJet
canonicalPolePrimeDiscrepancyEnergy_eq_rieszEnergy
```

The generic arbitrary-order Riesz identity is legal under explicit endpoint-jet hypotheses. It does not differentiate the discontinuous prime staircase.

### PR #155 — production source-energy parity/even jets

**PROVED:**

```text
sourceAtomRealEnergy_neg_sourceCoordinate
iteratedDeriv_even_sourceAtomRealEnergy_zero
centeredMoment_three_eq_zero_of_even
```

Hence production source energy is odd in the source coordinate, every even endpoint derivative at zero vanishes, and even reversal parity kills centered moment `M3`.

## What #155 did not prove

No current Lean theorem establishes:

```text
the complex production identity g_u'' = -(2*pi)^2 g_(D u)
the moment-prefix D-transport recursion
the required odd endpoint cancellations
unconditional production Riesz order 6
unconditional even-parity production Riesz order 8
a retained transformed-negative first-bad wrapper
a sign for the complete transformed discrepancy/archimedean/scalar residual
regular selected-residual nonnegativity
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

## Current derived bridge

The audited post-green calculation gives

```text
M0(u)=0
  -> g_u''(omega)=-(2*pi)^2 g_(D u)(omega)
```

for the genuine complex production energy, with an entrywise rank-two correction whose Hermitian quadratic form vanishes under the zero-sum condition.

Combining this with the already proved moment shift `M_k(Du)=M_(k+1)(u)` yields the intended recursion

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega)
  -> g_u^(2r+1)(0)=2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

**Formal status: DERIVED / OPEN IN LEAN.**

The next implementation must prove the complex sesquilinear transport directly; existing real-contraction derivative lemmas do not authorize silent promotion to `sourceAtomRealEnergy`.

## Exact route falsification after #155

The boundary-flat `K=2` fixtures

```text
even = (1,-4,6,-4,1)
odd  = (1,-2,0,2,-1)
```

satisfy the three moment constraints and the indicated reversal parity, yet the relevant seventh/ninth source derivatives change sign.

Therefore the universal implication

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is **DEAD**.

This does not refute the Riesz identity. It refutes a proposed pointwise sign mechanism. The complete integrated residual may still admit a sign through actual arithmetic cancellation, stationarity, whole-cell ancestry, or a different invariant.

## Current formal endpoint

From a hypothetical off-line zero, #153 supplies one retained regular first-bad certificate with strict negative exact canonical source-channel energy. #155 supplies a legal arbitrary-order conditional Riesz representation and the production even-jet/parity facts.

The missing theorem bridge is now sharply isolated:

```text
complex D-transport
  -> production odd endpoint jets
  -> exact Riesz order 6 / even order 8
  -> retained transformed-negative wrapper.
```

After that, the only missing contradiction-producing implication is genuinely arithmetic.

## Current execution order

```text
FB-01  retained first-bad certificate                              PROVED / #153
FB-02  exact pole-prime discrepancy                                PROVED / #153
FB-03A discrepancy integrability                                   PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic repeated IBP / conditional Riesz                    PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + production odd jets + Riesz 6/8       OPEN / NEXT
FB-03F retained transformed-negative wrapper                        OPEN
FB-04  complete transformed-residual arithmetic mechanism           OPEN
FB-05  scoped regular selected-residual nonnegative sign             OPEN
FB-06  same-state contradiction / negative-root exclusion            OPEN
FB-07  terminal outside-strip/trivial-zero seam                       OPEN
```

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority through #155 and machine claim promotion are separate;
- generic legal smoothing is not unconditional production order 6/8;
- a real contraction identity is not automatically the complex production identity;
- Riesz smoothing is not an arithmetic sign theorem;
- pointwise smoothed-integrand positivity is falsified as a universal route;
- interval-certified finite numerics are scoped falsification evidence, not Lean theorem authority;
- regularity is not successor positivity;
- `D` algebraic != `D` unitary/isometric;
- negative-root exclusion != terminal Mathlib RH without the final seam;
- RH remains OPEN.

Newest research implications:
`research/RHRC/RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md`.

**RH remains OPEN.**
