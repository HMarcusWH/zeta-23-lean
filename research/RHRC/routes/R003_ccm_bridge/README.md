# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #155. GENERIC RIESZ SMOOTHING + ALL EVEN SOURCE-ENERGY JETS ARE CLOSED; CURRENT FRONTIER = COMPLEX D-TRANSPORT / PRODUCTION ODD JETS / COMPLETE TRANSFORMED-RESIDUAL ARITHMETIC. RH OPEN.**

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

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW + parity + first-bad geometry                             PROVED / #100-#112
shifted/zero-shift Schur/secular package                        PROVED / #113-#128
source-explicit parity transfer                                  PROVED / #129
exact source-moment decomposition                                PROVED / #131
whole-kernel zero-shift source transport                         PROVED / #134
absolute canonical source energy                                 PROVED / #136
exact canonical source pairing + one-step determinant            PROVED / #137
regular selected first-bad endpoint                              PROVED / #140-#150
retained full first-bad / negative-energy certificates           PROVED / #153
exact finite pole-prime discrepancy / full-channel normal form   PROVED / #153
finite discrepancy interval integrability                       PROVED / #155
anchored Riesz primitives + AC / a.e. derivative                PROVED / #155
generic legal repeated IBP / conditional Riesz                   PROVED / #155
source oddness + all even endpoint jets                          PROVED / #155
even reversal parity -> M3=0                                    PROVED / #155
```

## Retained first-bad certificate surface

PR #153 exports

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
```

with theorem constructors

```text
exists_regular_cellMinimal_firstBadCertificate
exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero.
```

The current forced state therefore retains whole-cell minimality, selected-aperture smaller-size goodness, regularity, predecessor nonnegativity, the negative explicit Schur root, exact `A x0=b`, and strict negative production source-channel energy.

## Exact discrepancy + #155 Riesz surface

The exact finite discrepancy is

```text
D_L(t)
 = canonicalPolePrimeDiscrepancy L t
 = 4*sinh(t/2)
   - sum_{q in Icc 2 floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

PR #153 proves

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy.
```

PR #155 adds the public interval-integrability seam and the left-anchored iterated primitive API

```text
canonicalPolePrimeRieszPrimitive.
```

Positive-order primitives are absolutely continuous and recover the previous primitive as derivative almost everywhere. The generic Riesz energy theorem is legal and never differentiates the prime staircase.

The generic theorem still requires the relevant source-energy endpoint jets to vanish explicitly.

## Exact #155 source-energy jet surface

PR #155 proves

```text
sourceAtomRealEnergy_neg_sourceCoordinate
iteratedDeriv_even_sourceAtomRealEnergy_zero
centeredMoment_three_eq_zero_of_even.
```

Consequences:

```text
all even endpoint derivatives vanish;
even reversal parity gives M3=0.
```

This does **not** yet close the odd endpoint derivatives required for production Riesz order 6/8.

## Current frontier — FB-03E complex D transport

The post-green audited identity is

```text
M0(u)=0
  -> g_u''(omega)=-(2*pi)^2 g_(D u)(omega),
```

where `g_u=sourceAtomRealEnergy K u` and `D` is the centered index multiplier.

**Status: DERIVED / OPEN IN LEAN.**

The intended theorem composition uses the already-proved moment shift

```text
M_k(Du)=M_(k+1)(u)
```

to derive

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega)
  -> g_u^(2r+1)(0)=2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

Expected production specializations, still OPEN:

```text
boundary-flat -> jets 1..6 vanish -> exact Riesz order 6
even boundary-flat -> jets 1..8 vanish -> exact Riesz order 8.
```

### Required implementation pattern

1. use `sourceEntrySecondDerivative`, including the diagonal case;
2. prove the entrywise rank-at-most-two source-matrix defect identity;
3. coerce to the complex production matrix;
4. sum against `conj(u_i)*u_j`;
5. kill the rank-two correction with `sum u=0`;
6. identify `D A D` with the production source energy of `indexMatrix *ᵥ u`;
7. iterate through the moment-prefix flag.

**Firewall:** a theorem for the real contraction API does not establish the complex production source-energy identity.

## FB-03F — transformed retained negative certificate

After exact production Riesz 6/8 is theorem-backed, compose it with the retained #153 certificate and ExceptionalZero wrapper so a hypothetical off-line zero yields the same retained whole-cell first-bad ancestry plus an exact transformed negative residual.

No new boundary-flat/parity/regularity hypotheses may be inserted unless proved from the retained state.

## Post-#155 exact falsification

The exact `K=2` boundary-flat vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show that the relevant ninth/seventh source derivatives change sign on the physical source-coordinate interval.

Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is a dead universal route.

This does not refute the #155 Riesz identity. The surviving sign target is the **complete integrated discrepancy minus archimedean/scalar residual** or another global arithmetic invariant.

## #152 interval-certification harness

The historical `post150_*` tooling names remain unchanged. The harness is still scoped falsification/certification infrastructure, not theorem authority.

Do **not** retarget it to a guessed sixth/eighth-order observable. Wait until FB-03E/F define the exact Lean transformed residual, then use the harness to falsify specific candidate mechanisms.

Repeated numerical positivity or negativity by itself is not a proof mechanism.

## Current arithmetic target

The current theorem-backed forced state has

```text
canonicalSourceChannelEnergy(u0) < 0.
```

After FB-03E/F this should become an exact transformed negative residual. The decisive missing theorem is an independently justified nonnegative sign for that **same complete transformed residual** under the exact retained first-bad hypotheses.

Candidate mechanism families worth testing include:

```text
stationarity A x0=b
whole-cell smaller-size goodness
transfer to predecessor energies
exact transformed discrepancy/archimedean cancellation
combined-parity invariant.
```

The combined-parity idea is **LEAD / HYPOTHESIS** only and should be numerically falsified first.

## Highest-leverage next theorem order

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A finite discrepancy integrability                            PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic repeated IBP / conditional Riesz                    PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D-transport + production odd jets + Riesz 6/8       OPEN / NEXT
FB-03F retained transformed-negative wrapper                        OPEN
FB-04  transformed arithmetic-mechanism falsification               OPEN
FB-05  scoped complete-residual nonnegative sign                     OPEN
FB-06  same-state contradiction / negative-root exclusion            OPEN
FB-07  outside-strip/trivial-zero seam + Mathlib RH wrapper           OPEN
```

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #155;
- compiler theorem authority beyond machine-promoted claim IDs is not automatic claim promotion;
- retained negative energy is not itself a contradiction;
- exact discrepancy identity / generic Riesz smoothing is not an arithmetic sign theorem;
- real D-transport helper theorems are not automatically the complex production theorem;
- pointwise smoothed-integrand positivity is falsified as a universal mechanism;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- `D` is algebraic, not unitary/isometric;
- interval-certified finite numerics are scoped falsification evidence, not Lean theorem authority;
- terminal negative-root exclusion still needs the explicit outside-strip/trivial-zero bridge to Mathlib `RiemannHypothesis`;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md`.

**RH remains OPEN.**
