# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #153. RETAINED CERTIFICATE + EXACT POLE-PRIME DISCREPANCY ARE CLOSED; CURRENT FRONTIER = SOURCE-ENERGY ENDPOINT JETS / TRANSFORMED SELECTED-RESIDUAL ARITHMETIC. RH OPEN.**

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
eventual finite badness at every sufficiently large aperture     PROVED / #140
actual predecessor det!=0 <-> injective + unique preimage        PROVED / #140
fixed-cell actual-source continuity / witness persistence        PROVED / #142
exact frozen source/predecessor + log-cover scaffold             PROVED / #144
scalar removable analytic/production bridge                     PROVED / #145-#146
fixed-unit alpha/beta/gamma parameter holomorphy                 PROVED / #148
assembled frozen source/predecessor holomorphy                   PROVED / #150
deck-forced determinant nonidentity                              PROVED / #150
actual regular predecessor in every nonempty open cell interval  PROVED / #150
cell-minimal regular first-bad selection                         PROVED / #150
exact negative canonical source-channel energy at that state     PROVED / #150
retained full first-bad certificate                              PROVED / #153
retained full negative-energy Schur certificate                  PROVED / #153
off-line zero -> retained certificate                            PROVED / #153
exact finite pole-prime discrepancy identity                     PROVED / #153
full source-channel discrepancy normal form                      PROVED / #153
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

The current forced state therefore retains, in one theorem-backed object:

```text
whole-cell K* minimality
selected-aperture smaller-size goodness
selected parity badness at K*
selected predecessor regularity
predecessor nonnegativity
negative explicit Schur root + exact root equation
unique zero-shift preimage A x0=b
exact negative parity energy
exact negative production source-channel energy.
```

The pre-#153 tuple theorems remain compatibility projections.

## Exact #153 pole-prime discrepancy surface

The elementary source atom is

```text
sourceAtomRealEnergy K x omega
  = matrixRealEnergy (sourceMatrix omega K) x.
```

PR #153 proves it is smooth:

```text
contDiff_sourceAtomRealEnergy.
```

The pole primitive is

```text
canonicalPoleCumulativeWeight t = 4*sinh(t/2),
```

and the finite prime staircase is

```text
canonicalPrimeCumulativeWeight L t
  = sum_{q in Icc 2 floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

The exact production channel theorems are

```text
matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral
matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy.
```

Define

```text
D_L(t)
 = canonicalPolePrimeDiscrepancy L t
 = 4*sinh(t/2)
   - sum_{q in Icc 2 floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

Then, for `L>0`,

```text
E_pole(x)-E_prime(x)
  = (1/L) * integral_0^L D_L(t)
      * deriv(sourceAtomRealEnergy K x)(1-t/L) dt.
```

The full source channel is this discrepancy energy minus the reduced archimedean diagonal, reduced archimedean off-diagonal and scalar-correction terms.

This is theorem authority. The post-#150 Astra discrepancy derivation is now historical provenance rather than the current evidence class.

## Current frontier — FB-03 source-energy endpoint jets

The next theorem target is not “prove sixth/eighth-order Riesz smoothing” as a precommitted fact.

The exact question is:

```text
for legal boundary-flat/parity x,
what derivatives of sourceAtomRealEnergy K x vanish at omega=0?
```

Existing bridge theorems already encode low-order boundary-flat function/moment information, but they do not automatically establish the same derivative order for the quadratic source-atom energy.

The historical symbolic calculation suggested:

```text
g(omega) = -(8*pi^6/315)|M3|^2 omega^7 + O(omega^9)
```

and an even-parity first possible term at order nine.

**Status:** DERIVED / LEAD until Lean locks the exact source-energy jets.

### Required implementation pattern

1. identify the exact boundary-flat/parity hypotheses carried by the selected `cubicZeroShiftTrialVector`;
2. prove the source-energy derivative values at zero in increasing order;
3. accept the actual maximal order Lean/the exact formula gives;
4. define a generic iterated-primitive API for a discrepancy function;
5. prove repeated integration by parts with all endpoint terms explicit;
6. instantiate only to the formally established jet order.

The prime staircase must be integrated, not differentiated.

## Post-#150 / #152 interval-certification harness

The route contains the falsification harness:

```text
canonical_source_numeric.py
canonical_source_arb.py
post150_selected_residual.py
probe_post150_selected_residual_scope.py
certify_post150_selected_residual_scope.py
check_post150_selected_residual_scope.py
fixtures/post150_selected_residual_v1.json
```

The names remain `post150` because they are historical tooling names introduced by #152. They are not stale theorem-anchor claims.

The harness reconstructs exact rational carrier geometry, scouts production-canonical states, and replays checked-in candidates with Arb enclosures. H3 includes selected-aperture predecessor positivity/regularity, selected successor badness and both-parity goodness at every smaller size.

H3 is still not automatic proof of the stronger whole-cell quantifier retained in the #153 certificate.

A negative floating candidate is only **EXPERIMENTAL SIGNAL**. A rigorous Arb failure can falsify the finite scoped mechanism it certifies; it is not Lean theorem authority and not a zeta counterexample.

After FB-03, this harness should consume the exact theorem-backed transformed discrepancy observable rather than a hard-coded assumed sixth/eighth-order formula.

## Falsification constraints

The active arithmetic route must respect:

1. raw aperture Loewner monotonicity is not supported by canonical derivative probes;
2. the minimizing-trial Schur derivative changes sign in tested apertures;
3. elementary source-atom energy is signed in tested states;
4. the final Schur endpoint can be a tiny residue of much larger channel contributions;
5. exact arithmetic coefficients matter;
6. `L*coth(L/2)` and log-cover deck translation use different coordinates;
7. the historical order-seven/order-nine endpoint claim is not theorem authority;
8. after #153, separately bounding pole and prime discards an exact cancellation-preserving theorem and must be justified quantitatively.

## Current arithmetic target

On the exact retained forced state:

```text
canonicalSourceChannelEnergy(u0) < 0        PROVED
```

The decisive missing theorem is

```text
canonicalSourceChannelEnergy(u0) >= 0       OPEN
```

or an equivalent scoped arithmetic inequality under the exact certificate hypotheses.

Because the predecessor is nonnegative and regular, positive definiteness is a DERIVED finite Hermitian consequence. Formal Lean should keep the exact unique-preimage equation primary unless an inverse abstraction materially helps.

## Highest-leverage next theorem order

```text
FB-01  retained full first-bad certificate                     PROVED / #153
FB-02  exact finite pole-prime discrepancy                     PROVED / #153
FB-03  actual source-energy endpoint jets + generic smoothing  OPEN / NEXT
FB-04  interval-certified transformed arithmetic falsification OPEN
FB-05  scoped selected-residual nonnegativity                  OPEN
FB-06  same-state contradiction / negative-root exclusion      OPEN
FB-07  outside-strip/trivial-zero seam + Mathlib RH wrapper     OPEN
```

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #153;
- compiler theorem authority beyond machine-promoted claim IDs is not automatic claim promotion;
- retained negative energy is not itself a contradiction;
- exact discrepancy identity is not discrepancy positivity;
- smoothness is not high-order endpoint flatness;
- boundary-flat moment constraints do not automatically imply the historical order-seven/order-nine energy zero;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- `D` is algebraic, not unitary/isometric;
- generic/modified-source countermodels do not refute canonical CCM;
- numerical precision is not theorem authority;
- interval-certified finite numerics are scoped falsification evidence, not Lean theorem authority;
- terminal negative-root exclusion still needs the explicit outside-strip/trivial-zero bridge to Mathlib `RiemannHypothesis`;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md`.

**RH remains OPEN.**
