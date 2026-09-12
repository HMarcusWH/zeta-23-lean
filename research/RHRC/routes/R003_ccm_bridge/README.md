# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #150. REGULAR-APERTURE SELECTION IS CLOSED; CURRENT FRONTIER = REGULAR SELECTED-RESIDUAL ARITHMETIC SIGN. RH OPEN.**

## Current authority split

```text
live main after merged PR #150 = fb92d5749d6f7a65cfc9129d49d8213219c059db
live main tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8

theorem-state anchor = PR #150 merge fb92d5749d6f7a65cfc9129d49d8213219c059db
validated theorem head = b1be9eca5f544d4356ea88089c0f7264f75d2220
validated theorem tree = 999ef44d44855cdffd5be5843e9f072867c0a7a8
RHRC #971 / run 34690959720 = SUCCESS
Permansson #744 / run 34690959699 = SUCCESS

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
off-line zero -> q_c<0 OR exists Delta<0                        PROVED / #137
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
off-line zero -> finite regular negative-energy certificate      PROVED / #150
```

## Exact #150 analytic and rigidity endpoint

### Full source / predecessor holomorphy

The exact common source domain is

```text
complexFrozenSourceDomain = complexArchSafeStrip \\ {0}.
```

Headline source/predecessor declarations include:

```text
analyticOnNhd_complexFrozenCanonicalSourceRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenCanonicalSourceRemainder_toEuclideanLin_apply_sourceDomain
analyticOnNhd_complexFrozenParityCompressedRemainder_apply_sourceDomain
analyticOnNhd_complexFrozenIntrinsicPredecessorRemainder_coord_sourceDomain
analyticOnNhd_liftedFrozenIntrinsicPredecessorBlock_coord
```

The route now uses genuine analyticity rather than deck identities as a proxy.

### Algebraic determinant nonidentity

PR #150 proves:

```text
exists_nat_det_sub_smul_id_ne_zero
liftedFrozenIntrinsicPredecessorBlock_add_nat_two_pi_I
exists_nat_deck_translate_liftedFrozenIntrinsicPredecessor_det_ne_zero
liftedFrozenIntrinsicPredecessor_det_not_identically_zero
```

The determinant seed is forced by finite characteristic-polynomial rigidity. Holomorphy is not used in this nonidentity step.

### Analytic regular selection

The lifted determinant is then proved analytic and the project theoremizes:

```text
exists_intrinsicPredecessorRegular_in_open_fixedCell
```

Every nonempty open real interval inside one physical cutoff cell contains an aperture where the **actual** intrinsic predecessor is regular.

**DERIVED vocabulary:** this means the regular set is dense in the cell, but the exact Lean API is the open-interval existential statement.

## Cell-minimal regular first bad

PR #150 theoremizes the correct whole-cell quantifier order:

```text
CellAnyParityBad
exists_least_cellAnyParityBad_two_le
not_anyParityBad_of_lt_cellMinimal
exists_regular_cellMinimal_firstBad.
```

At the selected aperture:

```text
K* is bad in parity p
N*=K*-1
all M<K* are not AnyParityBad
IntrinsicPredecessorRegular p L N*.
```

The construction itself obtains `K*` by minimizing over the whole cell before moving the aperture, so smaller-size goodness survives the move.

## Exact negative canonical energy endpoint

PR #150 proves

```text
exists_regular_cellMinimal_negativeCanonicalEnergy
```

and the ExceptionalZero wrappers

```text
exists_regularFirstBad_negativeCanonicalEnergy_of_offLine_zero
exists_regularFirstBad_negativeCanonicalEnergy_of_exists_offLine_zero.
```

Thus a hypothetical off-line zero forces one actual-production state carrying:

```text
regular predecessor
negative explicit root
unique zero-shift preimage A x0=b
parityCanonicalSourceEnergy(cubicZeroShiftTrialVector x0) < 0
canonicalSourceChannelEnergy(cubicZeroShiftTrialVector x0) < 0.
```

This is a finite negative countercertificate, not a contradiction.

## Current frontier — A4b2r regular selected-residual sign

The active target is now

```text
Ecanonical(c-x0) >= 0
```

on the exact forced regular #150 state.

Because the predecessor is nonnegative from first-bad ancestry and regular by #150, positive definiteness is a **DERIVED** finite Hermitian consequence. Mathematically one may write `x0=A^-1b`, but formal Lean should keep the unique-preimage equation primary unless an inverse API pays for itself.

Universal one-step domination remains sufficient but is deliberately a broad fallback. Under predecessor nonnegativity and a one-dimensional shell it is essentially successor positivity, so a proof that merely renames that positivity has no research gain.

## Full-certificate strengthening lead

The cell-minimal construction knows more than the outer energy endpoint exports:

```text
whole-cell K* minimality
all smaller sizes good throughout the cell
both parity sectors good at smaller sizes
open persistence of the selected bad witness
selected regular predecessor
negative root / A x0=b / exact negative energy.
```

**LEAD / OPEN FORMALIZATION:** retain this as a first-class certificate. A finite nested-open argument may also permit simultaneous regularity of all finitely many predecessor blocks below `K*` in both parities. If formalized, the whole finite predecessor tower becomes positive definite.

## Cancellation-preserving arithmetic route

The post-#150 Astra audit proposes the exact discrepancy form

```text
E_pole(u)-E_prime(u)
  = (1/L) * integral_0^L D(t) g_u'(1-t/L) dt,
```

with weighted von-Mangoldt discrepancy `D` and elementary atom energy `g_u`.

**Status: EXTERNAL DERIVED / theoremization pending.**

The project synthesis combines this with the exact boundary-flat moments `M0=M1=M2=0`.

Direct atom expansion gives, **DERIVED**,

```text
g_u(omega)=-(8*pi^6/315)|M3|^2 omega^7 + O(omega^9),
```

and in even parity the first possible term is order nine:

```text
(4*pi^8/2835)|M4|^2 omega^9 + O(omega^11).
```

Conditional on the discrepancy identity, repeated integration by parts gives candidate Riesz-smoothed forms

```text
E_pole-E_prime = L^-7 * integral D^[6](t) g^(7)(1-t/L) dt
```

and in even parity

```text
E_pole-E_prime = L^-9 * integral D^[8](t) g^(9)(1-t/L) dt.
```

These are identity/compression targets, not final sign theorems.

## Falsification constraints

The active arithmetic route must respect the following current evidence:

1. raw aperture Loewner monotonicity is not supported by canonical derivative probes;
2. the minimizing-trial Schur derivative changes sign in tested apertures;
3. elementary source-atom energy is signed in tested states;
4. the final Schur endpoint can be a tiny residue of much larger channel contributions;
5. exact arithmetic coefficients matter; generic positive-weight/source architecture is insufficient;
6. the `L*coth(L/2)` scalar variable and the log-cover deck variable are different coordinates, so no common-lattice resolvent identity is currently licensed.

Items 1-4 are EXPERIMENTAL SIGNAL / route quarantines, not theorem authority.

## Post-#150 FB-04 interval-certification harness

The route now contains a dedicated falsification harness for
`E4A4-SCHUR-FB-04`:

```text
canonical_source_numeric.py
canonical_source_arb.py
post150_selected_residual.py
probe_post150_selected_residual_scope.py
certify_post150_selected_residual_scope.py
check_post150_selected_residual_scope.py
fixtures/post150_selected_residual_v1.json
```

The finite carrier geometry is constructed exactly over rational/integer
coordinates before a source matrix is inserted. The fast backend uses the
formal normalization lock

```text
canonical = legacy + 2*cCorrection(L) I
```

without changing the historical R004 `build_ccm_matrix`. The independent
python-flint/Arb backend reconstructs the direct production equation-(4.4)
source with the same removable archimedean formulas theoremized in
`CanonicalApertureContinuity.lean`.

The scout distinguishes selected-aperture scopes H0-H3. H3 includes regular
positive predecessor, selected successor badness and both-parity goodness at
every smaller size at the same aperture. Finite sampling is explicitly **not**
allowed to certify the stronger whole-cell ancestry used internally by #150.

A negative floating candidate remains **EXPERIMENTAL SIGNAL**. It is promoted
only to a rigorous finite scoped falsification result if Arb enclosures certify
the physical cutoff cell, predecessor positive definiteness/regularity,
explicit successor badness, all advertised smaller-size hypotheses, and strict
negative direct/Schur selected-residual energy. Even such a certificate is not
Lean theorem authority and does not alter the terminal claim.

Detailed audit:
`../../countermodels/POST_150_SELECTED_RESIDUAL_SCOPE_AUDIT_2026_09_12.md`.

## Highest-leverage next theorem order

```text
1. export/retain the full #150 first-bad certificate
2. theoremize the exact pole/prime discrepancy identity
3. theoremize boundary-flat Taylor annihilation and Riesz smoothing
4. interval-certify/falsify candidate sign mechanisms
5. prove the scoped regular selected-residual nonnegativity theorem
6. compose with #150 to negative-root exclusion
7. close the outside-strip/trivial-zero seam and explicit Mathlib RH wrapper
```

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #150;
- compiler theorem authority beyond the machine-promoted claim IDs is not automatic claim promotion;
- regularity is not successor positivity;
- nonnegative + regular predecessor -> positive definite is DERIVED unless separately packaged;
- exact negative source-channel energy is not itself a contradiction;
- external discrepancy/Riesz calculations are not Lean theorem authority until formalized;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- D is algebraic, not unitary/isometric;
- generic/modified-source countermodels do not refute canonical CCM;
- numerical precision is not theorem authority;
- interval-certified finite numerics are scoped falsification evidence, not Lean theorem authority;
- terminal negative-root exclusion still needs the explicit outside-strip/trivial-zero bridge to Mathlib `RiemannHypothesis`;
- RH remains OPEN.

Detailed current implications: `../../RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
