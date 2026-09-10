# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## One-screen frontier

```text
DONE THROUGH #137
  finite legal off-line-zero reduction
  canonical finite negative obstruction
  centered N-flow / parity / first-bad / KKT / one-dimensional shell
  shifted and zero-shift Schur machinery
  cross-parity source transfer
  exact source-moment decomposition
  denominator-free zero-shift source transport
  scalar-sensitive absolute canonical source energy
  exact source pairing and one-step determinant
  conditional domination sufficiency
  off-line zero -> q_c<0 OR exists w, Delta(w)<0

DONE / #140 — A4R0
  off-line zero -> finite negative canonical witness at every sufficiently large aperture
  off-line zero -> AnyParityBad at every sufficiently large aperture
  off-line zero -> freshly selectable global-first-bad at every sufficiently large aperture
  IntrinsicPredecessorRegular <-> injective intrinsicPredecessorBlock
  regular predecessor -> unique zero-shift preimage
  frozen prime-cutoff equality on cells floor(exp L)=Q
  exact threshold source-atom vanishing at L=log q
  exact real-axis scalar extraction -2*wCorrection(L)=-log(L)+remainder(L)

DONE / #142 — A4R1a
  physical cutoff cell I_Q=(log Q,log(Q+1)) lies on L>0 for Q>=1
  floor(exp L)=Q throughout I_Q
  actual canonical source entries are continuous on I_Q
  fixed-vector canonical quadratic energy is continuous on I_Q
  a strict negative witness persists on an open J subset I_Q
  same finite size N and same vector u persist throughout J
  off-line zero -> such a locally persistent witness at every chosen sufficiently large cell-interior aperture

POST-#142 DERIVED COMPRESSION
  choose the least bad size K* over the entire cutoff cell before regularization;
  every K<K* is then good in both parities throughout the cell;
  predecessor size N*=K*-1 is PSD throughout the cell;
  use #142 to preserve a bad parity witness at K* on an open J;
  regularize only the relevant predecessor determinant(s) at N*;
  intersect dense regularity with J.

  Primary A4R no longer needs:
    countable all-size Baire regularity;
    finite-prefix simultaneous regularization through an arbitrary witness size;
    prime-threshold crossing;
    persistence of an old pointwise least-bad index.

NOW — A4R1b ANALYTIC FROZEN PREDECESSOR REGULARITY
  production cell-minimum wrapper;
  exact complex continuation of the frozen production channels;
  actual intrinsic predecessor operator on a fixed cell;
  exact scalar split A(L)=-Log(L) I+B(L);
  single-valued holomorphic B on a connected punctured domain;
  log-lift periodicity B(exp(z+2*pi*i))=B(exp z);
  determinant nonidentity by finite-spectrum/eigenvalue counting;
  dense real regularity on each physical cutoff cell.

THEN — A4R1c REGULAR CELL-MINIMAL FIRST-BAD CERTIFICATE
  choose cell-minimal K* and bad parity witness;
  #142 gives open persistent-negative J;
  dense regularity gives L2 in J;
  predecessor PSD from cell-minimality;
  injective from regularity;
  positive definite by finite Hermitian linear algebra;
  #140 gives unique x0 with A x0=b;
  package the existing Schur/energy machinery into

    Ecanonical(c-x0)=Re S0<0.

DECISIVE OPEN ARITHMETIC TARGET
  prove, from exact canonical pole/arch/scalar/prime interaction,

    Ecanonical(c-x0)>=0

  on the exact forced regular state.

  Equivalent inverse shorthand after regularity:

    <b,A^-1 b> <= q_c.

  Do not obtain this by defining an auxiliary positive form whose positivity is equivalent to successor PSD.

DISCOVERY GATE BEFORE THE SIGN THEOREM
  simplify the full minimizing-trial source expression using A x0=b before estimating;
  preserve exact pole / reduced-arch-diagonal / reduced-arch-off-diagonal /
  scalar / finite von-Mangoldt cancellation;
  exploit the stronger interval-wide predecessor PSD hypothesis if aperture derivatives reveal new arithmetic identities;
  interval-certify small high-sensitivity cases before trusting any proposed sign or monotonicity.

BROAD FALLBACK — UNIVERSAL A4b2b
  universal q_c>=0 and Delta(w)>=0 remains a valid closing theorem if a genuinely
  independent canonical arithmetic mechanism is discovered.
  It is deferred because under predecessor PSD and a one-dimensional shell it
  is DERIVED equivalent to successor positivity.

PARALLEL / LOWER PRIORITY
  E4-B shifted-nullity
  E3-C secular monotonicity/root-count control
  E3-B3 lower-floor deformation
  deformation-budget diagnostic
  pole-neutral finite-approximation refinement
  all-size/Baire regularity only if the cell-minimal route fails for a theoremized reason

TARGET
  analytic frozen predecessor regularity
  -> regular cell-minimal first-bad source countercertificate
  -> exact regular Schur-energy arithmetic sign
  -> contradiction with forced Re S0<0
  -> no off-line zero through existing reduction
  -> explicit terminal Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact theorem objects added by #142

### Fixed-cell production continuity

`Zeta23/CCM/CanonicalApertureContinuity.lean` exposes:

```text
archSinhSlope
regularizedArchScale
regularizedAlphaIntegrand
regularizedBetaIntegrand
regularizedSourceEq411LhsIntegrand
alphaL_eq_regularized_integral
betaL_eq_regularized_integral
regularizedSourceEq411LhsIntegrand_eq
continuousOn_canonicalSourceMatrix_apply_fixedCell
continuousOn_re_canonicalSourceQuadraticForm_fixedCell
exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
```

The regularized primitive identities are exact production equalities on the real axis and are used to prove continuity. They do **not** prove complex analyticity.

### Exceptional-zero persistence wrapper

`Zeta23/ExceptionalZero/FixedCellWitnessPersistence.lean` exposes:

```text
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_exists_offLine_zero
```

The same `N` and same boundary-flat vector `u` persist on the returned open neighborhood.

## Cell-minimal selection — next production packaging theorem

The strongest current derived composition is:

```text
bad somewhere in I_Q
-> define K* as least size bad somewhere in I_Q
-> for all K<K* and all L in I_Q: not AnyParityBad L K
-> choose L*, parity p and vector u bad at K*
-> #142 gives open J around L* preserving that exact negative witness
-> dense regularity of predecessor p at N*=K*-1 gives L2 in J regular
-> predecessor p is PSD at L2 by cell-minimality
-> predecessor p is PD at L2 by PSD + injective.
```

A standalone abstract conditional theorem implementing this selection logic has been locally compiled. It is not merged theorem authority and does not establish canonical determinant density.

Formal production packaging should reuse:

```text
AnyParityBad
two_le_of_anyParityBad
euclideanParity_nonnegative_of_lt_least_anyParityBad
exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
IntrinsicPredecessorRegular
intrinsicPredecessorRegular_iff_injective
```

Do not introduce a stronger hidden assumption that the pointwise least-bad size is locally constant.

## A4R1b analytic target

For fixed `Q,p,N`, build an exact frozen production predecessor family agreeing with `intrinsicPredecessorBlock p L N` on the physical cell.

The preferred theorem chain is:

```text
1. complexify the #142 regularized archimedean primitives on one explicit domain;
2. complexify the finite frozen prime atoms and pole channel;
3. build a single-valued holomorphic frozen remainder B(L);
4. prove actual predecessor equality A(L)=-Log(L) I+B(L) on L>0;
5. lift by L=exp z;
6. prove the finite-dimensional periodic-log nonidentity lemma;
7. conclude frozen predecessor determinant is not identically zero;
8. use isolated-zero/identity theory to obtain dense real regular apertures in I_Q.
```

The scalar extraction from #140 is theorem-backed only on the positive real axis. The complex logarithm branch and remainder continuation must be constructed explicitly.

### Direct archimedean route after #142

Before #142, the old digamma bridge looked like the safest route to aperture analyticity. #142 changes that assessment.

After the real substitution `x=L t`, the regularized production integrals become fixed-domain expressions. Schematically:

```text
alpha_n(L) = 2*n * integral_0^1 sinc(2*pi*n*t) * h(L*t) dt
beta_n(L)  =       integral_0^1 cos(2*pi*n*t)  * h(L*t) dt
```

with an analogous divided-slope formula for `sourceEq44GammaL-wCorrection`.

These rescaled identities are **DERIVED**, not current Lean declarations. High-precision checks are discovery evidence only.

The fixed interval and fixed oscillatory frequency make direct holomorphy a primary candidate. `DictionaryArchPhysical.lean`, `DictionaryArchBridge.lean` and `GammaFacts/Mu.lean` remain useful fallback/cross-check infrastructure rather than mandatory first dependencies.

## A4R1b first-break gates

Reject or narrow the analytic route if any of these fail:

1. the complex regularized hyperbolic scale has no common punctured domain supporting the needed parameter integral and a winding loop around zero;
2. one production remainder channel carries monodromy that cancels the scalar logarithmic shift;
3. the complex family fails exact agreement with the actual `intrinsicPredecessorBlock` on the physical real cell;
4. the scalar identity is represented incorrectly after compression or basis choice;
5. one fixed parity/size determinant is structurally identically zero;
6. real analyticity/nonidentity near one region cannot be propagated to the physical cell needed by #140/#142;
7. the zero-dimensional predecessor edge case breaks the characteristic-polynomial argument;
8. dense regularity cannot be intersected with the #142 persistent-negative open set while preserving the selected production state.

A failure here kills or narrows A4R1b, not RH.

## Stronger post-#142 falsification firewall

The generic analytic family documented in

`countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`

has:

```text
analytic aperture dependence;
explicit -log L scalar term;
positive predecessors throughout the positive axis;
persistent finite negative witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parities.
```

Therefore a proof using only generic geometry, persistence, regularity, parity or scalar logarithms is overstrong.

The decisive contradiction must spend actual canonical arithmetic.

## Schur-sign discovery firewalls

- the reported source-atom determinant leading coefficient is negative; atomwise positive determinant/SOS is not the default plan;
- sampled canonical Schur energies can be residues of extremely large channel cancellation;
- modified prime-weight experiments show that exact arithmetic coefficients matter sharply;
- the new regularization countermodel shows that even interval-wide predecessor positivity plus persistent badness is generically possible;
- simplify the full combined source expression using `A x0=b` before estimating channels independently;
- do not treat high precision as interval certification or theorem authority;
- a regular first-bad state with `S0<0` is still only the forced countercertificate, not a contradiction.

## Current records

Newest research delta:

`RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md`

Newest reusable regularization countermodel:

`countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`

Historical deltas remain evidence:

```text
RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md
RESEARCH_LEADS_POST_138_ASTRA_DELTA.md
external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md
countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md
```

Older post-green deltas remain historical evidence and must not be rewritten to look current.

## Permanent claim boundary

**PROVED:** theorem authority is through PR #142, including #140 aperture freedom/regularity scaffold and #142 fixed-cell actual-source continuity plus same-witness local persistence.

**DERIVED:** cell-minimal bad size gives smaller-size nonnegativity throughout the cell; only the predecessor determinant(s) at the cell-minimal bad size need regularizing in the preferred route; fixed-unit-interval rescaled archimedean identities; PSD + injective Hermitian predecessor gives positive definiteness.

**LOCAL LEAN CHECK:** abstract conditional cell-minimal regular selection; not merged and not canonical determinant density.

**LEAD / HYPOTHESIS:** full frozen-cell holomorphic remainder; punctured-domain logarithmic monodromy; determinant nonidentity; dense fixed-block regularity; derivative-weighted arithmetic constraints; regular canonical Schur-energy sign.

**EXPERIMENTAL SIGNAL:** high-precision rescaling checks, sharp cancellation and prime-weight sensitivity.

**OPEN:** production cell-minimal wrapper, A4R1b analytic frozen regularity, regular first-bad countercertificate wrapper, regular canonical Schur-energy nonnegativity, finite negative-root exclusion, terminal Mathlib RH bridge, RH.

**RH remains OPEN.**