# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after merged PR #140 = fa96196b5bd6ed754853b0bdacee1dbd2356022f
live main tree = 2015404927540ae79a64469af82813463694b71d

theorem-state anchor = PR #140 merge fa96196b5bd6ed754853b0bdacee1dbd2356022f
validated theorem head = 77b52cfc73dfd83d2a0ed4373befba97d77e48e5
validated theorem tree = 2015404927540ae79a64469af82813463694b71d
RHRC #882 = SUCCESS
Permansson #655 = SUCCESS

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

POST-#140 RESEARCH CORRECTION
  choose a convenient frozen cutoff cell first;
  obtain a finite negative witness there using #140;
  only then regularize the finitely many predecessor sizes relevant to that witness.

  Primary A4R no longer needs a countable all-size Baire theorem.
  Primary A4R no longer needs to cross a prime threshold during the aperture move.

NOW — A4R1 FIXED-CELL FINITE REGULARIZATION
  choose Q with log Q above the #140 threshold;
  choose interior L1 in (log Q, log(Q+1));
  #140 gives finite N,u with strict negative canonical energy at L1;
  prove fixed-(N,u) energy continuity on that cell;
  prove dense regularity of each fixed intrinsic predecessor block;
  intersect only the finite family p in {even,odd}, 1<=k<=N;
  choose nearby L2 preserving negativity;
  reselect global first-bad at L2.

  Fixed-block analytic target:

    actual frozen projected predecessor
      -> genuine log-cover continuation
      -> Ahat(z) = -z I + Rhat(z)
      -> Rhat(z+2*pi*i)=Rhat(z)
      -> determinant nonidentity
      -> dense regular apertures.

  #140 proves the scalar -log(L) split on the real axis.
  The unresolved analytic work is the full production remainder, especially archimedean.
  Reuse DictionaryArchPhysical / DictionaryArchBridge / digamma machinery first.

AFTER A4R1 — REGULAR FIRST-BAD COUNTERCERTIFICATE
  predecessor minimality gives A>=0
  A4R1 gives A injective
  #140 gives unique x0 with A x0=b
  u0=c-x0
  package the exact existing Schur/energy machinery into

    Ecanonical(u0)=Re S0<0.

DECISIVE OPEN ARITHMETIC TARGET
  prove, from exact canonical prime/arch/scalar interaction,

    Ecanonical(c-x0)>=0

  on the exact forced regular first-bad trial A x0=b.

  Equivalent inverse shorthand after regularity:

    <b,A^-1 b> <= q_c.

  Do not obtain this by defining an auxiliary positive form whose positivity is equivalent to successor PSD.

DISCOVERY GATE BEFORE THE SIGN THEOREM
  analyze the full minimizing-trial source remainder after substituting A x0=b;
  preserve exact pole / reduced-arch-diagonal / reduced-arch-off-diagonal /
  scalar / prime cancellation;
  interval-certify small high-sensitivity cases before trusting any candidate inequality.

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
  all-size/Baire regularity only if the finite-cell route fails for a theoremized reason

TARGET
  fixed-cell finite regularization
  -> regular first-bad source countercertificate
  -> exact regular Schur-energy arithmetic sign
  -> contradiction with forced Re S0<0
  -> no off-line zero through existing reduction
  -> explicit terminal Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact theorem objects added by #140

### Aperture freedom

`Zeta23/ExceptionalZero/ApertureFreedom.lean` exposes:

```text
eventually_all_apertures_have_negativeCanonicalSourceWitness_of_offLine_zero
eventually_all_apertures_have_negativeCanonicalSourceWitness_of_exists_offLine_zero
eventually_all_apertures_have_anyParityBad_of_offLine_zero
eventually_all_apertures_have_globalFirstBad_of_offLine_zero
```

The key point is universal quantification over every sufficiently large aperture, with finite size/vector allowed to vary.

### Regularity and frozen-source scaffold

`Zeta23/CCM/CanonicalApertureRegularityScaffold.lean` exposes:

```text
intrinsicPredecessorDet
IntrinsicPredecessorRegular
intrinsicPredecessorRegular_iff_injective
existsUnique_intrinsicPredecessorBlock_preimage_of_regular
existsUnique_cubicZeroShiftPreimage_of_regular
frozenCanonicalPrimeMatrix
frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix
primeSourceCoordinate_log_self
sourceMatrix_primeSourceCoordinate_log_self
canonicalApertureScalarRemainder
neg_two_wCorrection_eq_neg_log_add_remainder
```

These are scaffold theorems. They do not prove dense regularity or a holomorphic aperture family.

## Why the fixed-cell route is stronger than the old A4R plan

The old plan tried to regularize while preserving a pre-existing finite witness before the final relevant finite horizon was known.

#140 lets us reverse the order:

```text
choose L first -> obtain finite N,u -> regularize only through N.
```

If `(N,u)` remains negative after the nearby move, any freshly reselected first-bad index satisfies `Nstar<=N`, so the finite regularity horizon covers the reselected state automatically.

This is the main reason all-size simultaneous regularity is unnecessary for the preferred composition.

## A4R1 first-break gates

Reject or narrow A4R1 if any of these fail:

1. fixed finite canonical energy is not continuous on one physical frozen cutoff cell;
2. the full frozen projected predecessor cannot be represented with a suitable analytic/log-cover remainder after the #140 scalar extraction;
3. hidden monodromy cancels the intended scalar shift;
4. a fixed parity/size predecessor determinant is structurally identically zero on the cell;
5. the determinant theorem controls a proxy rather than `intrinsicPredecessorBlock`;
6. fixed-block regular apertures are not dense;
7. finite simultaneous avoidance through an arbitrary finite `M` cannot be established;
8. the same strict negative witness cannot be preserved while moving inside the cell;
9. the reselected first-bad index can exceed the preserved negative witness size `N`;
10. the proposed proof silently crosses a threshold or invokes an all-size result that is not needed.

A failure here kills or narrows A4R1, not RH.

## Resurrected route

Before building new complex analysis around the raw production integrals, inspect and reuse:

```text
Zeta23/CCM/DictionaryArchPhysical.lean
Zeta23/CCM/DictionaryArchBridge.lean
Zeta23/GammaFacts/Mu.lean
```

They already theorem-lock physical archimedean normalization and a summable digamma-series representation. #140 makes this old infrastructure newly relevant to aperture analyticity.

## Schur-sign discovery firewalls

- the reported source-atom determinant leading coefficient is negative; atomwise positive determinant/SOS is not the default plan;
- sampled canonical Schur energies can be residues of extremely large channel cancellation;
- modified prime-weight experiments show that exact arithmetic coefficients matter sharply;
- therefore simplify the full combined source expression using `A x0=b` before estimating channels independently;
- do not treat high precision as interval certification or theorem authority;
- a regular first-bad state with `S0<0` is still only the forced countercertificate, not a contradiction.

## Current records

Newest research delta:

`RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md`

Historical post-#138 reroute and external-review provenance:

```text
RESEARCH_LEADS_POST_138_ASTRA_DELTA.md
external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md
countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md
```

Older post-green deltas remain historical evidence and must not be rewritten to look current.

## Permanent claim boundary

**PROVED:** theorem authority is through PR #140, including aperture freedom and the exact regularity/frozen-source scaffold.

**DERIVED:** first-bad PSD + injective Hermitian predecessor gives positive definiteness; finite-cell regularization only needs a finite horizon after a witness is obtained; all-size Baire is unnecessary for the preferred composition.

**LEAD / HYPOTHESIS:** full frozen-cell analytic/log-cover predecessor representation; determinant nonidentity; dense fixed-block regularity; finite simultaneous regularization; regular canonical Schur-energy sign.

**EXPERIMENTAL SIGNAL:** sharp cancellation and prime-weight sensitivity reported by the Astra audit.

**OPEN:** A4R1 fixed-cell regularization, regular first-bad countercertificate wrapper, regular canonical Schur-energy nonnegativity, finite negative-root exclusion, terminal Mathlib RH bridge, RH.

**RH remains OPEN.**