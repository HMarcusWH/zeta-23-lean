# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after merged PR #138 = ebf289bdfdde69020bee0d1571047f155e5de4db
live main tree = d26cd83709437260d0a16630d90c73a93f64c975

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. PR #138 and this synchronization layer do not advance theorem authority beyond #137.

## One-screen frontier

```text
DONE
  finite legal off-line-zero reduction
  canonical finite negative obstruction
  exact centered N-flow / parity / first-bad / KKT / one-dimensional shell
  exact shifted and zero-shift Schur machinery
  exact cross-parity source transfer
  exact pole/arch/prime source-moment decomposition / #131
  exact denominator-free zero-shift kernel/source transport / #134
  scalar-sensitive absolute canonical source energy / #136
  exact production source pairing / #137
  exact one-step determinant Delta(w) / #137
  domination -> kernel annihilation -> zero-shift preimage / #137
  domination + predecessor nonnegativity -> Re S0>=0 / #137
  domination -> no safe negative explicit Schur root / #137
  off-line zero -> global-first-bad domination failure / #137
  off-line zero -> q_c<0 OR exists w, Delta(w)<0 / #137

POST-#138 RESEARCH CORRECTION
  under A>=0 and a one-dimensional shell,

    q_c>=0 AND forall w, Delta(w)>=0

  is DERIVED to be equivalent to positivity of the one-step successor form.
  Universal A4b2b remains sufficient, but it is not currently a smaller RH subproblem.

NOW — A4R REGULAR-APERTURE SELECTION
  prove that every strict finite canonical negative witness can be moved to an
  arbitrarily nearby positive aperture, preserving negativity, so that all
  finitely relevant predecessor blocks in both parities are injective/positive
  definite; then reselect global first-bad at the new aperture.

  Candidate mechanism:

    frozen cutoff Q
    M_Q(L) = -log(L) I + B_Q(L)
    L = exp(z)
    Bhat_Q(z) periodic under z -> z + 2*pi*i
    characteristic-polynomial root count -> determinant nonidentity
    -> dense regular apertures

  This route earns information because it removes resonance by witness selection,
  not by assuming successor positivity.

AFTER A4R — REGULAR FIRST-BAD COUNTERCERTIFICATE
  both predecessor parity blocks positive definite
  unique x0 = A^-1 b
  u0 = c - A^-1 b
  canonicalSourceEnergy(u0) = Re S0 < 0 at the forced bad state

DECISIVE OPEN ARITHMETIC TARGET
  prove, from exact canonical prime/arch/scalar interaction,

    canonicalSourceEnergy(c - A^-1 b) >= 0

  on the exact forced regular first-bad trial.

  Equivalent regular scalar form:

    <b, A^-1 b> <= q_c.

  Do not obtain this by defining an auxiliary positive form whose positivity is
  equivalent to the desired successor positivity.

DISCOVERY GATE BEFORE THE SIGN THEOREM
  analyze the full minimizing-trial Schur remainder, not generic eigenvalue scans:

    u0 = c - A^-1 b
    S0 = Ecanonical(u0)

  record pole / reduced-arch-diagonal / reduced-arch-off-diagonal / scalar /
  finite-prime contributions and prime-weight sensitivities.

  interval-certify the smallest high-sensitivity examples before trusting a
  candidate inequality.

BROAD FALLBACK — UNIVERSAL A4b2b
  universal q_c>=0 and Delta(w)>=0 remains a valid closing theorem if a genuinely
  independent canonical arithmetic mechanism is discovered.
  It is deferred because the universal certificate is the full successor positivity
  problem under the present block hypotheses.

PARALLEL / LOWER PRIORITY
  E4-B shifted-nullity
  E3-C secular monotonicity/root-count control
  E3-B3 lower-floor deformation
  deformation-budget diagnostic
  pole-neutral finite-approximation refinement

TARGET
  regular-aperture selection
  -> regular first-bad source countercertificate
  -> exact regular Schur-energy arithmetic sign
  -> contradiction with forced Re S0<0
  -> no off-line zero through existing reduction
  -> explicit terminal Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact theorem objects available through #137

### Absolute scalar-sensitive energy

`CanonicalSourceEnergy.lean` exposes:

```text
matrixRealEnergy
parityCanonicalSourceEnergy
canonicalSourceChannelEnergy
cubicShellRealEnergy
```

with exact pole/arch/scalar/prime decomposition and exact zero-shift trial-energy bridge.

### Exact complex pairing

`CanonicalSourcePairing.lean` exposes the pairing needed to compute predecessor energy, shell coupling and determinant from the same production source.

### One-step determinant

`CanonicalOneStepDomination.lean` exposes:

```text
intrinsicPredecessorRealEnergy
cubicShellCoupling
cubicOneStepDeterminant
canonicalOneStepDomination
```

and proves the conditional kernel/range/endpoint/negative-root chain.

### Global countercertificate

`GlobalFirstBadOneStepDomination.lean` proves that a hypothetical off-line zero forces

```text
q_c < 0 OR exists w, Delta(w) < 0
```

at one global-first-bad predecessor-nonnegative state.

## Post-#138 derived geometry to preserve

These are not newly Lean-locked.

```text
k = P_(ker A)b
Delta(k) = -||k||^4
```

so resonance has an explicit determinant witness.

At a safe negative explicit root `lambda`, the root-selected predecessor vector

```text
w_lambda = (A-lambda I)^-1 b
```

has a derived closed determinant formula and is a preferred discovery direction.

The external audit also reports the exact correction-vector proportionality

```text
d = -(6/(2*N-1)) a
```

with exact rational finite checks; formalization remains optional cleanup rather than the immediate RH bottleneck.

## Why A4R moved ahead of A4b2b

The old post-#137 plan treated A4R as fallback because a successful domination theorem would itself remove resonance. That is formally true but strategically backwards: universal domination is now understood to contain the full successor positivity burden.

Regular-aperture selection instead attempts to remove only singular predecessor geometry. Generic regular negative examples show regularity does not imply positivity, so a successful A4R theorem adds real information without closing RH by assumption.

## A4R first-break gates

Reject or narrow the proposed theorem if any of these fail:

1. the exact production frozen-cutoff compression does not have the claimed `-log(L) I` coefficient;
2. frozen-cutoff analyticity/holomorphy fails on the required domain;
3. physical prime/prime-power threshold continuity is not exact;
4. an aperture-dependent basis introduces unaccounted Gram factors;
5. simultaneous determinant avoidance across the finite size/parity family cannot be established;
6. negativity cannot be preserved before moving the aperture;
7. the proof assumes the old least-bad index persists rather than reselecting first-bad;
8. the intrinsic projected predecessor is not the compression controlled by the determinant theorem.

A failure here kills or narrows A4R, not RH.

## Schur-sign discovery firewalls

- the reported source-atom determinant leading coefficient is negative; atomwise positive determinant/SOS is not the default plan;
- sampled canonical Schur energies can be the residue of extremely large channel cancellation;
- modified prime-weight experiments show that exact arithmetic coefficients matter sharply;
- therefore prefer exact combined-channel identities/remainders to independent absolute majorants;
- do not treat high precision as interval certification or theorem authority;
- a regular first-bad state with `S0<0` is still only the forced countercertificate, not a contradiction.

## Current records

Newest research delta:

`RESEARCH_LEADS_POST_138_ASTRA_DELTA.md`

External-review provenance:

`external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md`

Discovery/falsification record:

`countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`

Older post-green deltas remain historical evidence and must not be rewritten to look current.

## Permanent claim boundary

**PROVED:** theorem authority remains through PR #137.

**DERIVED:** universal one-step determinant positivity is successor positivity under the present block hypotheses; regular/resonant classification and selected determinant identities.

**LEAD / HYPOTHESIS:** log-lift dense regular-aperture selection; paired-channel regular Schur-energy bound; pole-neutral refined carrier.

**EXPERIMENTAL SIGNAL:** sharp cancellation and prime-weight sensitivity reported by the Astra audit.

**OPEN:** regular-aperture selection, regular canonical Schur-energy nonnegativity, finite negative-root exclusion, terminal Mathlib RH bridge, RH.

**RH remains OPEN.**