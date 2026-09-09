# RHRC formal audit — theorem authority through PR #137; post-#138 research frontier rerouted

> **RH remains OPEN.**

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

Live GitHub head + exact compiler/CI evidence outrank this prose. PR #138 and this research synchronization do not advance theorem authority.

## Exact theorem-state progression

### PR #134 — zero-shift source transport

**PROVED:** denominator-free whole-kernel source transport, direct zero-shift cross-parity transfer, exact zero-shift `Gamma` overlap formula, and `Gamma0*mu(z)=0` under both preimage hypotheses.

### PR #136 — absolute canonical source energy

**PROVED:** scalar-sensitive `matrixRealEnergy`, identity-shift sensitivity, exact prime/arch/scalar source-energy decomposition, cubic-shell energy, regular zero-shift trial energy `= Re S0`, and negative explicit Schur root -> negative canonical trial energy.

### PR #137 — canonical one-step determinant reduction

**PROVED:** exact complex source pairing, predecessor energy, shell coupling and

```text
Delta(w)=q_c*q_A(w)-|<w,b>|^2.
```

Also PROVED:

```text
Az=0 and Delta(z)>=0 -> shell coupling vanishes
canonicalOneStepDomination -> shell coupling in range A
canonicalOneStepDomination + predecessor nonnegativity -> Re S0>=0
canonicalOneStepDomination -> no safe negative explicit Schur root
not canonicalOneStepDomination <-> q_c<0 OR exists w, Delta(w)<0
off-line zero -> one global-first-bad state satisfying that sign-failure disjunction.
```

No theorem proves `canonicalOneStepDomination`, universal determinant sign, unconditional negative-root exclusion, or RH.

## Post-#138 independent research audit

An Astra review reconstructed the state from approximately #132 through merged #138, read the relevant theorem surface, and challenged the roadmap rather than the Lean validity.

The most important **DERIVED** correction is:

```text
A>=0 and dim(shell)=1:
q_c>=0 AND forall w, Delta(w)>=0
  <-> successor one-step quadratic form is nonnegative.
```

The universal determinant theorem is therefore a valid closing theorem but not presently a reduced RH subproblem.

## New active reduction — regular-aperture selection

The immediate research theorem is now:

> Move every strict finite canonical negative witness to an arbitrarily nearby positive aperture, preserving negativity, so that all finitely relevant predecessor parity blocks are positive definite; then reselect the global first-bad state at the moved aperture.

Candidate analytic mechanism:

```text
frozen prime cutoff Q
M_Q(L) = -log(L) I + B_Q(L)
L = exp(z)
periodic log-lift remainder
finite characteristic-polynomial root count
-> determinant nonidentity
-> dense simultaneous regular apertures.
```

This is a LEAD, not a theorem.

Required obligations are explicit: exact scalar coefficient, frozen-cutoff analyticity, physical threshold continuity, basis/Gram correctness, simultaneous avoidance in both parities and finitely many sizes, preservation of the negative witness, fresh first-bad reselection, and exact predecessor-compression identification.

## Smallest remaining obstruction after a successful A4R theorem

With predecessor `A>0`,

```text
x0 = A^-1 b
u0 = c - A^-1 b
S0 = q_c - <b,A^-1 b>.
```

Existing theorem ingredients identify the forced regular trial energy with the negative endpoint:

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive arithmetic target becomes

```text
Ecanonical(c - A^-1 b) >= 0
```

on the exact forced regular first-bad trial, equivalently

```text
<b,A^-1 b> <= q_c.
```

This scalar observable is smaller than universal domination but is not yet proved easier. Its sign remains substantial new mathematics.

## Derived observations preserved from the audit

These are not new Lean authority:

```text
k=P_(ker A)b
Delta(k)=-||k||^4
```

and a root-selected determinant identity for `w_lambda=(A-lambda I)^-1b`.

The review also reports an exact correction-vector proportionality

```text
d = -(6/(2*N-1)) a
```

with exact rational finite checks. Formalization is optional cleanup, not the current blocker.

## Falsification state

The external audit reports:

- a negative leading coefficient in the elementary source-atom two-vector determinant, so atomwise positive determinant/SOS is not a credible default route;
- sampled canonical positive Schur endpoints arising from cancellation ratios as large as approximately `6.46e20`;
- modified prime-weight experiments where relative `1e-8` changes can flip successor sign while predecessors stay positive.

These are **DERIVED/external symbolic** or **EXPERIMENTAL SIGNAL** as documented in `countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`. They are not canonical RH counterexamples and are not theorem evidence.

## Current execution order

```text
1. regular-aperture/log-lift selection
2. package one regular first-bad source countercertificate
3. interval/symbolic analysis of the full minimizing-trial Schur remainder
4. derive an independent exact prime/arch/scalar remainder or inequality
5. formalize regular canonical Schur-energy nonnegativity
6. compose with forced Re S0<0
7. explicit Mathlib RiemannHypothesis wrapper
```

Universal `q_c/Delta` domination is retained as a broad fallback if an independently positive canonical source mechanism is discovered.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority remains #137;
- external research reviews do not promote claims;
- regularity is not positivity;
- universal determinant positivity cannot count as a reduction if it merely restates successor PSD;
- atomwise source positivity is not available;
- no `A^-1` at zero before regularity;
- D is algebraic, not unitary/isometric;
- no division by unproved transfer/source factors;
- modified-source or generic countermodels are not zeta counterexamples;
- numerical precision is not theorem authority;
- machine claim promotion remains separate;
- RH remains OPEN.

Newest research implications: `research/RHRC/RESEARCH_LEADS_POST_138_ASTRA_DELTA.md`.

**RH remains OPEN.**