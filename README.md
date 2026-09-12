# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

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

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + predecessor parity nonnegativity             PROVED
  -> shell/KKT/Schur/secular machinery                               PROVED
  -> source-explicit transfer                                       PROVED / #129
  -> exact canonical source-moment decomposition                    PROVED / #131
  -> denominator-free zero-shift kernel/source transport            PROVED / #134
  -> scalar-sensitive absolute canonical source energy              PROVED / #136
  -> exact source pairing + one-step determinant                    PROVED / #137
  -> off-line zero => q_c<0 OR exists w, Delta(w)<0                 PROVED / #137
  -> every sufficiently large aperture has finite badness           PROVED / #140
  -> fixed-cell same-witness strict negative persistence            PROVED / #142
  -> frozen production source/predecessor + log-cover scaffold      PROVED / #144
  -> removable scalar analytic/production bridge                    PROVED / #145-#146
  -> fixed-unit archimedean parameter holomorphy                    PROVED / #148
  -> full frozen source/predecessor coordinate holomorphy           PROVED / #150
  -> deck-forced lifted determinant nonidentity                     PROVED / #150
  -> regular predecessor in every nonempty open subinterval         PROVED / #150
  -> cell-minimal regular first-bad selection                       PROVED / #150
  -> exact regular zero-shift canonical source-channel energy < 0   PROVED / #150
  -> off-line zero => one such finite regular negative certificate  PROVED / #150
```

## What #150 changed

PR #150 closes the analytic/regularization programme that had been the active frontier since #139.

The proof cleanly separates two mechanisms:

```text
deck law + finite characteristic polynomial
  -> determinant nonidentity

source/predecessor holomorphy + identity theorem
  -> regular aperture in every nonempty open interval of a fixed cell.
```

Cell-wide bad-size minimality is then combined with #142 persistence to choose a regular first-bad state without losing the strict negative witness. Existing Schur/energy theorems convert that state into exact negative canonical source-channel energy.

The current bottleneck is therefore arithmetic, not regularization.

## Active path

```text
PROVED THROUGH #150
  off-line zero
    -> sufficiently-large finite badness
    -> physical cutoff cell
    -> cell-minimal first bad
    -> open persistence of one negative witness
    -> actual regular predecessor selection
    -> unique zero-shift preimage A x0=b
    -> exact canonical source-channel energy < 0

NOW
  retain the full #150 first-bad ancestry
  -> theoremize a cancellation-preserving pole/prime discrepancy identity
  -> exploit boundary-flat high-order Taylor annihilation
  -> derive Riesz-smoothed discrepancy identities
  -> interval-certify/falsify candidate arithmetic sign mechanisms

DECISIVE OPEN THEOREM
  Ecanonical(c-x0) >= 0
  on the exact forced regular #150 state

TARGET
  contradiction with #150 negative energy
  -> negative-root exclusion
  -> explicit outside-strip/trivial-zero seam
  -> Mathlib RiemannHypothesis wrapper
```

Universal one-step domination remains a broad fallback if a genuinely independent canonical arithmetic mechanism is discovered. Repackaging successor positivity under a new name does not count as a reduction.

## Important status distinctions

At the selected #150 state:

```text
A >= 0                    theorem-backed from smaller-size goodness
A regular                 theorem-backed / #150
A > 0                     DERIVED finite Hermitian consequence
A x0 = b uniquely         theorem-backed
u0 = c-x0                 exact selected zero-shift trial
Ecanonical(u0) < 0        theorem-backed / #150
```

The theorem `exists_intrinsicPredecessorRegular_in_open_fixedCell` gives regularity in every nonempty open interval. Calling the regular set “dense” is a **DERIVED interpretation**, not a separate exported density theorem.

Likewise, the stronger statement that off-line badness yields regular negative certificates arbitrarily far out is a natural composition of #140/#150 but should remain **DERIVED** until separately packaged.

## Current arithmetic leads

### Pole/prime discrepancy

An external post-#150 audit derives a cancellation-preserving identity of the schematic form

```text
E_pole(u)-E_prime(u)
  = (1/L) * integral_0^L D(t) * g_u'(1-t/L) dt,
```

where `D` is a weighted von-Mangoldt discrepancy and `g_u` is the elementary source-atom energy.

**Status: EXTERNAL DERIVED / theoremization pending.**

### Boundary-flat Riesz smoothing

Legal boundary-flat vectors satisfy centered moment constraints `M0=M1=M2=0`. Direct Taylor expansion of the exact source atom then gives a sixth-order stationary endpoint, with first generic term

```text
-(8*pi^6/315)|M3|^2 omega^7.
```

Even parity moves the first possible term to order nine.

Conditional on the exact discrepancy identity, repeated integration by parts yields sixth/eighth-order Riesz-smoothed discrepancy formulas.

**Status: DERIVED / LEAD; not yet Lean-locked.**

The research hypothesis is that the smoothed discrepancy may be easier to bound sharply enough to preserve the enormous pole/prime/arch cancellation visible numerically.

## Post-#150 falsification memory

Current diagnostics argue against these default shortcuts:

- global aperture Loewner monotonicity;
- global zero-shift Schur monotonicity;
- universal positive elementary source-atom energy;
- loose independent pole/arch/scalar/prime majorants.

These are experimental/quarantined findings, not theorems about every canonical state.

The earlier `L*coth(L/2)` versus deck-lattice analogy is also downgraded: the coth factor uses the complex aperture variable `L`, while #150 deck translation acts in the log-cover variable `z` after `L=exp z`. No common-lattice resolvent identity follows without an additional theorem.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #150; machine claim promotion is a separate surface.
- regularity is not successor positivity.
- nonnegative + regular predecessor -> positive definite is DERIVED unless separately packaged.
- a negative exact canonical source-channel value is a countercertificate, not a contradiction.
- external exact calculations are not Lean theorem authority.
- Riesz smoothing is not a sign theorem.
- generic/modified-source countermodels are not zeta counterexamples.
- no factorwise division by unproved transfer/source quantities.
- D remains algebraic, not unitary/isometric.
- numerical precision is not theorem authority.
- negative-root exclusion is not yet the full Mathlib `RiemannHypothesis` statement without the final seam.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md` — newest project synthesis
- `research/RHRC/external_reviews/ASTRA_POST_150_ARITHMETIC_FRONTIER_ASSESSMENT_2026_09_12.md` — external-review provenance
- `research/RHRC/countermodels/POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md` — falsification/diagnostic memory
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`

Historical dated deltas remain historical and are not rewritten to look current.

**RH remains OPEN.**
