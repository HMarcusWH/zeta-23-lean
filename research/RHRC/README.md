# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
centered N-flow / parity / first-bad / shell / Schur package            PROVED / #100-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing + one-step determinant                   PROVED / #137
off-line zero -> q_c<0 OR exists w, Delta(w)<0                         PROVED / #137
aperture freedom at every sufficiently large L                          PROVED / #140
fixed-cell actual-source continuity + fixed-witness persistence          PROVED / #142
frozen/log-cover source/predecessor scaffold                            PROVED / #144
scalar removable analytic/production bridge                             PROVED / #145-#146
fixed-unit archimedean parameter holomorphy                             PROVED / #148
assembled full frozen source/predecessor holomorphy                     PROVED / #150
deck-forced determinant nonidentity                                     PROVED / #150
open-interval actual predecessor regular selection                      PROVED / #150
cell-minimal regular first-bad selection                                PROVED / #150
regular zero-shift exact canonical source-channel energy < 0            PROVED / #150
off-line zero -> finite regular negative-energy certificate             PROVED / #150

regular selected-residual arithmetic sign                               OPEN / NOW
universal canonical one-step domination                                 OPEN / BROAD FALLBACK
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero seam + terminal RH bridge                     OPEN
RH                                                                       OPEN
```

## What #150 changed

The analytic regularization route is complete.

PR #150 assembles the actual frozen source/predecessor analytic family, proves determinant nonidentity algebraically from the deck law and finite characteristic-polynomial rigidity, and uses one-variable analytic uniqueness to put an actual regular predecessor in every nonempty open interval of a physical cutoff cell.

That is then composed with cell-wide bad-size minimality and #142 persistence to produce a regular first-bad state carrying exact negative source-channel energy.

The current problem is no longer “can we move to a regular aperture?” It is:

```text
why can the exact #150 selected residual not have negative canonical energy?
```

## Current execution priority

1. **Retain the full #150 certificate.** Preserve cell-minimal ancestry and smaller-size information before the outer wrapper compresses it.
2. **Theoremize the cancellation-preserving pole/prime identity.** Reproduce the external discrepancy calculation in exact repository notation.
3. **Spend the exact boundary-flat moments.** Prove the source-atom Taylor annihilation through order six, and order eight in even parity.
4. **Derive the Riesz-smoothed discrepancy identities.** Keep these as identity/compression theorems, not sign claims.
5. **Run interval-certified falsification.** Test candidate kernels/inequalities on exact canonical regular selected-residual observables.
6. **Prove the scoped arithmetic sign** `Ecanonical(c-x0)>=0` on the exact forced state.
7. **Compose to negative-root exclusion and then close the terminal Mathlib seam.**

Universal A4b2b domination remains a broad fallback if a genuinely independent canonical arithmetic mechanism appears.

## Formal endpoint and derived interpretation

At the selected #150 state:

```text
A>=0                    theorem-backed from smaller-size goodness
A regular               theorem-backed
A>0                     DERIVED finite Hermitian consequence
unique x0 with A x0=b   theorem-backed
u0=c-x0
Ecanonical(u0)<0         theorem-backed
```

The exact regularity theorem is `exists_intrinsicPredecessorRegular_in_open_fixedCell`. “Dense regular apertures” is a correct **DERIVED interpretation** of that open-interval theorem, not a separate exported density declaration.

## Post-#150 arithmetic reduction

The external Astra audit proposes a cancellation-preserving identity

```text
E_pole(u)-E_prime(u)
  = (1/L) * integral_0^L D(t) g_u'(1-t/L) dt,
```

where `D` is a weighted von-Mangoldt discrepancy and `g_u` is the exact elementary source-atom energy.

**Status: EXTERNAL DERIVED / theoremization pending.**

The project synthesis then observes that legal boundary-flat vectors satisfy `M0=M1=M2=0`, forcing

```text
g_u(omega) = -(8*pi^6/315)|M3|^2 omega^7 + O(omega^9)
```

generically, and order nine in even parity. Conditional on the discrepancy identity, repeated integration by parts produces sixth/eighth-order Riesz-smoothed discrepancy expressions.

**Status: DERIVED / LEAD.**

## Falsification memory

Do not silently re-enter these shortcuts:

- global aperture Loewner monotonicity — experimental mixed-sign derivative evidence;
- global zero-shift Schur monotonicity — experimental sign changes;
- universal positive elementary source atom — experimental sign changes;
- independent loose channel majorants — conditioning/cancellation warning;
- coth/deck common-lattice identification — coordinate mismatch unless a new transform theorem is proved.

These are route-design constraints, not RH evidence.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md` — newest project synthesis.
- `external_reviews/ASTRA_POST_150_ARITHMETIC_FRONTIER_ASSESSMENT_2026_09_12.md` — external provenance.
- `countermodels/POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md` — discovery/falsification memory.
- `RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md` — historical pre-#150 frontier.
- `OBSTRUCTION_LEDGER.md` — reusable blockers.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #150; machine claim promotion remains separate.
- regularity is not successor positivity.
- negative exact selected energy is not a contradiction without an independent nonnegativity theorem.
- external derivations and numerical experiments are not Lean authority.
- Riesz smoothing is not a sign theorem.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- D remains algebraic, not unitary/isometric.
- terminal negative-root exclusion still needs the outside-strip/trivial-zero seam before the Mathlib `RiemannHypothesis` wrapper.

**RH remains OPEN.**
