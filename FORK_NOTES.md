# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant + sign-failure endpoint
#140 eventual aperture freedom + predecessor regularity scaffold
#142 fixed-cell continuity + same-witness persistence
#144 exact frozen production source/predecessor + logarithmic-cover scaffold
#145-#146 removable scalar analyticity + production bridge
#148 fixed-unit alpha/beta/gamma parameter holomorphy
#150 assembled source/predecessor holomorphy + determinant rigidity
#150 open-interval actual predecessor regularity
#150 cell-minimal regular first bad + exact negative source-channel energy
#150 off-line zero -> finite regular negative-energy certificate
```

## What #150 adds

**PROVED:** the exact frozen source remainder is entrywise analytic on an explicit punctured source strip, and its actual intrinsic predecessor scalar coordinates remain analytic after parity compression/projection and log lifting.

**PROVED:** deck translation forces lifted determinant nonidentity by finite characteristic-polynomial rigidity.

**PROVED:** every nonempty open interval inside one physical cutoff cell contains a regular actual intrinsic predecessor aperture.

**PROVED:** whole-cell bad-size minimization composes with #142 persistence and regular selection to produce a regular cell-minimal first-bad state.

**PROVED:** that state carries a unique zero-shift preimage, a safe negative explicit root and strictly negative exact canonical source-channel energy.

**PROVED:** a hypothetical off-line zero forces one such finite regular negative-energy certificate.

No theorem proves the selected energy nonnegative, excludes the hypothetical zero, or proves RH.

## Current frontier

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4R0 aperture freedom                                            PROVED / #140
A4R1a fixed-cell negative persistence                            PROVED / #142
A4R1b analytic/log-cover/determinant regularity                  PROVED / #144-#150
A4R1c cell-minimal regular first-bad selection                   PROVED / #150
A4b2r exact regular negative selected residual                   PROVED / #150
A4b2r independent selected-residual nonnegativity                OPEN / NOW
A4b2b universal shell/determinant domination                     OPEN / BROAD FALLBACK
global negative-root exclusion                                   OPEN
outside-strip/trivial-zero + terminal Mathlib RH wrapper          OPEN
RH                                                               OPEN
```

## Current research reduction

The active object is the exact selected zero-shift residual `u0=c-x0`, where `A x0=b` uniquely at the #150 regular predecessor.

The next work is not another regularity proof. It is to understand the cancellation structure of

```text
Ecanonical(u0)<0
```

forced by a hypothetical off-line zero and prove independently that the exact forced state must instead satisfy

```text
Ecanonical(u0)>=0.
```

An external post-#150 audit proposes a pole-minus-prime discrepancy integral that preserves cancellation before estimation. The project synthesis combines that with the exact boundary-flat moments to derive candidate sixth/eighth-order Riesz-smoothed discrepancy identities.

These are **EXTERNAL DERIVED / DERIVED LEADS**, not yet Lean theorem authority.

## Valuable state not to discard

The cell-minimal construction carries more ancestry than the outer energy endpoint exports:

```text
whole-cell K* minimality
all smaller sizes good throughout the cell
both parity sectors nonnegative at smaller sizes
open persistence of the selected bad witness
selected regular predecessor
negative root
A x0=b
exact negative energy.
```

The next theorem interface should consider preserving this full state. A finite simultaneous-regularity strengthening across both parities/smaller sizes is also worth theoremizing if it remains cheap.

## Current falsification firewalls

- raw aperture Loewner monotonicity is not supported by canonical experiments;
- scalar zero-shift Schur monotonicity is not supported globally;
- elementary atom energy is signed in tested states;
- coarse independent channel bounds are conditioning-hostile;
- coth aperture singularities and log-cover deck translations live in different coordinates.

These findings constrain route design but do not prove the desired sign.

## Firewalls

- RH remains OPEN.
- theorem authority is through #150 only.
- machine claim promotion remains separate.
- regularity is not successor positivity.
- `A>0` at the selected state is a DERIVED finite Hermitian consequence unless separately packaged.
- the open-interval regularity theorem supports a dense interpretation but “dense” is not the exact theorem declaration.
- negative exact source-channel energy is not a contradiction.
- external discrepancy/Riesz work is not theorem authority until formalized.
- no factorwise division by unproved transfer quantities.
- D remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib RH wrapper without explicit final bookkeeping.

Newest research detail: `research/RHRC/RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**
