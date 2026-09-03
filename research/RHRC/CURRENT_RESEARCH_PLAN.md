# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current theorem-state anchor

~~~text
theorem-state anchor = PR #107 merge b7d1022e33e2177c5597d008f593d3684d0ec720
validated theorem head = cfcf397cc8c15dbb368fbee3a161b8733061b770
validated synthetic merge = 19cd290510fe4fb1d253522c29644ff3e4563c03
validated theorem tree = 719b45162fd0814581759661f12eab16c46e1201
live main = b7d1022e33e2177c5597d008f593d3684d0ec720
theorem-bearing merged through = PR #107
RHRC #717 = SUCCESS
Permansson #490 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
RH = OPEN
~~~

## One-screen frontier

~~~text
DONE
  W0/W1/W2-ZS + finite legal approximation
  F1 canonical finite negative obstruction
  constrained algebra / Hermitianity / displacement
  Euclidean constrained sector
  exact centered N-flow
  fixed-L negative constrained tail
  exact reversal symmetry
  direct parity decomposition
  D : V_N^+ ≃ V_N^-
  exact parity dimensions N-1/N-1
  D_M E = E D_N
  exact parity quadratic split
  fixed bad parity tail
  least bad parity size >=2
  predecessor parity sector nonnegative
  exact 1D Euclidean successor parity shell
  parity-constrained Euclidean compression
  exact compressed/self quadratic equality
  compressed symmetry
  ParityBad -> negative Rayleigh eigenmode
  predecessor nonnegativity transported into successor matrix
  negative successor eigenmode not inherited
  off-line zero -> first-bad negative spectral endpoint

NOW — FIRST-BAD-RIGIDITY
  internalize predecessor image W inside successor parity subtype V
  prove dim(W^perp)=1 intrinsically in V
  prove P_(W^perp) v != 0 for the #107 negative eigenmode
  prove negative index = 1 / unique negative eigenline if cheap
  prove parity-specific normal spaces
    even residual normal = span{1,d²}
    odd residual normal = span{d}
  derive exact parity KKT residual
  derive shifted scalar Schur/Feshbach equation
  compose even KKT with D/displacement commutator collapse

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Why FIRST-BAD-RIGIDITY is next

#107 supplies the legal symmetric compressed operator and a genuine negative eigenmode at the
successor size, while proving that eigenmode is not inherited from the codimension-one nonnegative
predecessor. The remaining first-bad geometry is therefore one-channel.

**DERIVED / OPEN FORMALIZATION:** nonzero shell projection and negative index exactly one.

## Ordering correction after #107

Unique negative eigenline is no longer a prerequisite for KKT/Schur. #107 already gives a
concrete eigenpair with `lam < 0` and a non-inherited component. Do not let multiplicity API work
block the more informative parity-normal/KKT/Schur calculation.

## Schur firewall

The predecessor block may be semidefinite. The safe future equation uses `A - lam I` for
`lam < 0`:

~~~text
c - lam - b* (A - lam I)^(-1) b = 0
~~~

Never replace this with an `A⁻¹` formula at zero without a separate invertibility theorem.

**RH remains OPEN.**
