# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current theorem-state anchor

~~~text
theorem-state anchor = PR #105 merge 5e19483c905c07cfe9fef0a97f834004e77b5fb9
validated theorem head = 100fb03cccd44d1c09dadfc41cd104ba753308ee
validated synthetic merge = 4411f6a5a5c679795e043968db70f44922c2a468
theorem tree = 84ed44aaf5ff014a9352901ff1a1a31a29809b6e
theorem-bearing merged through = PR #105
RHRC #706 = SUCCESS
Permansson #479 = SUCCESS
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
  negative witness -> one bad parity
  fixed bad parity tail
  least bad parity size >=2
  predecessor parity sector nonnegative
  exact 1D Euclidean successor parity shell

NOW — FIRST-BAD-SPECTRUM
  define parity-constrained Euclidean compression
  prove compressed/self quadratic equality
  prove compressed symmetry
  extract negative constrained Rayleigh eigenmode
  prove every negative first-bad eigenmode uses the shell
  prove unique negative eigenline / negative index one

THEN
  prove parity-specific normal spaces
    even residual normal = span{1,d²}
    odd residual normal = span{d}
  derive scalar shifted Schur/Feshbach equation
  combine KKT residual with D/displacement identities

IF NEEDED
  reopen aperture/prime-event first crossing

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Why FIRST-BAD-SPECTRUM is next

At the #105 least bad size (N_*), the predecessor parity sector is nonnegative and has codimension one in the bad parity sector. After legal compression, this should force at most one negative spectral direction; badness forces at least one. The expected result is therefore one negative eigenline.

Do not infer this before compression is formalized.

## D-flow consequence

#105 proves (D_ME=ED_N) on all raw vectors. Together with #103, D should descend to an algebraic equivalence between the one-dimensional parity quotient increments. This does not imply orthogonal-shell equivalence because D is not unitary.

## Schur firewall

The predecessor block may be semidefinite. The safe future equation uses (A-lambda I) for a negative eigenvalue (lambda<0), not (A^{-1}) at zero.

**RH remains OPEN.**
