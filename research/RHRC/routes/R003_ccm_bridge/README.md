# R003 — CCM / finite Weil bridge

Status: **ACTIVE. FIRST-BAD PARITY SHELL PROVED; SPECTRAL COMPRESSION NEXT. RH OPEN.**

## Current authority

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

## Closed internal ladder

~~~text
F1 finite canonical obstruction                           PROVED
K0-F1/K0-F1E constrained + Euclidean finite wall          PROVED
N-FLOW fixed-L negative tail                              PROVED / #100
PARITY reversal / displacement collapse                   PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry          PROVED / #103
PARITY-BAD D/N-flow compatibility                          PROVED / #105
PARITY-BAD quadratic split                                 PROVED / #105
PARITY-BAD fixed bad parity tail                           PROVED / #105
PARITY-BAD least bad size + predecessor nonnegative        PROVED / #105
PARITY-BAD 1D successor shell                              PROVED / #105
~~~

## Current finite obstruction state

A hypothetical off-line zero now forces one fixed positive aperture and one fixed parity with a least bad size (N_*ge2). Every smaller size in that parity is nonnegative, the predecessor Euclidean parity sector is nonnegative, and the new orthogonal successor shell has complex finrank one.

## Next route state — FIRST-BAD-SPECTRUM

Build the orthogonally compressed canonical operator on the parity-constrained Euclidean subtype. Prove exact quadratic agreement and symmetry, extract a negative eigenmode, then use the codimension-one nonnegative predecessor to prove the negative spectral direction is unique and has nonzero shell component.

Only after that derive parity-specific normal spaces and the shifted scalar Schur/Feshbach/KKT equation.

## Firewalls

D is not unitary. D-flow compatibility does not imply orthogonal-shell transport or compressed intertwining. The predecessor block may be singular. One-dimensional shell geometry is not itself a contradiction.

**RH remains OPEN.**
