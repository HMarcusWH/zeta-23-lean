# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

## Recent theorem packages

~~~text
#94  F1 canonical finite negative obstruction
#96  constrained canonical algebra
#98  Euclidean constrained sector
#100 exact centered N-flow + fixed-L negative tail
#102 exact reversal symmetry + even commutator collapse
#103 exact parity geometry + D-equivalence
#105 fixed-parity bad tail + least bad size + 1D successor shell
~~~

## Current frontier

~~~text
FIRST-BAD-SPECTRUM
  parity-constrained Euclidean compression
  compressed/self quadratic equality
  compressed symmetry
  negative Rayleigh eigenmode
  unique negative eigenline at first bad size
  nonzero shell component

THEN
  parity-specific normal spaces
  scalar Schur/Feshbach
  KKT + D/displacement rigidity
~~~

#105 closes the former staged `ParityBadness.lean` seam. OBS-018 remains as a permanent validation rule, not a current theorem gap.

**RH remains OPEN.**
