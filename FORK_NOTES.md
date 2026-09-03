# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

## Recent theorem packages

~~~text
#94  F1 canonical finite negative obstruction
#96  constrained canonical algebra
#98  Euclidean constrained sector
#100 exact centered N-flow + fixed-L negative tail
#102 exact reversal symmetry + even commutator collapse
#103 exact parity geometry + D-equivalence
#105 fixed-parity bad tail + least bad size + 1D successor shell
#107 parity compression + genuine negative eigenmode + non-inheritance
~~~

## Current frontier

~~~text
FIRST-BAD-RIGIDITY
  intrinsic predecessor subspace in successor parity space
  nonzero orthogonal shell projection
  negative index one / unique negative eigenline [derived, not yet formalized]
  parity-specific normal spaces
  KKT residual
  shifted Schur/Feshbach
  D/displacement rigidity
~~~

#107 closes the former spectral-compression gap. OBS-017 is now escaped for constrained
compression/eigenmode extraction; the raw-vs-Euclidean norm warning remains valid.

**RH remains OPEN.**
