# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

~~~text
theorem-state anchor = PR #103 merge c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated theorem head = af43242f55536a8170bf303b9c9558c6a0fccdcf
validated synthetic merge = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
theorem-bearing merged through = PR #103
live GitHub main = authoritative
RH = OPEN
~~~

## Recent permanent theorem packages

~~~text
#93  F0-B1C-B legal boundary-flat WCONT approximation
#94  strict finite sign transfer + F1 canonical finite negative obstruction
#96  constrained canonical finite-wall algebra
#98  Euclidean constrained sector + exact mode floor
#100 exact centered N-flow + persistent fixed-L negative tail
#102 exact reversal symmetry + even constrained commutator collapse
#103 exact parity geometry + D-induced even/odd equivalence
~~~

## What #102/#103 closed

PR #102 theorem-locks reversal compatibility, moment parity, simultaneous canonical-matrix reversal invariance, oddness of displacementVector, matrix-action commutation with reversal, and exact collapse of the canonical commutator on even boundary-flat vectors.

PR #103 theorem-locks

~~~text
V_N = V_N^+ direct-sum V_N^-
D : V_N^+ ≃ₗ[ℂ] V_N^-
finrank V_N^+ = finrank V_N^- = N-1
same Euclidean parity dimensions
exact centered Euclidean N-flow preserves each parity sector.
~~~

The D-equivalence is structural: boundary-flat moment zero removes D's central ambient kernel, while an explicit odd primitive gives surjectivity.

## Current primary frontier

~~~text
import/compile ParityBadness.lean
  -> D / centered-N-flow compatibility
  -> exact quadratic parity split
  -> off-line zero -> one fixed bad parity tail
  -> least bad parity size
  -> one-dimensional new parity shell
  -> constrained compression + negative spectral mode
  -> exact normal space / KKT / scalar Schur-Feshbach rigidity
~~~

## Staged-source firewall

`Zeta23/CCM/ParityBadness.lean` is on main but was not imported by the validated #103 CCM build. Its `ParityBad`, least-bad and one-dimensional-shell declarations are **STAGED / NOT PROVED** until the module enters an authoritative compiler-tested import/build closure.

## Guardrails

- principal-block and quadratic preservation do not imply full operator intertwining.
- D-equivalence is not a unitary equivalence and does not imply equal parity spectra.
- the historical ambient coordinate-shell Schur complement is not automatically the future constrained-subspace shell.
- KKT residual form requires an exact normal-space theorem, not codimension counting alone.
- source-faithful G1-B1B/G1-final/S-NEG/G23 remains a parallel route.
- DR-010 remains dead; R002/Bombieri remain comparator lanes.
- RH remains OPEN.

## External roadmap

External v2.0 should be produced against the post-#103 validated theorem state.

**RH remains OPEN.**
