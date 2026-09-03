# Research leads — post-PR #103 delta

> **RH remains OPEN.**

## Authority

~~~text
PR #103 final validated head = af43242f55536a8170bf303b9c9558c6a0fccdcf
synthetic merge tested = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
PR #103 merge = c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated/merged theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
RHRC #704 = SUCCESS
Permansson #477 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

## What became formally true

The boundary-flat sector is exactly the direct sum of its even and odd reversal sectors.

The centered-index operator restricts to a complex-linear equivalence:

~~~text
D : V_N^+ ≃ₗ[ℂ] V_N^-.
~~~

This is not merely a dimension identity. Boundary-flat moment zero removes the sole ambient central kernel and an explicit primitive gives every odd constrained vector a preimage.

For N>=1 both sectors, and their Euclidean copies, have finrank N-1. Exact centered Euclidean N-flow preserves each parity.

## What changed

The expected 1+1 growth split has a structural reason tied to the same D used in the displacement algebra.

## Upstream implications

**LEAD:** theorem-lock `D_M E = E D_N`. If true, D should pair the new parity quotient directions coherently across N.

## Downstream implications

**DERIVED:** once the quadratic cross term is formally zero, every negative constrained witness has a negative parity component. #100/#103 should then produce one fixed bad parity tail.

At a least bad size in that parity, the N-1 dimension law gives the intended one-dimensional successor shell.

## Resurrected routes

Parity-resolved resolvent/barycentric analysis becomes structurally eligible after constrained spectral extraction and first-bad reduction.

## New RH-relevant clues

**LEAD:** after the exact normal-space theorem, the failure of compressed D-intertwining must pass through a small parity-resolved normal space. This is a concrete finite-rank rigidity target.

## Falsification checks

D is not unitary. Equal dimensions do not imply equal spectra. Ambient commutator collapse does not imply compressed intertwining. A one-dimensional shell can generically create a negative eigenvalue.

## Staged-source warning

`ParityBadness.lean` is on main but was not imported by the exact #103 build. Its declarations remain STAGED / NOT PROVED.

## Highest-leverage next moves

Compile parity badness; prove D/N-flow compatibility; prove quadratic parity split; derive fixed bad parity tail; validate least bad parity + 1D shell; then build constrained compression.

**RH remains OPEN.**
