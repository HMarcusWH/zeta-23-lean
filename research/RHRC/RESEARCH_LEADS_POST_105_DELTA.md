# Research leads — post-PR #105 delta

> **RH remains OPEN.**

## Authority

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

## What became formally true

#105 moves the parity-badness layer from staged source into the authoritative CCM/ExceptionalZero build closure.

**PROVED:**

- (D_M E=E D_N) for all raw coefficient vectors.
- exact canonical quadratic reversal invariance.
- exact parity energy split (q(u)=q(u_+)+q(u_-)).
- every negative constrained witness has a negative even or odd component.
- parity badness persists upward at fixed aperture and fixed parity.
- every parity-bad size is at least two.
- least parity-bad size exists whenever parity badness exists.
- all smaller parity sectors are nonnegative, including the exact Euclidean inner-self form.
- the Euclidean successor parity shell has complex finrank one.
- an off-line zero forces one fixed bad parity tail and a least-bad/1D-shell endpoint.

## What changed

The project no longer needs continuous aperture flow merely to manufacture a first crossing. There is now an exact discrete first-bad event in N inside one fixed parity.

## Upstream implications

D-flow compatibility is stronger than expected: it holds before imposing parity or boundary-flat constraints. It should descend to an algebraic equivalence between the one-dimensional even and odd successor quotients.

Do not infer orthogonal-shell transport because D is not unitary.

## Downstream implications

After legal parity-constrained compression, a first-bad Hermitian problem has a nonnegative codimension-one predecessor. Therefore the negative spectral direction should be unique: a two-dimensional negative subspace would intersect the predecessor nontrivially.

This is DERIVED / OPEN FORMALIZATION until the compressed operator exists.

## Resurrected routes

The constrained Schur/Feshbach route is now live. The safe future formula must use (A-lambda I) with (lambda<0), not (A^{-1}), because the predecessor block is only semidefinite.

## New RH-relevant clues

**LEAD:** unique negative eigenline at first bad size.

**LEAD:** parity-specific KKT normals should be smaller than the full three-moment normal space: even residual channels ({1,d^2}), odd residual channel ({d}).

## Falsification checks

- the negative mode need not lie purely in the new shell;
- the opposite parity may already be bad;
- one-dimensional shell growth is generic and is not a contradiction;
- D is not unitary;
- no compressed operator or eigenmode is yet proved.

## Highest-leverage next moves

FIRST-BAD-SPECTRUM: define compression, prove quadratic agreement and symmetry, extract a negative constrained eigenmode, prove nonzero shell component, then prove uniqueness of the negative eigenline.

**RH remains OPEN.**
