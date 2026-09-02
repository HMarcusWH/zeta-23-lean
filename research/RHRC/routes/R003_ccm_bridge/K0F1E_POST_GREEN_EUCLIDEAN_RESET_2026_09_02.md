# K0-F1E post-green Euclidean constrained reset — 2026-09-02

> **RH remains OPEN.**

## Exact validation object

~~~text
PR = #98
base = b2e0f4cdbeb7c46afbd5acae0fbad332c334a9ff
final head = 723c63badb2ac787c3dfa78369909477af6bc6a4
head tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
merge = 4f212e35fefb339646e294573dcb390dae2f6181
merge tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
RHRC #685 = SUCCESS
Permansson #458 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

## What became formally true

**PROVED**

- the three-moment map is surjective for N>=1 and its kernel is boundaryFlatSubspace N;
- finrank(boundaryFlatSubspace N)=2*N-2;
- N=1 has no nonzero boundary-flat vector, hence theorem-backed nonzero witnesses require N>=2;
- the exact Euclidean constrained sector carries the same equations and dimension;
- canonicalSourceMatrix.toEuclideanLin is symmetric;
- quadraticForm is exactly bridged to the Euclidean inner-product quantity;
- every hypothetical off-line zero forces a nonzero Euclidean constrained negative direction at some L>0,N>=2.

## What changed

OBS-017 coordinate, subspace and quadratic transport obligations are closed. The remaining spectral obligation is genuine orthogonal compression plus Rayleigh/eigenmode extraction.

The old derived codimension and N>=2 leads are now formal results.

## Upstream implications

boundaryMomentTripleMap is now the compact exact representation of the three constraints. Its rank theorem should feed parity and normal-space work.

The raw function-space norm remains separate from Euclidean norm despite successful coordinate transport.

## Downstream implications

Reopen the exact finite-N nesting slice from historical v0.8/v0.9. If central inclusion preserves the canonical matrix and Euclidean quadratic form, the same fixed-L negative direction persists to all larger truncations.

Pinned Mathlib already contains the needed orthogonal-projection and finite-dimensional Rayleigh APIs for the later compression package.

## Resurrected routes

**RESURRECTED / RE-SCOPED:** historical FTI-C1 finite nesting and retained-complement algebra. The reopened object is initially only the exact finite algebraic nesting slice, not the old finite-to-infinite/Xi convergence route.

**STILL DEAD:** DR-010 fitted small-commutator -> eigenvector convergence.

## New RH-relevant clues

**LEAD:** exact nesting + parity may produce a first bad parity size with a one-dimensional genuinely new constrained shell.

**LEAD:** even boundary-flat u plus odd displacement vector would force exact [D,M]u=0.

**LEAD:** after proving V_N^perp=span{1,d,d²}, parity may reduce the KKT residual to one or two channels.

**LEAD:** at first bad parity size and lambda<0, the previous nonnegative block A gives A-lambda I positive/invertible, creating a clean scalar secular equation.

## Falsification checks

- kill N-flow if exact nesting fails;
- prefix Fin inclusion is the wrong centered embedding;
- do not infer Euclidean isometry from raw norm;
- total dimension growth two does not prove 1+1 parity growth;
- nesting persistence alone is generic infrastructure, not RH closure;
- codimension three does not prove the explicit KKT normal basis;
- low displacement rank alone is diagonal-blind and cannot determine sign;
- no global PSD theorem is assumed.

## Highest-leverage next moves

1. exact centered finite-N embedding and principal-block theorem;
2. raw/Euclidean zero-extension preservation;
3. reversal/parity and exact parity dimensions;
4. constrained compression + negative eigenmode;
5. first bad parity size / one-dimensional new shell;
6. scalar secular + KKT/Krylov;
7. only then decide whether aperture/prime-event flow is needed.

## Standing question

Can exact centered nesting and parity turn the #98 negative Euclidean direction into a first finite counterexample whose genuinely new constrained state space is one-dimensional?

If yes, the counterexample space has been compressed to a scalar finite-shell obstruction. If no, kill or demote the route quickly.

**RH remains OPEN.**
