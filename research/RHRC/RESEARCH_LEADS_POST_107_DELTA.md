# Research leads — post-PR #107 delta

> **RH remains OPEN.**

## Authority

~~~text
main = b7d1022e33e2177c5597d008f593d3684d0ec720
theorem head = cfcf397cc8c15dbb368fbee3a161b8733061b770
synthetic merge = 19cd290510fe4fb1d253522c29644ff3e4563c03
theorem tree = 719b45162fd0814581759661f12eab16c46e1201
RHRC #717 = SUCCESS
Permansson #490 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
RH = OPEN
~~~

## What became formally true

**PROVED:** exact parity-constrained compression; exact compressed/self agreement; symmetry; `ParityBad ->` a genuine negative eigenpair; successor-matrix transport of predecessor nonnegativity; negative mode not inherited; off-line zero -> fixed-aperture fixed-parity least-bad negative spectral endpoint with one-dimensional successor shell.

## What changed

The project has crossed from quadratic-form badness to a genuine finite-dimensional spectral obstruction. The proof also closes the matrix-size seam by transporting predecessor nonnegativity through exact #100 N-flow before comparing it with the successor eigenmode.

## Upstream implications

Promote the exact predecessor image to an intrinsic submodule `W` of successor parity subtype `V`, making `V = W ⊕ W^perp` the native geometry.

## Downstream implications

**DERIVED / OPEN FORMALIZATION:** `P_(W^perp)v != 0`; negative index exactly one; unique negative eigenline.

## Resurrected routes

The shifted Schur/Feshbach route is now live. With predecessor block `A >= 0` and #107 `lam<0`, `A - lam I` is invertible even if `A` has kernel. Safe target:
~~~text
c - lam - b* (A - lam I)^(-1) b = 0.
~~~

## New RH-relevant clue

**LEAD / HYPOTHESIS:** one-dimensional shell + genuine negative eigenmode + parity-small normal space + rank-two displacement law. Expected KKT residuals are even `Mv = lam v + a0*1 + a2*d²`, odd `Mv = lam v + a1*d`. In the even branch, combine with PROVED `[D,M]v=0` and inspect the projected `d³` defect.

## Falsification checks

- `v ∉ W` does not mean pure shell.
- shell invariance is unproved.
- D is not unitary.
- parity normal-space formulas are OPEN.
- predecessor semidefiniteness forbids `A⁻¹` at zero.
- no KKT contradiction, positivity, finite-to-infinite theorem or RH theorem is proved.

## Highest-leverage next moves

1. intrinsic predecessor submodule;
2. nonzero shell projection;
3. negative index one if cheap;
4. parity normal-space theorem;
5. KKT;
6. shifted Schur/Feshbach;
7. D/displacement `d³` rigidity;
8. Krylov/Hankel + T22 falsification against the distinguished eigenmode.

**RH remains OPEN.**
