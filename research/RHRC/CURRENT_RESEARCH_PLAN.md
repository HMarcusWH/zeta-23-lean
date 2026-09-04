# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current theorem-state anchor

~~~text
theorem-state anchor = PR #113 merge d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
validated theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
theorem-bearing merged through = PR #113
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
RH = OPEN
~~~

## One-screen frontier

~~~text
DONE
  W0/W1/W2-ZS + finite legal approximation
  F1 canonical finite negative obstruction
  constrained algebra / Hermitianity / Euclidean sector
  exact centered N-flow + fixed-L negative tail
  exact reversal symmetry + even commutator collapse
  direct parity decomposition + algebraic D-equivalence
  fixed bad parity tail + least bad size
  predecessor parity sector nonnegative
  exact 1D Euclidean successor parity shell
  parity-constrained Euclidean compression
  genuine negative Rayleigh eigenmode
  negative first-bad eigenmode not inherited
  nonzero ambient shell projection
  exact parity normal spaces + KKT residual
  explicit nonzero cubic odd channel g_N=P_-d^3
  parity compressed defect range in C g_N and finrank <=1
  global least bad size with BOTH predecessor parities nonnegative
  intrinsic predecessor W inside successor V
  intrinsic one-dimensional shell S inside successor V
  exact cubic defect functional and factorization F_N(v)=ell_N(v) g_N
  canonical complement V = W ⊕ S
  canonical predecessor/shell projections
  shellPart(v)=0 iff v∈W
  first-bad negative mode has canonical shellPart !=0
  projected predecessor block A=P_W T|_W
  predecessor nonnegativity descends to A
  A-lam I bijective for every real lam<0
  shifted resolvent R=(A-lam I)^(-1)
  (A-lam I)w=-Bs and w=-R Bs
  basis-free scalar shifted Schur identity
  off-line zero -> same global-first-bad KKT+cubic+Schur finite state

NOW — FIRST-BAD-RIGIDITY-E1: CUBIC-SHELL INCIDENCE
  exploit shellPart(x)=0 iff x∈W
  prove/falsify exact odd cubic projection formula
  prove odd cubic generator at successor size is not in centered predecessor W
  conclude canonical odd cubic shellPart !=0
  pull cubic generator algebraically through D^-1 for the even carrier
  prove corresponding even predecessor non-membership / shellPart !=0

THEN — E1b / E2
  dim_C S=1 + two nonzero shell vectors
    -> negative-mode shell coordinate = beta * cubic shell coordinate, beta!=0
  transfer #113 Schur identity onto the canonical cubic shell line
  normalize by shell norm / scalar scale
  obtain a scale-free one-dimensional cubic-normalized secular equation

THEN — E3
  prove projected predecessor block A symmetric
  strengthen A-lam I to quantitative shifted coercivity
  derive positive-resolvent / norm-bound statements if Lean-cheap
  establish scalar resolvent monotonicity if possible

THEN — E4
  theoremize parity nullity-difference <=1 algebraically
  package common even/odd resonance vs one-channel opposite-parity resolvent
  classify or exclude simultaneous first-bad resonance using KKT/displacement/cubic/shell data

OPTIONAL / CHEAP IF AVAILABLE
  codim-one predecessor nonnegative + negative successor mode
    -> negative index exactly one / unique negative eigenline

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Why E1 is now the highest-leverage next theorem

#112 and #113 completed the tasks that the post-#110 plan listed under FIRST-BAD-RIGIDITY-D: the native predecessor/shell geometry, exact cubic factorization, safe shifted inverse and scalar Schur identity are all theorem-backed.

The remaining first-bad problem now contains two independently constructed one-dimensional structures at the same finite state:

~~~text
S_N = intrinsic N-flow shell, dim_C S_N = 1
g_N = explicit cubic parity-defect generator.
~~~

The #113 theorem

~~~text
intrinsicShellPart p N x = 0
  <-> x ∈ intrinsicParityPredecessorSubspace p N
~~~

changes the proof strategy. To show the cubic channel couples to the shell, it is enough to prove that the cubic generator is not a centered predecessor extension. This is substantially smaller than building another ambient projection-comparison layer.

## E1 explicit route to test first

For the odd carrier, the exact odd normal space is `span{d}` and `g_K` is the orthogonal projection of `d^3` to the odd boundary-flat sector. The current algebraic lead is

~~~text
g_K = d^3 - alpha_K d,
alpha_K = <d,d^3>/<d,d>.
~~~

On the centered grid `-K,...,K`, power-sum algebra suggests

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5,
(g_K)_(+K) = K(K-1)(2K-1)/5.
~~~

For `K>=2` the predicted outer coefficient is nonzero, whereas exact centered predecessor extension has zero on the new outer coordinates. If the repository's exact `orthogonalProjectionOnto`, inner-product convention and size indexing yield this formula, non-membership in W follows immediately.

**Status: LEAD / HYPOTHESIS.** The formula must be theoremized or falsified before any downstream use.

## E2 composition target

Suppose E1 gives a cubic vector `c` with

~~~text
intrinsicShellPart p N c != 0.
~~~

The first-bad negative eigenmode `v` already satisfies

~~~text
intrinsicShellPart p N v != 0,
Module.finrank C S = 1.
~~~

Therefore the two shell coordinates are nonzero scalar multiples. The #113 Schur expression is homogeneous of degree two in the shell vector, so the scalar can be normalized away. The target is a scalar equation attached to the **canonical cubic shell line** rather than an arbitrary eigenvector normalization.

This is the first intended direct composition of the N-flow shell and the parity cubic-defect channel.

## E3 shifted-block target

#113 proves only what is needed for safe inversion. The next useful strengthening is

~~~text
A symmetric,
Re <A w,w> >= 0,
lam < 0
  -> Re <(A-lam I)w,w> >= (-lam)||w||^2.
~~~

This should support a resolvent norm bound and, through a resolvent identity, monotonicity of the scalar Schur correction. These are generic rigidity tools; they become RH-relevant only after composition with the special CCM shell/cubic/parity structure.

## E4 resonance target

After algebraically transporting the odd compression to the even carrier, #110/#112 give a rank-at-most-one / exact one-channel defect. Standard finite-dimensional algebra suggests a kernel/nullity difference of at most one at each scalar. For an eigenvector one obtains a dichotomy:

~~~text
lam common even/odd resonance
OR
D v lies in one opposite-parity resolvent channel generated by g_N.
~~~

Do not invoke Hermitian rank-one interlacing: D is not unitary.

## Falsification gates

Before building around E1/E2, require these checks:

- derive the cubic projection formula from the exact repository projection rather than parity intuition;
- keep predecessor size N and successor size N+1 explicit;
- verify exact outer-coordinate behavior of centered zero extension;
- for the even pullback use only algebraic D-equivalence, not metric compatibility;
- remember `g_N !=0` does not imply `cubicDefectFunctional !=0`;
- remember nonzero shell coordinate does not imply pure shell;
- remember the scalar Schur equation can have negative roots in generic Hermitian systems;
- remember uniqueness/monotonicity of a negative root is not absence;
- keep simultaneous resonance open until excluded by theorem;
- do not introduce an RH-equivalent arithmetic hypothesis as an auxiliary estimate.

## Current claim boundary

**PROVED:** intrinsic direct-sum block geometry, exact cubic factorization, safe shifted inverse, predecessor reconstruction and scalar Schur equation at the same global first-bad finite state forced by an off-line zero.

**DERIVED / OPEN FORMALIZATION:** projected A symmetry, quantitative shifted coercivity, negative index exactly one, resolvent monotonicity, parity nullity difference, resonance/resolvent dichotomy.

**LEAD / HYPOTHESIS:** cubic-shell incidence, explicit outer coefficient formula, cubic-normalized Schur rigidity and exclusion of the remaining first-bad state.

**OPEN:** positivity / finite-to-infinite closure / RH.

Detailed post-green reasoning: `RESEARCH_LEADS_POST_113_DELTA.md`.

**RH remains OPEN.**
