# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
theorem-bearing merged through = PR #119
FIRST-BAD-RIGIDITY-E3-A exact canonical secular equivalence = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/CI remain authoritative over these prose anchors.

## One-screen frontier

```text
DONE
  W0/W1/W2-ZS + finite legal approximation
  F1 canonical finite negative obstruction
  constrained algebra / Hermitianity / Euclidean sector
  exact centered N-flow + fixed-L negative tail
  exact reversal symmetry + even commutator collapse
  direct parity decomposition + algebraic D-equivalence
  least/global first bad + predecessor nonnegative
  negative first-bad eigenmode + noninheritance
  exact parity normals + KKT
  rank-at-most-one cubic parity defect
  intrinsic W/S block, dim_C S=1, exact cubic factorization
  canonical V=W⊕S coordinates
  safe shifted predecessor resolvent
  basis-free shifted Schur identity
  E1 canonical cubic shell incidence / #115
  E2 canonical cubic quotient coordinate + normalized Schur / #118
  E3-A exact canonical secular root <-> negative-shift eigenmode / #119

NOW — E3-B1: PROJECTED SYMMETRY / SHIFTED COERCIVITY
  prove intrinsicPredecessorBlock symmetric in the exact repository inner product
  prove A-lam I symmetric for real lam
  prove quantitative coercivity for lam<0
  derive ||R_lam b|| <= ||b||/(-lam)
  prove resolvent quadratic value is real/nonnegative and safely bounded

NEXT — E3-B2: EXPLICIT SECULAR BRIDGE
  define/use the normalized explicit Schur scalar on the canonical cubic shell
  prove exact pointwise equality with #119 cubicSecularScalar
  respect Mathlib convention: complex inner product linear in second argument
  only after this bridge attach sign/monotonicity claims to the #119 scalar

PARALLEL / NEXT — E4-A: ZERO RESONANCE / PARITY NULLITY
  prove generic rank-at-most-one shifted-nullity difference lemma
  specialize to even/odd compressed canonical operators through algebraic D-equivalence
  classify predecessor zero resonance
  test whether b=Bc annihilates ker A

THEN — E3-B3: QUANTITATIVE PREDECESSOR-FLOOR THEOREM
  introduce a theorem-level lower floor mu on A
  for lam<mu prove resolvent bound with denominator mu-lam
  define theorem-backed q_N and beta_N from canonical c_N
  derive d_N(g_N+d_N) <= beta_N^2
  use d_N <= beta_N^2/g_N only when g_N>0 is independently certified

THEN — E3-C: RESOLVENT IDENTITY / MONOTONICITY
  prove finite-dimensional shifted resolvent identity without calculus if possible
  derive scalar monotonicity only on the exact real explicit secular representation
  root uniqueness / negative-index control if justified
  do not confuse uniqueness with absence

TARGET
  CCM-specific negative-root exclusion at the global first-bad state
  combine shell/parity/KKT/N-flow/zero-resonance constraints
  positivity / finite-to-infinite closure remains open until separately proved

PARALLEL DIAGNOSTIC
  probe g_N=q_N-mu_N, beta_N, beta_N^2/g_N
  kill the deformation-budget route cheaply if gap/coupling/summability fails
  no PRUNE without a complete assured infinite-tail certificate

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
```

## What PR #118 made possible

PR #118 makes the one-dimensional shell canonical rather than basis-dependent. The cubic shell coordinate is faithful, the successor/predecessor quotient is represented by one complex scalar, and genuine negative eigenmodes can be normalized so their shell component is exactly `intrinsicCubicShellPart`.

This removes arbitrary shell scaling from every downstream Schur/resolvent quantity.

## What PR #119 made possible

For every safe negative shift the repository now has a canonical trial vector

```text
u_lam = -(A-lam I)^(-1)Bc + c
```

and residual

```text
r_lam = T u_lam - lam u_lam.
```

The predecessor coordinate of the residual is exactly zero. Therefore the canonical quotient coordinate detects the entire residual:

```text
cubicSecularScalar(lam)=0
  <-> r_lam=0
  <-> u_lam is a genuine eigenmode
  <-> exists a nonzero eigenmode at lam.
```

This changes the project from a one-way Schur necessary condition to an exact one-variable spectral criterion on the negative axis.

## Why E3-B is the immediate next layer

The exact #119 scalar is **not defined as** the #113/#118 inner-product Schur expression. Sign, realness and monotonicity of the explicit Schur expression cannot be transferred to `cubicSecularScalar` until a theorem identifies them pointwise.

Projected predecessor symmetry and resolvent symmetry are the natural bridge because the canonical quotient coordinate uses

```text
<c,s>/<c,c>
```

while the old block identity was derived using full-operator symmetry and cross terms with the repository's fixed complex inner-product orientation.

The smallest useful E3-B package is therefore metric, not another shell abstraction.

## Zero resonance promoted to a primary obstruction

The global-first-bad predecessor is only nonnegative. Thus

```text
ker A
```

may be nonzero. For `lam<0`, `A-lam I` is safely invertible, but the resolvent can diverge as `lam -> 0-` on the zero eigenspace.

The high-information split is:

```text
Case 1: A has a positive lower floor.
  -> E3-B3 applies directly.

Case 2: ker A != 0.
  -> determine whether Bc is orthogonal to ker A.
  -> if yes, the dangerous zero eigenspace decouples from the secular channel.
  -> if no, exploit the resonant singular component as a separate rigidity signal.
```

This is why E4-A moves forward in priority.

## Quantitative deformation composition

Once a lower predecessor floor `mu` is available, the intended exact theorem shape is

```text
mu ||w||^2 <= Re <Aw,w>
lam < mu
R_lam = (A-lam I)^(-1)
```

implying

```text
(mu-lam) ||R_lam b|| <= ||b||
Re <R_lam b,b> <= ||b||^2/(mu-lam).
```

For the canonical shell vector `c`, define scale-free

```text
q_N = Re <Tc,c> / ||c||^2
beta_N^2 = ||Bc||^2 / ||c||^2.
```

At a negative secular root, with

```text
d_N = mu_N-lam
g_N = q_N-mu_N,
```

the target inequality is

```text
d_N(g_N+d_N) <= beta_N^2.
```

The shortcut `d_N <= beta_N^2/g_N` requires independently certified `g_N>0`.

All of this remains DERIVED / LEAD until Lean theoremizes the exact hypotheses.

## Deformation-budget falsification gates

- `q_N-mu_N` must remain usefully positive in the tested regime;
- `beta_N` must exhibit useful decay;
- `beta_N^2/(q_N-mu_N)` must admit a complete certified summable tail majorant, not merely tend to zero;
- the result must survive both parity carriers and the required positive-L regime;
- reduced/reference decision commutation remains required for decision-bearing reduced calculations;
- a finite prefix, fitted tail or local residual is not an infinite-horizon certificate.

## E4-A falsification gates

- D remains algebraic, not unitary/isometric;
- derive nullity comparison from rank/range algebra, not Hermitian interlacing through D;
- shifted kernel statements must use the exact transported operators at the same scalar;
- zero-resonance conclusions must distinguish `ker A`, `ker T_even`, and `ker T_odd`;
- do not assume `Bc` is orthogonal to `ker A`; test/prove it;
- simultaneous parity resonance remains OPEN until separately classified.

## Permanent claim boundary

**PROVED:** through PR #119, including exact canonical negative secular root/eigenmode equivalence and the off-line-zero -> global-first-bad negative-root endpoint.

**DERIVED / OPEN FORMALIZATION:** projected predecessor symmetry, shifted coercivity, resolvent positivity/bounds, pointwise explicit-Schur bridge, parity shifted-nullity difference.

**LEAD / HYPOTHESIS:** kernel-coupling decoupling, theorem-backed deformation budget, resolvent monotonicity/root uniqueness, CCM-specific root exclusion.

**OPEN:** positivity, finite-to-infinite closure, RH.

Detailed post-green lead delta: `RESEARCH_LEADS_POST_119_DELTA.md`.

**RH remains OPEN.**