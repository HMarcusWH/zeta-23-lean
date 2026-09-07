# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
theorem tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
theorem-bearing merged through = PR #122
E3-B1 metric layer + E4-A1 zero-resonance coupling classification = PROVED / MERGED

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
  E3-B2 exact explicit Schur scalar bridge / #121
  E3-B1 projected symmetry + shifted coercivity/resolvent metric control / #122
  E4-A1 exact ker(A) cubic-coupling classification / #122

NOW — E4-A2: ZERO-SHIFT / RANGE-ENDPOINT SPLIT
  Case A: coupling vanishes on ker A
    prove b ⟂ ker A -> b ∈ range A for the finite symmetric projected block
    obtain x0 with A x0 = b
    define/prove the zero-shift endpoint algebraically, without A^-1
  Case B: coupling does not vanish on ker A
    isolate a kernel witness z with <z,b> != 0
    theoremize the corresponding zero-resonant contribution to R_lam b
    determine the induced sign/asymptotic restriction on the secular scalar as lam -> 0-

PARALLEL — E3-C: RESOLVENT IDENTITY / MONOTONICITY
  prove finite-dimensional shifted resolvent identity
  exploit #122 real exact scalar representation
  prove strict monotonicity on lam<0 if justified
  derive at most one negative root / negative-index control
  never confuse uniqueness with absence

PARALLEL — E4-B: PARITY SHIFTED-NULLITY
  use finrank-at-most-one defect + algebraic D-equivalence
  theoremize shifted-nullity difference without unitary assumptions
  connect only where the exact first-bad state permits

PARALLEL — E3-B3: GENERAL LOWER-FLOOR DEFORMATION THEOREM
  under mu ||w||^2 <= Re<Aw,w> and lam<mu,
  prove the mu-lam resolvent bound
  theoremize q_N, beta_N and d_N(g_N+d_N) <= beta_N^2
  use d_N <= beta_N^2/g_N only after independent g_N>0

TARGET
  CCM-specific negative-root exclusion at the global first-bad state
  combine shell/parity/KKT/N-flow/zero-resonance/endpoint constraints
  positivity / finite-to-infinite closure remains open until separately proved

PARALLEL DIAGNOSTIC
  probe g_N=q_N-mu_N, beta_N, beta_N^2/g_N
  no PRUNE without a complete assured infinite-tail certificate

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
```

## What #121/#122 made possible

PR #121 proves the pointwise bridge

```text
F(lam)=star(S(lam))/<c,c>
```

between the exact quotient-coordinate root detector `F` and the explicit cubic Schur scalar

```text
S(lam)=<Tc,c>-lam<c,c>-<R_lam Bc,Bc>.
```

PR #122 proves that `S(lam)` is real in the safe negative-shift regime and theoremizes the exact metric structure needed for scalar analysis. Hence

```text
F(lam)=S(lam)/<c,c>
```

and at a root

```text
0 <= Re(<Tc,c>-lam<c,c>)
(-lam) * Re(<Tc,c>-lam<c,c>) <= ||Bc||^2.
```

The old representation barrier is therefore closed. Scalar sign/monotonicity work can now target the actual exact root detector rather than a merely related expression.

## E4-A1 changes the zero-resonance question

Let

```text
A = intrinsicPredecessorBlock = P_W T|_W
c = intrinsicCubicShellPart
b = intrinsicShellToPredecessor c.
```

For every `z` with `Az=0`, #122 proves

```text
<z,b> = star(kappa(Tz)) <c,c>
```

and therefore

```text
<z,b>=0 <-> Tz=0.
```

So the previous vague question “does `b` annihilate `ker A`?” is now an exact dichotomy:

```text
all kernel couplings vanish
  <-> every projected-kernel vector is already a successor zero mode;

some kernel coupling is nonzero
  <-> some projected-kernel vector has a nonzero shell image under the successor operator.
```

Neither branch is currently ruled out.

## Why E4-A2 is the immediate next layer

The zero-resonance branch now determines the endpoint geometry of the exact secular scalar.

### Decoupled branch

If `b ⟂ ker A`, finite-dimensional symmetry should give

```text
b ∈ range A.
```

This would provide an exact algebraic zero-shift witness `x0` satisfying `Ax0=b`, avoiding the forbidden move of pretending that `A^-1` exists at zero. The finite endpoint candidate becomes

```text
S(0-) = <Tc,c> - <x0,b>
```

once independence of the chosen solution and compatibility with the negative-shift limit are separately theoremized.

### Resonant branch

If some `z∈ker A` has `<z,b>!=0`, the shifted resolvent should carry a `1/(-lam)` component in the zero eigenspace. The fastest useful theorem is not a generic asymptotic slogan but an exact lower/sign statement sufficient to decide whether the explicit secular scalar is forced negative near zero.

## E3-C monotonicity lane

With symmetry and realness now proved, the expected finite-dimensional spectral picture is

```text
A >= 0,
R_lam=(A-lam I)^(-1),
lam<0.
```

The target scalar identity should imply that `S` is strictly decreasing in `lam` on the safe negative axis. This may be formalized by a resolvent identity rather than calculus.

If successful:

```text
S has at most one negative root.
```

Permanent firewall: this does not exclude that one root.

## Quantitative deformation composition

The #122 `mu=0` root metric bound is now theorem-backed. The reusable generalization remains:

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

For canonical shell quantities

```text
q_N = Re <Tc,c> / ||c||^2
beta_N^2 = ||Bc||^2 / ||c||^2
d_N = mu_N-lam
g_N = q_N-mu_N,
```

the target remains

```text
d_N(g_N+d_N) <= beta_N^2.
```

The shortcut `d_N <= beta_N^2/g_N` requires independently certified `g_N>0`.

## Upstream cleanup candidate

`re_inner_shiftedIntrinsicPredecessorBlock_ge` currently accepts `hlam : lam < 0`, although the displayed quadratic comparison itself is produced from predecessor nonnegativity plus the algebraic shift. Negativity is needed downstream to obtain a positive coercive floor and perform cancellation/division. A later cleanup may split the algebraic inequality from the negative-shift corollary.

This is a dependency-compression opportunity, not the current critical path.

## Falsification gates

- generic block systems with `A=0`, `b!=0` show that zero resonance can generate negative spectrum; do not assume resonance is benign;
- `b=0` alone does not exclude a negative root if the shell diagonal is negative;
- monotonicity gives uniqueness, not absence;
- do not identify `ker A` with the predecessor-size compressed-operator kernel;
- do not use successor positivity to prove the endpoint sign: that would be circular at the first-bad state;
- D remains algebraic, not unitary/isometric;
- no finite prefix, fitted tail or observed decay is an infinite-horizon certificate.

## Permanent claim boundary

**PROVED:** through PR #122, including the exact real explicit secular representation, projected metric/resolvent bounds, the first root metric inequality, and the E4-A1 kernel-coupling equivalence.

**DERIVED / OPEN FORMALIZATION:** finite-dimensional `range A = (ker A)⊥` specialization for the projected block; zero-shift solution-based endpoint; generic rank-one shifted-nullity comparison.

**LEAD / HYPOTHESIS:** resonant near-zero secular forcing, strict secular monotonicity/root uniqueness, positive-floor deformation budget, CCM-specific root exclusion.

**OPEN:** which E4-A1 branch occurs, negative-root exclusion, positivity, finite-to-infinite closure, RH.

Detailed post-green lead delta: `RESEARCH_LEADS_POST_122_DELTA.md`.

**RH remains OPEN.**