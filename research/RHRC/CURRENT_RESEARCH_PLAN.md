# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
theorem tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
theorem-bearing merged through = PR #125
E4-A2 zero-shift kernel/range dichotomy + strict regular endpoint = PROVED / MERGED

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
  E4-A2 range/kernel direct sum + decoupled zero-shift solve / #124
  E4-A2 exact resonant identity + denominator-free bound / #124
  E4-A2 canonical zero-shift endpoint + complete square / #125
  E4-A2 decoupled branch at negative secular root -> Re S0<0 / #125

NOW — E4-A3: BRANCH RIGIDITY
  A3a ZERO-SHIFT SHELL RESPONSE
    theoremize T u0 ∈ S from the proved zero predecessor coordinate
    use dim_C S=1 and the canonical cubic coordinate to obtain the exact shell coefficient
    identify the one-dimensional response encoded by S0
    do not promote this to an eigenvector theorem

  A3b RESONANT POLE DECOMPOSITION
    use W=ker A⊕range A to split b=bK+bR
    theoremize the exact kernel contribution to R_lam b
    isolate the 1/(-lam) pole coefficient without heuristic spectral language

  A3c BRANCH RIGIDITY / COUNTERMODEL ATTACK
    compose A3a/A3b with parity rank-at-most-one structure
    compose with KKT / parity normal-space geometry
    compose with canonical cubic quotient data
    compose with exact N-flow and global-first-bad minimality
    attempt to exclude one or both branches, or shrink the surviving finite countermodel class

PARALLEL — E4-B: PARITY SHIFTED-NULLITY
  use finrank-at-most-one defect + algebraic D-equivalence
  theoremize shifted-nullity difference without unitary assumptions
  use only where it constrains the E4-A3 branch state

PARALLEL — E3-C: RESOLVENT IDENTITY / MONOTONICITY
  prove finite-dimensional shifted resolvent identity
  exploit the exact real scalar representation
  prove strict monotonicity on lam<0 if justified
  derive at most one negative root / negative-index control
  never confuse uniqueness with absence

PARALLEL — E3-B3: GENERAL LOWER-FLOOR DEFORMATION THEOREM
  under mu ||w||^2 <= Re<Aw,w> and lam<mu,
  prove the mu-lam resolvent bound
  theoremize q_N, beta_N and d_N(g_N+d_N) <= beta_N^2
  use d_N <= beta_N^2/g_N only after independent g_N>0

TARGET
  CCM-specific negative-root exclusion at the global first-bad state
  positivity / finite-to-infinite closure remains open until separately proved

PARALLEL DIAGNOSTIC
  probe g_N=q_N-mu_N, beta_N, beta_N^2/g_N
  no PRUNE without a complete assured infinite-tail certificate

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
```

## What #124/#125 made possible

Let

```text
A = intrinsicPredecessorBlock = P_W T|_W
c = intrinsicCubicShellPart
b = intrinsicShellToPredecessor c.
```

PR #124 closes the range/kernel infrastructure:

```text
range A ⟂ ker A
W=ker A⊕range A.
```

It turns the E4-A1 coupling split into an exact zero-shift dichotomy. In the decoupled branch:

```text
b ∈ range A
∃x0, Ax0=b
Ax=b and Ay=b -> <x,b>=<y,b>.
```

In the resonant branch:

```text
Az=0
<z,b>!=0
<z,b>=(-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

PR #125 then defines

```text
S0=<Tc,c>-<x0,b>
u0=-x0+c
```

and proves:

```text
predecessorPart(Tu0)=0
<Tu0,u0>=S0
exact predecessor-fibre complete square
Re S0<0 at the safe negative explicit secular root.
```

The old E4-A2 endpoint existence/sign problem is therefore closed. The new problem is whether the full CCM structure can tolerate either remaining branch.

## Why E4-A3 is the immediate next layer

### Regular branch

The regular branch already has a strictly negative canonical endpoint. Generic Hermitian Schur systems can do this, so negativity alone is not a contradiction.

The highest-information refinement is one-dimensional shell response. Since #125 proves the predecessor coordinate of `T u0` is zero and `V=W⊕S`, theoremize `T u0∈S`; then use the canonical cubic coordinate on the one-dimensional shell to identify the exact response coefficient. This creates a scalar object that can be compared to parity/KKT/N-flow structure.

### Resonant branch

#124 already proves a quantitative lower bound. The next useful theorem is stronger and more structural: decompose the coupling under `ker A⊕range A` and isolate the exact pole of `R_lam b`. This distinguishes finite regular response from genuine zero-mode resonance algebraically.

### Branch rigidity

The project should then attack the finite counterexample space, not RH by slogan. Ask whether a finite system satisfying all of:

```text
A>=0
negative explicit secular root
strict regular endpoint OR exact resonance
rank-at-most-one parity defect
KKT/cubic constraints
first-bad N-flow ancestry
```

can still exist.

## E3-C monotonicity lane

The exact root detector is already theorem-identified with a real explicit scalar. Strict monotonicity may yield:

```text
S has at most one negative root.
```

Permanent firewall: this does not exclude that one root. Because a hypothetical off-line zero already forces a negative root, E3-C is supportive rather than the primary exclusion mechanism.

## Quantitative deformation composition

The #122 `mu=0` root metric bound remains theorem-backed. The reusable generalization remains:

```text
mu ||w||^2 <= Re <Aw,w>
lam < mu
R_lam=(A-lam I)^(-1)
```

implying the expected `mu-lam` resolvent estimate and the normalized one-step inequality

```text
d_N(g_N+d_N) <= beta_N^2.
```

The shortcut `d_N <= beta_N^2/g_N` requires independently certified `g_N>0`.

Do not let this lane displace E4-A3 unless it produces independent information about branch exclusion.

## Falsification gates

- generic block systems with `A>=0` can have negative zero-shift Schur complement; `Re S0<0` is not contradiction;
- generic zero resonance can generate negative spectrum; the resonant branch is not automatically impossible;
- `T u0∈S` does not imply `u0` is an eigenvector;
- `ker A` is not the predecessor-size compressed-operator kernel;
- monotonicity gives uniqueness, not absence;
- D remains algebraic, not unitary/isometric;
- do not use successor positivity to prove endpoint nonnegativity at the first-bad state;
- no finite prefix, fitted tail or observed decay is an infinite-horizon certificate.

## Permanent claim boundary

**PROVED:** through PR #125, including exact real secular representation, projected metric/resolvent bounds, E4-A1 coupling classification, E4-A2 range/kernel split, zero-shift solution canonicity, exact resonant identity/bound, canonical zero-shift endpoint, complete-square identity and strict `Re S0<0` in the decoupled first-bad branch.

**DERIVED / OPEN FORMALIZATION:** `T u0∈S` and a canonical shell-response coefficient; generic rank-one shifted-nullity comparison.

**LEAD / HYPOTHESIS:** exact resonant pole decomposition, branch exclusion from parity/KKT/N-flow composition, strict secular monotonicity/root uniqueness, positive-floor deformation budget.

**OPEN:** exclusion of the regular branch, exclusion of the resonant branch, negative-root exclusion, positivity, finite-to-infinite closure, RH.

Detailed post-green lead delta: `RESEARCH_LEADS_POST_125_DELTA.md`.

**RH remains OPEN.**