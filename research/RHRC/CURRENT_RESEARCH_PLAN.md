# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
theorem-bearing merged through = PR #129
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

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
  E4-A3a canonical zero-shift shell response / #127
  E4-A3b regular Re sigma0<0 + canonical resonant kernel pole / #128
  E4-A3c exact cross-parity secular transfer / #129
  E4-A3c cubic defect = canonical quadratic source moment / #129
  off-line zero -> source-explicit global first-bad certificate / #129

NOW — E4-A4: CANONICAL-SOURCE BRANCH EXCLUSION

  A4a SOURCE MOMENT DECOMPOSITION
    expand the actual production canonicalSourceMatrix inside
      <n2, M u+>/<n2,n2>
    identify exact prime/arch/diagonal contributions and cancellations
    theoremize the exact decomposition before any inequality

  A4b REGULAR-BRANCH SOURCE TEST
    combine
      k=0
      Re sigma0<0
      F_- = alpha F_+ + Gamma sourceMoment(u+)
    with actual source structure
    seek contradiction or a sharply smaller canonical regular class
    do not assume alpha/Gamma/sourceMoment nonzero or sign-controlled

  A4c RESONANT-BRANCH SOURCE TEST
    combine
      k!=0
      (-lam) K(R_lam b)=k
      F_- = alpha F_+ + Gamma sourceMoment(u+)
    with actual source structure and predecessor nonnegativity
    seek contradiction or a sharply smaller canonical resonant class

  A4d GLOBAL FIRST-BAD EXCLUSION
    exclude both actual canonical branches
    theoremize absence of a negative first-bad root
    then compose with the existing off-line-zero -> first-bad reduction

PARALLEL — E4-B: PARITY SHIFTED-NULLITY
  use finrank-at-most-one defect + algebraic D-equivalence
  theoremize shifted-nullity difference without unitary assumptions
  activate only if it constrains A4 source-sensitive branch analysis

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
  do not let this displace A4 unless it adds source-sensitive exclusion data

PARALLEL DIAGNOSTIC
  probe g_N=q_N-mu_N, beta_N, beta_N^2/g_N
  no PRUNE without a complete assured infinite-tail certificate

PARALLEL SOURCE CROSS-CHECK
  G1-B1B -> G1-final -> S-NEG -> G23

TARGET
  canonical first-bad negative-root exclusion
  -> no off-line zero via existing global reduction
  -> explicit final bridge to Mathlib RiemannHypothesis
  RH OPEN
```

## What #127-#129 made possible

Let

```text
A = intrinsicPredecessorBlock = P_W T|_W
c = intrinsicCubicShellPart
b = intrinsicShellToPredecessor c
u0 = -x0+c
```

PR #127 closes the special zero-shift shell response:

```text
T u0 = shellPart(T u0)
sigma0*c = T u0
S0 = star(sigma0)<c,c>.
```

PR #128 closes the next branch-response layer:

```text
REGULAR: Re sigma0<0 and k=K(b)=0
RESONANT: k=K(b)!=0 and (-lam)K(R_lam b)=k.
```

The divided pole follows only because `lam<0`; the denominator-free identity is primary.

PR #129 then identifies the parity-defect coefficient with the actual canonical source moment and proves exact parity transfer:

```text
cubicDefectFunctional L K v
  = evenQuadraticSourceMoment L K v
  = <n2, canonicalSourceMatrix(L,K)v>/<n2,n2>

F_- = alpha F_+ + Gamma sourceMoment(u_+).
```

The `Gamma` coefficient has an exact odd trial/cubic overlap representation. At an even root the odd scalar is exactly overlap times source moment. At an odd root the full balance is retained without division.

The old E4-A3 construction problem is therefore closed. The new question is not how to expose the branch response. It is whether the **actual canonical source formula** can support either exposed branch.

## Why E4-A4 is the immediate next layer

### Generic structure has been adversarially tested

The post-#128 discovery pass found generic Hermitian and centered-grid diagonal models that preserve increasingly much of the structural package while retaining bad successor behavior. These include:

- a regular 2x2 Schur countermodel with nonnegative predecessor and negative endpoint;
- a resonant 2x2 countermodel with exact zero-mode coupling;
- centered radius-3 diagonal models with both regular responses negative;
- a centered model with only one parity bad;
- a genuine centered odd resonance with zero successor kernels;
- reversal-symmetric diagonal perturbations that preserve the displacement identity while changing the sign-sensitive first-bad state.

These are **EXPERIMENTAL SIGNAL / regression fixtures**, not Lean theorems and not zeta counterexamples.

Their implication is methodological: parity/KKT/rank-one/displacement/first-bad structure alone is insufficient. A valid contradiction must spend information specific to the actual canonical source values.

### A4a is the cheapest decisive theorem

PR #129 has already exposed exactly where the source enters. Before attempting a sign theorem, expand

```text
evenQuadraticSourceMoment L (N+1) uPlus
```

through the production definition of `canonicalSourceMatrix`. The first useful result may be an exact identity rather than an inequality: cancellation of constant normal contributions, isolation of the canonical diagonal term, or a prime/arch split aligned with `n2`.

This has high falsification value: if the source moment remains sign-indefinite on legal first-bad data, we learn immediately that A4b needs a more compositional invariant.

## Regular branch target

The regular branch already carries

```text
Ax0=b
k=0
Re sigma0<0
Re S0<0
```

plus the #129 parity transfer. A source-specific exclusion theorem must show that the actual `canonicalSourceMatrix` cannot realize that package at a first-bad root.

A transparent sufficient certificate would resemble block positivity,

```text
q_c >= 0
|<w,b>|^2 <= q_c q_A(w)
```

but this is essentially one-step positivity and is not progress if merely assumed. Any useful theorem must derive its content from the canonical source formula.

## Resonant branch target

The resonant branch carries a canonical nonzero kernel coordinate and exact pole. The next useful theorem should ask whether the actual source moment / parity transfer forces a vanishing or incompatible overlap on that same state.

Do not replace the projected predecessor kernel with the predecessor-size compressed spectrum. Do not infer contradiction from the pole alone.

## Falsification gates

- re-run any proposed generic inequality on the post-#129 structural countermodels;
- if an argument excludes arbitrary reversal-symmetric diagonal perturbations, identify the stronger invariant it is actually using;
- test boundary cases `N=1`, source-moment zero, overlap zero, `Gamma=0`, `alpha=0`;
- never divide by a factor unless nonzeroness is separately theoremized;
- preserve the predecessor correction in `D c+`;
- do not use D as an isometry;
- do not use successor positivity at the first-bad state;
- monotonicity gives uniqueness, not absence;
- no finite prefix or fitted tail is an infinite-horizon certificate.

## Permanent claim boundary

**PROVED:** through PR #129, including exact zero-shift shell response, signed regular response, canonical resonant kernel pole, source-explicit cubic-defect identity, exact cross-parity secular transfer, overlap representation, even-root source-product specialization, and the global off-line-zero source-explicit first-bad wrapper.

**DERIVED:** the source moment is the exact surviving quadratic normal coefficient in the canonical even compression residual; at a forced even root, the same-lambda odd root condition reduces to vanishing of the overlap-times-source product. These consequences should not be promoted beyond their theorem hypotheses.

**LEAD / HYPOTHESIS:** source-moment decomposition through prime/arch/diagonal channels; regular-branch source exclusion; resonant-branch source exclusion; strict secular monotonicity; positive-floor deformation budget.

**EXPERIMENTAL SIGNAL:** the post-#128/#129 structural countermodels and exact rational transfer checks.

**OPEN:** useful sign/nonzeroness of source moment/overlap/Gamma; exclusion of regular branch; exclusion of resonant branch; negative-root exclusion; explicit terminal RH bridge; RH.

Detailed post-green lead delta: `RESEARCH_LEADS_POST_129_DELTA.md`.

**RH remains OPEN.**