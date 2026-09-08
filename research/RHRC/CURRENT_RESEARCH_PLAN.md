# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
theorem-bearing merged through = PR #131
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

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
  E4-A4a exact canonical source-moment decomposition / #131
  E4-A4a arch scalar cancellation + arch diagonal/off-diagonal split / #131
  E4-A4a finite von-Mangoldt prime atomization / #131
  E4-A4a pole even/odd factorization + odd-profile cancellation / #131

NOW — E4-A4b: REGULAR-BRANCH SOURCE TEST

  A4b-0 SOURCE-EXPANDED ROOT INTERFACE
    compose #131 directly into the #129 cross-parity secular equations
    theoremize linearity / negation / scalar covariance of the explicit source moment
    isolate the one-parameter elementary source-atom observable
    theoremize its exact endpoint zeros at omega=0 and omega=1
    do not attempt a universal raw sign theorem on the full vector space

  A4b REGULAR-BRANCH SOURCE TEST
    combine
      k=0
      Re sigma0<0
      predecessor nonnegativity
      F_- = alpha F_+ + Gamma explicitSourceMoment(u+)
    with the actual pole/arch/prime formula
    seek contradiction or a sharply smaller canonical regular class
    target the compositional quantity entering parity transfer, not sourceMoment in isolation
    do not assume alpha/Gamma/overlap/sourceMoment nonzero or sign-controlled

  A4c RESONANT-BRANCH SOURCE TEST
    combine
      k!=0
      (-lam) K(R_lam b)=k
      predecessor nonnegativity
      F_- = alpha F_+ + Gamma explicitSourceMoment(u+)
    with the same actual source formula
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

## What #127-#131 made possible

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

PR #129 identifies the parity-defect coefficient with the actual canonical source moment and proves exact parity transfer:

```text
cubicDefectFunctional L K v
  = evenQuadraticSourceMoment L K v
  = <n2, canonicalSourceMatrix(L,K)v>/<n2,n2>

F_- = alpha F_+ + Gamma sourceMoment(u_+).
```

PR #131 then opens that source moment completely:

```text
cubicDefectFunctional L K v
  = explicitCanonicalSourceMoment L K v
```

where the right-hand side is exactly

```text
one surviving pole-even profile term
- reduced arch diagonal moment
- reduced arch off-diagonal moment
- finite von-Mangoldt weighted elementary sourceMatrix moments.
```

The index-independent canonical archimedean scalar cancels from the active observable, and the pole odd profile annihilates the even boundary-flat input.

The old A4a source-opacity problem is therefore closed. The new question is which property of this **actual pole/arch/prime combination, composed with the canonical parity overlap and branch data**, excludes the regular or resonant state.

## Why A4b is the immediate next layer

### Generic structure has been adversarially tested

The post-#128 discovery pass found generic Hermitian and centered-grid diagonal models that preserve increasingly much of the structural package while retaining bad successor behavior. These are **EXPERIMENTAL SIGNAL / regression fixtures**, not Lean theorems and not zeta counterexamples.

Their implication remains methodological: parity/KKT/rank-one/displacement/first-bad structure alone is insufficient. A valid contradiction must spend information specific to the actual canonical source values.

### #131 falsifies the naive universal-sign target

The explicit source moment is linear in the trial vector. Therefore a universal theorem asserting strict positivity or nonnegativity of the raw moment on the entire even boundary-flat vector space cannot be the A4b mechanism: `v -> -v` reverses the value, and complex phase covariance strengthens the same obstruction.

This does not rule out a sign/phase/nonvanishing statement for the canonically oriented trial vector after composition with overlap, `Gamma`, root parity, or branch equations. It means the useful invariant must be compositional.

### A4b-0 is the cheapest next theorem

Before guessing a difficult inequality, theoremize the exact post-#131 root interface:

```text
F_- = alpha F_+ + Gamma explicitCanonicalSourceMoment(u_+).
```

At an even root, replace the source term in the exact overlap-times-source product by the explicit pole/arch/prime decomposition. Then isolate the elementary source atom

```text
omega -> quadraticNormalMatrixMoment K (sourceMatrix omega K) v.
```

The existing endpoint identities `sourceMatrix 0 = 0` and `sourceMatrix 1 = 2 I`, together with scalar-identity annihilation of the quadratic-normal observable, imply endpoint zeros. The next useful theorem may be a factorization or shape constraint rather than a global sign theorem.

## Regular branch target

The regular branch carries

```text
Ax0=b
k=0
Re sigma0<0
Re S0<0
```

plus exact #129/#131 source-expanded parity transfer. A source-specific exclusion theorem must show that the actual pole/arch/prime formula cannot realize that package at a first-bad root.

A transparent sufficient certificate resembling one-step positivity is not progress if merely assumed. Any useful theorem must derive its content from the canonical source formula.

## Resonant branch target

The resonant branch carries a canonical nonzero kernel coordinate and exact pole. The next useful theorem should ask whether the explicit source decomposition / parity transfer forces a vanishing or incompatible overlap on that same state.

Do not replace the projected predecessor kernel with the predecessor-size compressed spectrum. Do not infer contradiction from the pole alone.

## Falsification gates

- test `v -> -v` and complex phase rotation before proposing source-moment sign claims;
- test boundary cases `N=1`, source-moment zero, overlap zero, `Gamma=0`, `alpha=0`;
- test the elementary source observable at and near `omega=0,1`;
- if combining arch off-diagonal and prime atoms through divided differences, verify diagonal compatibility separately;
- re-run any proposed generic inequality on the post-#129 structural countermodels;
- never divide by a factor unless nonzeroness is separately theoremized;
- preserve the predecessor correction in `D c+`;
- do not use D as an isometry;
- do not use successor positivity at the first-bad state;
- monotonicity gives uniqueness, not absence;
- no finite prefix or fitted tail is an infinite-horizon certificate.

## Permanent claim boundary

**PROVED:** through PR #131, including exact zero-shift shell response, signed regular response, canonical resonant kernel pole, source-explicit cubic-defect identity, exact cross-parity secular transfer, global off-line-zero source-explicit first-bad wrapper, and exact canonical source-moment decomposition into pole-even / reduced arch diagonal / reduced arch off-diagonal / finite prime-atom channels.

**DERIVED:** the explicit source moment is linear in the trial vector; raw universal positivity on the whole vector space is not a viable route; the elementary source observable vanishes at `omega=0` and `omega=1` by the existing endpoint matrix identities plus scalar-identity annihilation.

**LEAD / HYPOTHESIS:** source-expanded root-interface theorem package; compositional overlap-times-source invariant; elementary source-atom factorization/shape theorem; regular-branch source exclusion; resonant-branch source exclusion; potential-level arch/prime unification; strict secular monotonicity; positive-floor deformation budget.

**EXPERIMENTAL SIGNAL:** the post-#128/#129 structural countermodels and exact rational transfer checks.

**OPEN:** useful sign/nonzeroness of the canonically composed source/overlap quantity; exclusion of regular branch; exclusion of resonant branch; negative-root exclusion; explicit terminal RH bridge; RH.

Detailed current post-green delta: `RESEARCH_LEADS_POST_131_DELTA.md`.

**RH remains OPEN.**