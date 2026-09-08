# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + ZERO-SHIFT BRANCH RESPONSE + SOURCE-EXPLICIT CROSS-PARITY TRANSFER + EXACT SOURCE DECOMPOSITION PROVED THROUGH PR #131; E4-A4b REGULAR SOURCE TEST CURRENT. RH OPEN.**

## Current authority split

```text
theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean/CI build closure remain authoritative.

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW fixed-L negative tail                                     PROVED / #100
PARITY reversal / displacement collapse                          PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry                 PROVED / #103
PARITY-BAD least bad size + predecessor nonnegative               PROVED / #105
FIRST-BAD-SPECTRUM compression + negative mode                    PROVED / #107
FIRST-BAD-RIGIDITY-A/B shell projection + KKT                     PROVED / #109
FIRST-BAD-RIGIDITY-C cubic parity defect finrank <=1              PROVED / #110
FIRST-BAD-RIGIDITY-D1 global first bad + W/S + exact cubic F      PROVED / #112
FIRST-BAD-RIGIDITY-D2 V=W⊕S + shifted inverse + Schur             PROVED / #113
FIRST-BAD-RIGIDITY-E1 cubic generator not inherited               PROVED / #115
FIRST-BAD-RIGIDITY-E2 canonical cubic quotient + normalized Schur PROVED / #118
FIRST-BAD-RIGIDITY-E3-A exact negative secular root iff eigenmode PROVED / #119
FIRST-BAD-RIGIDITY-E3-B2 exact explicit Schur scalar bridge       PROVED / #121
FIRST-BAD-RIGIDITY-E3-B1 projected metric/resolvent control       PROVED / #122
FIRST-BAD-RIGIDITY-E4-A1 ker(A) cubic-coupling classification     PROVED / #122
FIRST-BAD-RIGIDITY-E4-A2 kernel/range zero-shift dichotomy        PROVED / #124
FIRST-BAD-RIGIDITY-E4-A2 canonical endpoint + complete square     PROVED / #125
FIRST-BAD-RIGIDITY-E4-A3a canonical zero-shift shell response     PROVED / #127
FIRST-BAD-RIGIDITY-E4-A3b signed response + canonical kernel pole PROVED / #128
FIRST-BAD-RIGIDITY-E4-A3c source-explicit parity transfer         PROVED / #129
off-line zero -> source-explicit first-bad certificate            PROVED / #129
FIRST-BAD-RIGIDITY-E4-A4a exact source-moment decomposition       PROVED / #131
```

## Exact post-#131 first-bad state

A hypothetical off-critical-line zeta zero forces one finite problem with:

- positive aperture `L`;
- global least-bad successor size;
- both predecessor parity sectors nonnegative;
- a genuine negative parity-compressed eigenvalue `lam<0`;
- intrinsic successor decomposition `V=W⊕S`, `dim_C S=1`;
- canonical cubic shell vector `c!=0`;
- canonical quotient coordinate on `V/W`;
- safe shifted predecessor inverse `R_lam=(A-lam I)^(-1)`;
- exact quotient and explicit real Schur scalar root;
- exact kernel/range split `W=ker A⊕range A`;
- exact regular/resonant zero-shift classification;
- exact #127 shell response;
- exact #128 canonical kernel pole;
- exact #129 source-explicit parity transfer;
- exact #131 decomposition of the source moment into pole-even, reduced arch diagonal, reduced arch off-diagonal and finite prime-atom channels.

The branch package remains:

```text
REGULAR:
  Ax0=b
  S0=<Tc,c>-<x0,b>
  u0=-x0+c
  sigma0*c = T u0
  S0=star(sigma0)<c,c>
  Re S0<0
  Re sigma0<0
  k=K(b)=0

RESONANT:
  k=K(b)!=0
  (-lam)K(R_lam b)=k
  K(R_lam b)=(-lam)^(-1)k
  plus the #124 pointwise witness / identity / bound.
```

Across parity,

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

PR #131 theoremizes

```text
sourceMoment(v) = explicitCanonicalSourceMoment(v)
```

with

```text
explicitCanonicalSourceMoment
  = poleEven
    - reducedArchDiagonal
    - reducedArchOffDiagonal
    - finitePrimeAtomSum.
```

The index-independent archimedean scalar is annihilated by the quadratic-normal observable. The pole odd profile pairs to zero against the even boundary-flat sector. No branch is excluded.

## E4-A4a settlement

**PROVED / #131.**

The source-opacity obligation is closed:

- `canonicalSourceMatrix = pole - canonicalArch - prime` is theoremized;
- the corrected direct Eq. 4.4 archimedean channel is reduced by removing the index-independent scalar;
- the active observable annihilates that scalar identity exactly;
- the reduced arch channel splits into diagonal and off-diagonal matrices;
- the prime channel is a finite von-Mangoldt weighted sum of elementary `sourceMatrix` atoms;
- the pole channel has an exact rank-two even/odd profile factorization;
- the odd pole profile cancels on even boundary-flat input;
- the #129 cubic defect equals the exact explicit source moment.

This is decomposition, not a sign theorem.

## Current route state — E4-A4b regular-branch source test

### A4b-0 — source-expanded root interface

**OPEN / PRIMARY.**

Compose #131 directly into the #129 transfer theorems so that the root interface is stated with `explicitCanonicalSourceMoment` rather than the opaque `sourceMoment` alias.

The first theorem tranche should also formalize linearity/negation/scalar covariance of the explicit moment and isolate

```text
omega -> quadraticNormalMatrixMoment K (sourceMatrix omega K) v.
```

The existing endpoint identities imply this elementary observable vanishes at `omega=0` and `omega=1`; theoremize those endpoints before attempting a global inequality.

### A4b — regular branch source test

**OPEN / CURRENT.**

Use

```text
k=0
Re sigma0<0
F_- = alpha F_+ + Gamma explicitCanonicalSourceMoment(u_+)
```

plus predecessor nonnegativity and the actual source formula. The objective is either a contradiction or a strictly smaller canonical regular class.

Do not seek universal positivity of the raw source moment on the whole vector space: the observable is linear in `v`, so `v -> -v` reverses it. The useful object must be the canonically composed source/overlap quantity or another orientation-sensitive invariant.

### A4c — resonant branch source test

**OPEN / NEXT.**

Use

```text
k!=0
(-lam)K(R_lam b)=k
F_- = alpha F_+ + Gamma explicitCanonicalSourceMoment(u_+)
```

plus predecessor nonnegativity and actual source values.

The exact pole is classification, not contradiction.

### A4d — global first-bad exclusion

**OPEN.**

Only after both canonical branches are excluded should the route theoremize no negative global first-bad root. The existing ExceptionalZero reduction already starts from an arbitrary off-line zero; a final explicit bridge to the terminal Mathlib `RiemannHypothesis` statement would still be required.

## Post-#131 falsification rule

Before theoremizing a source inequality:

- test `v -> -v` and complex phase rotation;
- test source moment zero, overlap zero, `Gamma=0`, `alpha=0`;
- test the elementary source atom at and near `omega=0,1`;
- if combining arch off-diagonal and prime terms through divided differences, prove diagonal compatibility separately;
- rerun the post-#129 structural countermodels to confirm the argument really spends canonical source values.

The structural fixtures remain **EXPERIMENTAL SIGNAL / synthetic falsification fixtures**, not canonical CCM counterexamples.

## E4-B — parity shifted-nullity

**OPEN / PARALLEL.** Use algebraic D-equivalence and finrank-at-most-one defect only. Do not import unitary interlacing through D.

## E3-C — monotonicity / root-count control

**OPEN / PARALLEL.** A shifted-resolvent identity may yield strict monotonicity and at most one negative root.

```text
at most one negative root != no negative root.
```

## E3-B3 — general predecessor-floor theorem

**LEAD / OPEN FORMALIZATION.** Under `mu ||w||^2 <= Re <Aw,w>` and `lam<mu`, prove the denominator `mu-lam` resolvent estimate and derive `d_N(g_N+d_N) <= beta_N^2`. The shortcut `d_N<=beta_N^2/g_N` requires separately proved `g_N>0`.

## Source-faithful parallel lane

The independent source-faithful lane remains

```text
G1-B1B -> G1-final -> S-NEG -> G23.
```

Do not conflate source interface geometry with source negativity.

## Permanent normalization / model firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix` under the repaired source convention;
- legacy printed `finiteMatrix` differs by a scalar identity, so absolute eigenvalue/PSD/inertia claims do not transfer automatically;
- generic R002 smooth taper-grid is not the canonical CCM family except at exact specialization;
- Bombieri zero-height truncations are distinct from deterministic CCM Fourier-mode truncations;
- boundary-flat legality is required for the hard-window C² bridge;
- `ker A` is not the predecessor-size compressed-operator kernel;
- no `A^-1` at zero;
- `Re S0<0` and `Re sigma0<0` are not branch exclusion;
- the exact resonant pole is not automatically contradictory;
- D is algebraic, not unitary/isometric;
- the predecessor correction in `D c+` may not be dropped;
- #129/#131 prove no useful sign/nonzeroness for `alpha`, `Gamma`, overlap or source moment;
- universal raw source-moment positivity is not compatible with this linear observable;
- generic structural countermodels do not refute `canonicalSourceMatrix`;
- root uniqueness is not root exclusion;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_131_DELTA.md`.

**RH remains OPEN.**