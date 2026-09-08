# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after PR #131 = 436d524d0cdeb5986d76dcbb988f771d19836c55
live main tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI are the exact authority. The control plane may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed internal route

```text
F1 finite canonical negative obstruction                              PROVED / #94
constrained algebra / Euclidean sector                                PROVED / #96-#98
exact centered N-flow + fixed-L negative tail                         PROVED / #100
reversal symmetry / parity geometry / algebraic D                     PROVED / #102-#103
global first bad + predecessor nonnegative + 1d successor shell       PROVED / #105,#112
negative first-bad eigenmode + KKT/cubic channel                      PROVED / #107,#109,#110
canonical V=W⊕S + shifted predecessor Schur reduction                 PROVED / #113
canonical cubic shell incidence                                       PROVED / #115
canonical cubic quotient coordinate + normalized Schur                PROVED / #118
exact quotient secular root <-> negative-shift eigenmode              PROVED / #119
exact explicit cubic Schur scalar bridge                              PROVED / #121
projected symmetry/coercivity + real resolvent metric control         PROVED / #122
zero-resonance cubic-coupling classification on ker A                 PROVED / #122
zero-shift kernel/range dichotomy + canonical endpoint                PROVED / #124-#125
exact one-dimensional zero-shift shell response                       PROVED / #127
signed regular response + canonical resonant kernel pole              PROVED / #128
source-explicit cubic defect + cross-parity secular transfer          PROVED / #129
off-line zero -> source-explicit global first-bad certificate         PROVED / #129
exact canonical source-moment decomposition                           PROVED / #131

E4-A4b regular-branch source test                                     NOW
E4-A4c resonant-branch source test                                    NEXT / PARALLEL
E4-B parity shifted-nullity comparison                                PARALLEL
E3-C resolvent monotonicity / root uniqueness                         PARALLEL
E3-B3 positive-floor deformation theorem                              PARALLEL / OPEN FORMALIZATION
negative-root exclusion                                               OPEN
explicit terminal RH bridge                                           OPEN
RH                                                                     OPEN
```

## Exact post-#131 finite state

A hypothetical off-line zero is reduced to one global-first-bad finite state carrying:

- a negative shift `lam<0`;
- both predecessor parity sectors nonnegative;
- canonical `V=W⊕S` with one-dimensional shell;
- canonical cubic shell vector `c!=0`;
- safe shifted predecessor resolvents;
- exact quotient scalar `F_p(lam)` and explicit real Schur scalar;
- exact root/eigenmode equivalence and metric bounds;
- `W=ker A⊕range A` for the projected predecessor block;
- the exact regular/resonant branch package;
- the #127 pure-shell response of the regular zero-shift image;
- the #128 canonical kernel coordinate and exact resonant `1/(-lam)` pole;
- the #129 source-explicit cross-parity certificate;
- the #131 exact pole/arch/prime decomposition of the canonical source moment.

The branch data remain:

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
  (-lam) K(R_lam b)=k
  K(R_lam b)=(-lam)^(-1) k
  plus the earlier pointwise kernel witness / identity / bound.
```

Across parity,

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

PR #131 now identifies the source term with

```text
explicitCanonicalSourceMoment
  = poleEven
    - reducedArchDiagonal
    - reducedArchOffDiagonal
    - finitePrimeAtomSum.
```

The index-independent archimedean scalar is annihilated by this observable, and the odd pole profile pairs to zero against every even boundary-flat input.

This is the strongest current finite rigidity/source-exposure package. It is not branch exclusion, negative-root exclusion or RH.

## Why the frontier moved from A4a to A4b

A4a is closed by #131. The production source formula is no longer opaque at the quadratic-normal interface.

The post-green reading also exposes a route constraint: `explicitCanonicalSourceMoment L K v` is linear in `v`. Therefore universal strict positivity/nonnegativity of the raw source moment over the whole even boundary-flat vector space cannot be the exclusion mechanism; `v -> -v` reverses it, and complex phase covariance gives the same warning more generally.

This does not rule out source-sensitive constraints on the canonically oriented first-bad secular trial vector. It redirects A4b toward a **compositional invariant** involving the source decomposition together with the canonical overlap / `Gamma`, root parity, and branch equations.

## Current execution priority

1. **E4-A4b-0 — source-expanded root interface.** Compose #131 directly into the #129 cross-parity/root theorems; theoremize linearity/negation/scalar covariance of the explicit source moment; isolate the elementary source-atom observable; theoremize its endpoint zeros at `omega=0,1`.
2. **E4-A4b — regular branch source test.** Combine `k=0`, `Re sigma0<0`, predecessor nonnegativity, overlap/source transfer and the explicit pole/arch/prime formula. Seek contradiction or a strictly smaller canonical regular class.
3. **E4-A4c — resonant branch source test.** Combine `k!=0`, the exact pole, predecessor nonnegativity, parity transfer and the same explicit source decomposition.
4. **E4-A4d — global first-bad exclusion.** Only after both actual canonical branches are excluded should the project theoremize no negative first-bad root.
5. **E4-B / E3-C / E3-B3** remain parallel only where they add information not already falsified by generic structural countermodels.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains a parallel cross-check.

## Post-#131 falsification rule

A proposed source inequality should be attacked first with:

- `v -> -v` and complex phase rotation;
- source moment zero, overlap zero, `Gamma=0`, `alpha=0`;
- the elementary atom at and near `omega=0,1`;
- the known post-#129 generic structural fixtures;
- diagonal compatibility if attempting to unify the arch off-diagonal channel with prime divided-difference atoms.

Generic countermodels remain **EXPERIMENTAL SIGNAL / regression fixtures**, not realizable zeta configurations and not counterexamples to the canonical CCM matrix.

## Control-v2 authority

`research/RHRC/control_v2/` remains additive research-control infrastructure only. It may rank actions, select first-break falsifiers, record archaeology/replay evidence and build fail-closed deformation-budget certificates. It may not write theorem authority, promote claims, change `BOUNDARY.json` terminal status or emit RH.

The control-plane anchor remains #117 because #118/#119/#121/#122/#124/#125/#127/#128/#129/#131 changed theorem state but not controller semantics.

## Permanent firewalls

- RH remains OPEN.
- shell nonzero is not shell invariance.
- the special theorem `T u0∈S` does not make `u0` an eigenvector.
- D is algebraic, not unitary/isometric.
- the predecessor correction in `D c+` may not be dropped.
- exact cubic factorization is rank at most one, not automatically exact rank one.
- predecessor nonnegative is not a positive spectral gap.
- `ker A` is the projected successor predecessor-block kernel, not the predecessor-size compressed-operator kernel.
- no `A^-1` at zero.
- `Re S0<0` and `Re sigma0<0` are not root exclusion.
- the exact resonant pole is not automatically contradictory.
- #129/#131 prove no useful sign/nonzeroness for `alpha`, `Gamma`, overlap or source moment.
- universal raw source-moment positivity is not a viable theorem target for this linear observable.
- no finite/fitted deformation tail is proof of complete future control.
- no source-normalization, promoted-binding, negative-root exclusion or RH change follows automatically from #127-#131.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_131_DELTA.md` — current post-green implications and falsification targets.
- `RESEARCH_LEADS_POST_129_DELTA.md` — historical predecessor delta.
- `RESEARCH_LEADS.md` — accumulated historical option memory.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — route failures requiring changed-premise justification before revival.
- `countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md` — structural falsification fixtures.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**