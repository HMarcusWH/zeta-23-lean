# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after PR #129 = e1192857afed9f68fa4a13143ce690b62191b997
live main tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7

theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
validated theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

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

E4-A4 canonical-source branch exclusion                               NOW
E4-B parity shifted-nullity comparison                                PARALLEL
E3-C resolvent monotonicity / root uniqueness                         PARALLEL
E3-B3 positive-floor deformation theorem                              PARALLEL / OPEN FORMALIZATION
negative-root exclusion                                               OPEN
explicit terminal RH bridge                                           OPEN
RH                                                                     OPEN
```

## Exact post-#129 finite state

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
- the #129 source-explicit parity certificate.

The branch data are now:

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

Across parity, with `u_+` the canonical even trial vector and `sourceMoment` the #129 canonical quadratic source moment,

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

`Gamma` has an exact odd trial/cubic overlap representation. If the forced root is even, `F_+=0` and the odd scalar is the exact overlap-times-source product. If the forced root is odd, `F_-=0` and the full balance is retained without division.

This is the strongest current finite rigidity/source-exposure package. It is not branch exclusion, negative-root exclusion or RH.

## Why the frontier moved to E4-A4

The post-#128 falsification pass constructed generic and centered-grid structural countermodels that retain the relevant Schur/shell/resonance/parity/KKT/displacement geometry while still admitting a bad successor state. Therefore the project should not spend another theorem tranche proving a contradiction from generic block structure alone.

PR #129 exposes the first clearly source-specific scalar in the active parity route:

```text
evenQuadraticSourceMoment L K v
  = <n2, canonicalSourceMatrix(L,K) v> / <n2,n2>
  = cubicDefectFunctional L K v.
```

The next theorem must use the actual `canonicalSourceMatrix` formula, not merely its Hermitianity, parity, displacement rank or abstract block decomposition.

## Current execution priority

1. **E4-A4a — source moment decomposition.** Expand the production `canonicalSourceMatrix` inside the #129 source moment and theoremize exact cancellations/channel decomposition before attempting inequalities.
2. **E4-A4b — regular branch source test.** Combine `k=0`, `Re sigma0<0`, cross-parity transfer and the source moment to seek a canonical-source incompatibility. Do not assume any factor nonzero.
3. **E4-A4c — resonant branch source test.** Combine `k!=0`, the exact pole, parity transfer and the source moment. Test whether the actual source formula can support the resonant state.
4. **E4-A4d — global first-bad exclusion.** Only after both branches are excluded should the project theoremize no canonical first-bad negative root.
5. **E4-B / E3-C / E3-B3** remain parallel only where they add information not already falsified by generic structural countermodels.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains a parallel cross-check.

## Post-#129 falsification rule

A proposed root-exclusion theorem should be attacked against the known structural fixtures first.

If the argument also excludes arbitrary reversal-symmetric diagonal perturbations preserving the displacement identity, then either:

- the proof has found a genuinely stronger invariant not represented in those fixtures; or
- it is silently using an assumption that must be identified.

Generic countermodels are **EXPERIMENTAL SIGNAL / regression fixtures**, not realizable zeta configurations and not counterexamples to the canonical CCM matrix.

## Control-v2 authority

`research/RHRC/control_v2/` remains additive research-control infrastructure only. It may rank actions, select first-break falsifiers, record archaeology/replay evidence and build fail-closed deformation-budget certificates. It may not write theorem authority, promote claims, change `BOUNDARY.json` terminal status or emit RH.

The control-plane anchor remains #117 because #118/#119/#121/#122/#124/#125/#127/#128/#129 changed theorem state but not controller semantics.

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
- #129 proves no useful sign/nonzeroness for `alpha`, `Gamma`, overlap or source moment.
- no finite/fitted deformation tail is proof of complete future control.
- no source-normalization, promoted-binding, negative-root exclusion or RH change follows automatically from #127-#129.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_129_DELTA.md` — current post-green implications and falsification targets.
- `RESEARCH_LEADS.md` — accumulated historical option memory; newer deltas supersede stale per-entry currentness.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — route failures requiring changed-premise justification before revival.
- `countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md` — post-#128/#129 falsification fixtures.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**