# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after PR #119 = d4175d2bb305e62863f593824b3f40e921a46ee6
live main tree = 1985472ac470822af279044261fa365fb9bb5535

theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
FIRST-BAD-RIGIDITY-E3-A exact secular equivalence = PROVED / MERGED

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
reversal symmetry / even commutator collapse                          PROVED / #102
direct parity geometry + algebraic D-equivalence                      PROVED / #103
least/global bad + predecessor nonnegative + 1d successor shell       PROVED / #105,#112
negative first-bad eigenmode + noninheritance                         PROVED / #107
nonzero shell projection + exact parity normals/KKT                   PROVED / #109
cubic parity channel + compressed defect finrank <=1                  PROVED / #110
intrinsic W/S block + exact cubic factorization                       PROVED / #112
canonical V=W⊕S + shifted predecessor Schur reduction                 PROVED / #113
canonical cubic shell incidence                                       PROVED / #115
canonical cubic shell/quotient coordinate + normalized Schur          PROVED / #118
exact canonical secular root <-> negative-shift eigenmode             PROVED / #119

e3-B projected symmetry / coercivity / explicit scalar bridge         NEXT
e4 parity shifted-nullity / zero-resonance classification             PARALLEL / NEXT
quantitative one-step deformation theorem                              LEAD / OPEN FORMALIZATION
resolvent monotonicity / negative-root uniqueness                      OPEN
negative-root exclusion                                                OPEN
positivity / finite-to-infinite closure                                OPEN
RH                                                                       OPEN
```

## What #119 gives the controller

The current finite obstruction is no longer merely

```text
negative eigenmode -> Schur identity.
```

For each safe negative shift `lam<0`, the repository constructs a canonical trial vector and residual and proves

```text
cubicSecularScalar(lam)=0
  <-> exists nonzero v with T v = lam v.
```

A hypothetical off-line zero therefore forces a global-first-bad state with an exact negative secular root.

This is the new theorem frontier consumed by research-control routing.

## Critical representation firewall

`cubicSecularScalar` in PR #119 is the canonical cubic quotient coordinate of the full residual. The #113/#118 expression

```text
<Tc,c> - lam<c,c> - <R_lam Bc,Bc>
```

is not yet theorem-identified pointwise with the #119 scalar for all safe negative shifts.

Therefore the next theorem action must establish the **metric bridge** before the controller treats sign or monotonicity of the explicit Schur expression as sign or monotonicity of `cubicSecularScalar`.

## Current execution priority

1. **E3-B1 — projected symmetry / shifted coercivity.** Prove native symmetry of `intrinsicPredecessorBlock`, quantitative coercivity of `A-lam I`, and safe resolvent norm/positivity bounds.
2. **E3-B2 — explicit secular bridge.** Prove the exact pointwise equality between the #119 quotient scalar and the normalized explicit Schur scalar, respecting Mathlib's complex-inner-product convention.
3. **E4-A — parity nullity / zero resonance.** Theoremize the rank-at-most-one shifted-nullity consequence and determine how `Bc` interacts with `ker A`.
4. **E3-B3 — quantitative predecessor-floor deformation bound.** Use a certified lower spectral floor `mu` to prove the theorem-backed one-step inequality if the exact hypotheses close.
5. **E3-C — resolvent identity / monotonicity / root uniqueness.** Attempt only after the scalar bridge and zero-resonance behavior are under control.
6. **Root exclusion.** Uniqueness is not absence; any contradiction must use additional CCM-specific shell/parity/KKT/N-flow structure.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains parallel.

## Deformation-budget lane

Control-v2 may continue to falsify the candidate route numerically using

```text
g_N = q_N-mu_N
beta_N
beta_N^2/g_N
```

but the diagnostic lane must follow the theorem lane's definitions and hypothesis boundaries.

The expected theorem-backed composition is

```text
E3-B metric bridge
  -> certified predecessor-floor resolvent estimate
  -> d_N(g_N+d_N) <= beta_N^2
  -> d_N <= beta_N^2/g_N only when g_N>0 is separately certified.
```

A finite prefix, fitted tail, local residual or observed decay is never an infinite-tail certificate. Decision-bearing reduced calculations still require the hardened Control-v2 assurance rules.

## Zero-resonance first break

Global-first-bad gives `A>=0`, not `A>0`. Consequently a zero eigenvalue of the predecessor block can make the shifted resolvent singular near zero.

The cheapest high-information structural tests are:

```text
ker A != 0 ?
Bc ⟂ ker A ?
```

and the parity comparison

```text
|nullity(T_even-zI)-nullity(T_odd-zI)| <= 1 ?
```

The rank-at-most-one parity defect makes the last statement a natural algebraic target, but all three remain OPEN until theoremized.

## Control-v2 authority

`research/RHRC/control_v2/` remains additive research-control infrastructure only.

It may:
- rank research actions;
- select first-break falsifiers;
- record archaeology/replay evidence;
- build fail-closed deformation-budget certificates.

It may not:
- write theorem authority;
- change claim registry status by inference;
- change `BOUNDARY.json` terminal status;
- convert numerical or historical clues into proof.

The merged control-plane anchor is #117 because #118/#119 changed theorem files but not Control-v2 semantics.

## Permanent firewalls

- RH remains OPEN.
- shell nonzero is not shell invariance or pure-shell behavior.
- D is algebraic, not unitary/isometric.
- exact cubic factorization is rank at most one, not exact rank one.
- predecessor nonnegative is not a positive spectral gap.
- use `(A-lam I)^(-1)` only for `lam<0`; no `A^-1` at zero.
- #119 root equivalence is not root exclusion.
- quotient secular scalar is not yet pointwise identified with the explicit Schur expression.
- root uniqueness, if proved, is not positivity.
- no finite/fitted deformation tail is a proof of complete future control.
- no source-normalization, promoted-binding, finite-to-infinite or RH change follows from #118/#119.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_119_DELTA.md` — current post-green theorem implications and falsification targets.
- `RESEARCH_LEADS.md` — accumulated lead ledger / historical option memory.
- `OBSTRUCTION_LEDGER.md` — reusable blockers and claim firewalls.
- `DEAD_ROUTES.md` — route failures requiring changed-premise justification before revival.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**