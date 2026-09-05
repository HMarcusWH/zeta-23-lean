# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

~~~text
live main after PR #116 = 8921572170e89d74216f0c5577b669696626219e
live main tree = fc138b517c6835230515167386eafe3ef3495baf

theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
Control v2 / FFBBP v1.6 assurance = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
~~~

Live GitHub head + Lean compiler + CI remain the exact authority. PR #116 did not advance theorem authority.

## Theorem-backed internal route

~~~text
F1 finite canonical negative obstruction                              PROVED / #94
constrained algebra / Euclidean sector                                PROVED / #96-#98
exact centered N-flow + fixed-L negative tail                         PROVED / #100
reversal symmetry / even commutator collapse                          PROVED / #102
direct parity geometry + algebraic D-equivalence                      PROVED / #103
least parity bad + one-dimensional successor shell                    PROVED / #105
negative first-bad eigenmode + noninheritance                         PROVED / #107
nonzero eigenmode shell projection + exact parity normals/KKT         PROVED / #109
cubic parity channel + compressed defect finrank <=1                  PROVED / #110
global first bad + both predecessor parities nonnegative              PROVED / #112
intrinsic W/S block, dim_C S=1 + exact cubic factorization            PROVED / #112
canonical V=W⊕S + shifted predecessor Schur reduction                 PROVED / #113
canonical cubic shell coordinate != 0 in either parity                PROVED / #115

cubic-normalized scale-free Schur equation                            NEXT / E2
projected A symmetry / shifted coercivity                             DERIVED / OPEN FORMALIZATION
E2+E3 certified one-step deformation bound                            LEAD / OPEN FORMALIZATION
shifted resolvent positivity / monotonicity                           DERIVED / OPEN FORMALIZATION
parity nullity difference <=1                                        DERIVED / OPEN FORMALIZATION
simultaneous parity-resonance classification                          OPEN
positivity / finite-to-infinite closure                              OPEN
RH                                                                     OPEN
~~~

## Current execution priority

1. **E1b/E2 — cubic-normalized Schur.** Use `dim_C S=1` together with the two theorem-backed nonzero shell vectors from #113/#115; transfer the Schur identity onto the canonical cubic shell line and normalize only scalar choice.
2. **E3 — shifted block rigidity.** Prove projected predecessor symmetry and quantitative coercivity; derive the safe resolvent estimate and, if the paper test survives, theoremize the one-step deformation bound.
3. **E4 — parity resonance.** Theoremize parity nullity difference and the common-resonance versus one-channel-resolvent dichotomy, then attack simultaneous resonance.
4. **Parallel diagnostic lane — deformation budget.** Probe `g_N=q_N-mu_N`, `beta_N` and `beta_N^2/g_N` for both parities and several fixed `L` values. Kill the route before analytic tail work if the gap/coupling/summability tests fail.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains parallel.

## Post-#116 synthesis

PR #116's first real-history controller run selected the deformation-budget paper test, but that recommendation is non-authoritative. The stronger mathematical composition is

~~~text
#115 cubic-shell incidence
  -> E2 cubic-normalized Schur
  -> E3 shifted coercivity / resolvent
  -> candidate certified one-step deformation theorem.
~~~

Exact N-flow already gives upward persistence of badness. Therefore a fully certified positive rigidity horizon at fixed `(L,p)` would exclude earlier badness by persistence and later badness by the complete future-deformation bound. The strong target is elimination of the whole fixed-`(L,p)` N-axis, not merely a finite search window. This is a LEAD / OPEN certification target.

The required global condition is all-`L` certification / controlled `L`-dependence; one universal `Nstar` independent of `L` is not assumed unless a later theorem needs it.

## Cheap projected-defect lead

PR #112 proves `F_N(z)=ell_N(z) g_N`; #115 proves the cubic generator has nonzero intrinsic shell coordinate. The cheap formalization candidate is

~~~text
intrinsicShellPart(F_N z)=0  <->  cubicDefectFunctional ... z = 0.
~~~

This would identify the scalar functional with visibility of the exact defect in the unique new N-flow quotient direction. It does not prove the functional nonzero on any specific vector.

## Control v2 hardening

`research/RHRC/control_v2/` remains an additive research-control layer with no theorem/claim authority. The hardened version now enforces:

- separate theorem and control-plane anchors;
- typed, exact, contiguous finite-prefix deformation steps;
- no certified numeric tail without a passed horizon certificate targeting `remaining_deformation_budget`;
- decision commutation for reduced-model decision-bearing `PRUNE` use when declared;
- retro receipts bound to exact declared Git search paths;
- no generic `fold`/`rupture`/`slack` alias flood in the deformation-budget concept;
- deterministic score formula and candidate score/blocker diagnostics.

The controller may say **where to look next**. Lean/CI still says **what is proved**. `runner/terminal_answer.py`, `BOUNDARY.json`, `CLAIM_REGISTRY.json` and `routes/ROUTE_REGISTRY.json` remain outside Control-v2 write authority.

## Deformation-budget safety rule

A local or finite calculation is never an infinite-tail certificate. A decision-bearing prune requires a certified positive lower margin and a certified upper bound for the complete remaining deformation budget. Small local residual, fitted convergence or numerical closeness cannot substitute for this.

For reduced-model decision-bearing use, numerical closeness is also not decision commutation.

## Claim firewalls after #116

- `V=W⊕S` is proved; shell invariance is not.
- nonzero shell coordinate is not a pure-shell statement.
- `F_N(v)=ell_N(v) g_N` does not prove `ell_N != 0`.
- D is algebraic, not unitary/isometric.
- the shifted Schur identity is a reduction, not a contradiction.
- E1 proves cubic-shell incidence, not cubic-normalized Schur rigidity.
- the diagnostic 2x2 displacement formula is not an operator theorem.
- `beta_N -> 0` alone does not imply a summable deformation tail.
- negative index exactly one, resolvent monotonicity and resonance exclusion remain open/formalization targets.
- no positivity theorem, finite-to-infinite closure or RH theorem follows from #115/#116.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_116_DELTA.md` — current post-green E2/deformation-budget/control-hardening lead delta.
- `RESEARCH_LEADS.md` — accumulated lead ledger and older option memory.
- `OBSTRUCTION_LEDGER.md` — explicit open obstructions/firewalls.
- `DEAD_ROUTES.md` — reusable route failures; revival requires a changed-premise record.
- `control_v2/README.md` — deterministic/retro research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**
