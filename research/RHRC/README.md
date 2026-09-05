# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 = PROVED / MERGED
RH = OPEN
~~~

Live GitHub head + Lean compiler + CI remain the exact authority.

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
shifted resolvent positivity / monotonicity                           DERIVED / OPEN FORMALIZATION
parity nullity difference <=1                                        DERIVED / OPEN FORMALIZATION
simultaneous parity-resonance classification                          OPEN
positivity / finite-to-infinite closure                              OPEN
RH                                                                     OPEN
~~~

## Current execution priority

1. **E1b/E2 — cubic-normalized Schur.** Use `dim_C S=1` together with the two theorem-backed nonzero shell vectors from #113/#115; transfer the Schur identity onto the canonical cubic shell line and normalize only scalar choice.
2. **E3 — shifted block rigidity.** Prove projected predecessor symmetry and quantitative coercivity; seek resolvent norm/positivity/monotonicity consequences.
3. **E4 — parity resonance.** Theoremize parity nullity difference and the common-resonance versus one-channel-resolvent dichotomy, then attack simultaneous resonance.
4. **Parallel diagnostic lane — deformation budget.** Test whether the exact N-flow admits a useful certified remaining-deformation budget. This lane is not theorem authority and must survive decision-commutation, horizon and first-break gates before it influences the proof plan.

The source-faithful `G1-B1B -> G1-final -> S-NEG -> G23` lane remains parallel.

## Control v2

`research/RHRC/control_v2/` is an additive research-control layer with no theorem/claim authority. It provides:

- deterministic RACR-style next-action ranking;
- MCM-style first-break contracts;
- an RH-native deformation-budget diagnostic;
- vocabulary-aware Git archaeology;
- optional external historical archive search;
- `as_of` counterfactual replay with future-source leakage guards;
- dead-route revival enforcement.

`research/RHRC/ffbbp/v16_*` exposes FFBBP v1.6 assurance primitives — especially diagnostic vs decision commutation, horizon certificates and explicit witness/masking checks — without changing the qualified RUN42C historical implementation.

The controller may say **where to look next**. Lean/CI still says **what is proved**. `runner/terminal_answer.py`, `BOUNDARY.json`, `CLAIM_REGISTRY.json` and `routes/ROUTE_REGISTRY.json` remain outside Control-v2 write authority.

## Deformation-budget safety rule

A local or finite calculation is never an infinite-tail certificate. A decision-bearing prune requires a certified positive lower margin and a certified upper bound for the complete remaining deformation budget. Small local residual, fitted convergence or numerical closeness cannot substitute for this.

## Claim firewalls after #115

- `V=W⊕S` is proved; shell invariance is not.
- nonzero shell coordinate is not a pure-shell statement.
- `F_N(v)=ell_N(v) g_N` does not prove `ell_N != 0`.
- D is algebraic, not unitary/isometric.
- the shifted Schur identity is a reduction, not a contradiction.
- E1 proves cubic-shell incidence, not cubic-normalized Schur rigidity.
- negative index exactly one, resolvent monotonicity and resonance exclusion remain open/formalization targets.
- no positivity theorem, finite-to-infinite closure or RH theorem follows from #115.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_115_DELTA.md` — current post-green E2/deformation-budget lead delta; supersedes the post-#113 delta for current execution.
- `RESEARCH_LEADS.md` — accumulated lead ledger and older option memory.
- `OBSTRUCTION_LEDGER.md` — explicit open obstructions/firewalls.
- `DEAD_ROUTES.md` — reusable route failures; revival requires a changed-premise record.
- `control_v2/README.md` — adaptive/retro research-control semantics.
- `CLAIM_REGISTRY.json` / `R003_PROMOTED_BINDINGS.json` — machine promotion surface; do not infer promotion from prose.

**RH remains OPEN.**
