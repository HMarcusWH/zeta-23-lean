# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED
RH = OPEN
~~~

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Hermitianity / displacement            PROVED / #96
  -> Euclidean constrained sector / exact dimensions              PROVED / #98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> exact reversal symmetry / even commutator collapse           PROVED / #102
  -> direct parity geometry / algebraic D-equivalence             PROVED / #103
  -> least bad parity size + predecessor nonnegative              PROVED / #105
  -> exact one-dimensional successor parity shell                 PROVED / #105
  -> negative first-bad eigenmode + noninheritance                PROVED / #107
  -> nonzero eigenmode shell projection + parity normals/KKT      PROVED / #109
  -> cubic parity channel + compressed defect finrank <= 1        PROVED / #110
  -> global first bad + both predecessor parities nonnegative     PROVED / #112
  -> intrinsic predecessor W + shell S, dim_C S = 1               PROVED / #112
  -> exact cubic defect factorization F_N(v)=ell_N(v) g_N         PROVED / #112
  -> canonical V = W ⊕ S coordinates                              PROVED / #113
  -> safe shifted predecessor inverse / reconstruction            PROVED / #113
  -> basis-free scalar shifted Schur identity                     PROVED / #113
  -> canonical cubic shell coordinate != 0 in either parity       PROVED / #115

NOW
  E1b/E2 cubic-normalized scale-free Schur equation

THEN
  E3 projected predecessor symmetry / shifted coercivity / resolvent
  E4 parity nullity / common-resonance vs one-channel resolvent
  classify or exclude simultaneous first-bad resonance

PARALLEL
  deformation-budget paper/diagnostic lane
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## What PR #115 changed

PR #115 theoremized the exact E1 statement needed for composition: the canonical cubic parity-defect direction is not inherited from the centered predecessor and therefore has a nonzero canonical intrinsic shell coordinate.

At the same global first-bad finite state we now have

~~~text
intrinsicShellPart p N v != 0
intrinsicCubicShellPart p N != 0
Module.finrank C (intrinsicParitySuccShell p N) = 1
~~~

so the negative-mode shell coordinate and cubic shell coordinate are two nonzero vectors in the same one-dimensional complex shell. E1b/E2 is to identify them up to a nonzero scalar, transport the #113 shifted Schur identity onto the canonical cubic shell line and normalize only scalar choice.

The stronger optional closed-form projection coefficient

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5
~~~

was intentionally not made an E1 dependency and remains a lead unless separately theoremized.

## Parallel deformation-budget research lens

The exact centered N-flow suggests a separate search-contraction question. For fixed aperture/parity, let the candidate diagnostic state carry

~~~text
mu_N       spectral-floor lower information
q_N        new-shell stiffness information
beta_N     shell/predecessor coupling information
D_N        one-step downward-deformation upper bound
R_N        complete remaining deformation upper bound
H_N        headroom lower bound = mu_lower_N - R_upper_N
~~~

A paper-level two-by-two comparison motivates the safe one-step form

~~~text
D_N <= beta_upper_N^2 / gap_lower_N
~~~

when a positive shell gap is independently certified. The useful global target is a rigorous infinite-tail majorant. `D_N -> 0` by itself is not enough: the floor could already be negative.

A decision-bearing prune therefore requires

~~~text
certified mu_lower_N > certified R_upper_N.
~~~

Point estimates, fitted tails and small local residuals cannot substitute for that inequality.

## RHRC Control v2

PR #116 adds an **additive research-control layer** under `research/RHRC/control_v2/`. It has no theorem or claim-promotion authority.

It combines:

- deterministic RACR-style research-action ranking;
- MCM-style first-break / cheapest-decisive-falsifier contracts;
- FFBBP v1.6 assurance primitives for diagnostic vs decision commutation, residual horizons and witness masking;
- a read-only PIRE-style monitor for route oscillation, evaluator monoculture, benchmark lock-in and complexity ratchets;
- vocabulary-aware retroactive Git archaeology across historical refs;
- strict `as_of` counterfactual replay restricted to the historical reachable DAG;
- hash/availability-bound ingestion of external historical text snapshots;
- dead-route revival records.

The qualified RUN42C FFBBP implementation remains frozen and unchanged. The v1.6 assurance overlay does **not** inherit RUN42C qualification.

Control v2 may recommend **where to look next**. Lean/CI still decides **what is proved**. The controller cannot write `BOUNDARY.json`, `CLAIM_REGISTRY.json`, `routes/ROUTE_REGISTRY.json`, or the terminal RH answer.

## Permanent firewalls

- `V = W ⊕ S` is proved, but shell invariance under the compressed operator is not.
- nonzero shell coordinate does not imply a pure-shell eigenmode.
- D-equivalence is algebraic, not unitary or isometric.
- exact factorization through `g_N` does not prove `ell_N != 0` or exact rank one.
- `g_N != 0` does not prove the parity defect operator is nonzero.
- algebraic conjugation does not automatically preserve self-adjointness in the original inner product.
- no equal-spectrum, Hermitian interlacing or inertia transfer through D is proved.
- use `A-lam I` for `lam<0`; never assume `A^-1` at zero for the semidefinite predecessor block.
- the shifted Schur identity is a reduction, not a contradiction.
- negative index exactly one, resolvent monotonicity and simultaneous-resonance exclusion remain open/formalization targets.
- the deformation-budget asymptotics/tail certificate are a lead, not a theorem.
- generic R002 taper-grid and Bombieri zero-height truncations remain distinct from the canonical deterministic CCM finite family except where exact specialization/bridge theorems say otherwise.
- the legacy printed `finiteMatrix` differs from the canonical source matrix by a scalar identity; absolute PSD/inertia claims must use the canonical source normalization.
- positivity, finite-to-infinite closure and RH remain OPEN unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_115_DELTA.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond the entries actually present in the registries.

**RH remains OPEN.**
