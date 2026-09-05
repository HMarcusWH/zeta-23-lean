# Research leads — post-PR #115 delta

> **RH remains OPEN.**

This is the current incremental research delta after merged theorem-bearing PR #115. It supersedes `RESEARCH_LEADS_POST_113_DELTA.md` for the E1/E2 execution frontier while preserving the older file as historical evidence.

## Authority

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED
RH = OPEN
~~~

Live GitHub head + Lean/compiler/CI remain authoritative over this research delta.

## What became formally true in #115

At the same global first-bad finite state already carrying the #112/#113 intrinsic predecessor/shell block, negative eigenmode, exact cubic factorization and shifted Schur identity, the canonical parity cubic direction now has a nonzero intrinsic shell coordinate:

~~~text
intrinsicCubicShellPart p N != 0
~~~

for both parity carriers in the stated nontrivial range.

This was proved without making the optional closed-form projection coefficient a dependency. In particular,

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5
~~~

remains an optional lead unless separately theoremized.

## Immediate composition consequence

### L-115-E2 — cubic-normalized shell/Schur composition

**Research status:** ACTIVE / NEXT  
**Formal status:** DERIVED INTERFACE + OPEN FORMALIZATION

The #113 first-bad eigenmode shell coordinate and #115 cubic shell coordinate are both nonzero vectors in the same complex one-dimensional shell. Therefore they are nonzero scalar multiples. The #113 Schur identity is homogeneous of degree two in the shell vector, so the immediate target is to move the identity onto the canonical cubic shell line and normalize away scalar choice.

Target shape:

~~~text
canonical cubic shell c != 0
v_shell = beta * c, beta != 0

<Tc,c>/<c,c>
  - lam
  - <(A-lam I)^(-1)Bc, Bc>/<c,c>
  = 0
~~~

**Firewall:** this is a canonical scalar reduction, not a contradiction. Generic Hermitian systems can have negative scalar Schur roots.

## E3/E4 downstream state

### L-115-E3 — shifted block rigidity

**Research status:** READY  
**Formal status:** DERIVED / OPEN FORMALIZATION

Still target:

- projected predecessor symmetry;
- quantitative coercivity of `A-lam I` for real `lam<0`;
- resolvent norm/positivity consequences;
- scalar resolvent monotonicity if justified.

The moving-spectral-floor viewpoint is a useful paper abstraction, but no monotonicity or asymptotic tail statement is promoted by #115.

### L-115-E4 — parity resonance

**Research status:** READY / DOWNSTREAM  
**Formal status:** DERIVED + OPEN

Still target:

- algebraic parity nullity difference at most one;
- common-resonance vs one-channel opposite-parity resolvent dichotomy;
- classification/exclusion of simultaneous first-bad parity resonance.

D remains algebraic rather than unitary/isometric; Hermitian interlacing/inertia transport through D remains forbidden without a separate theorem.

## New parallel lead — deformation budget

### L-115-DB — finite remaining-deformation budget

**Research status:** TESTING / PARALLEL  
**Formal status:** LEAD / HYPOTHESIS

Treat exact centered N-flow as a nested spectral process. For fixed `(L,p)`, let `mu_N` denote the constrained spectral floor and define a one-step downward movement budget. With a normalized one-dimensional new shell, write schematic shell stiffness/coupling data as `q_N` and `beta_N`.

The paper-level two-by-two comparison gives a candidate bound

~~~text
0 <= mu_N - mu_(N+1) <= D_N
~~~

and, when a positive shell gap is independently certified,

~~~text
D_N <= beta_upper_N^2 / gap_lower_N.
~~~

The useful global object is not `D_N -> 0`; it is a certified complete remaining budget

~~~text
R_N = sum_{k>=N} D_k
~~~

or another rigorous infinite-tail majorant. A certified positive lower headroom

~~~text
H_N = mu_lower_N - R_upper_N > 0
~~~

would rule out a future zero crossing for that certified lane.

### Required falsification gates

Before any theorem-oriented promotion:

1. calculate/estimate the canonical shell stiffness and coupling rather than a coordinate-dependent surrogate;
2. determine whether the shell gap stays usefully positive;
3. determine whether coupling admits a summable certified majorant;
4. require FFBBP v1.6 **decision commutation**, not only numerical closeness, for any reduced/reference pruning decision;
5. require an actual horizon certificate for tail language;
6. test parity and aperture dependence explicitly;
7. remember that `D_N -> 0` is compatible with a spectral floor that is already negative;
8. do not turn a fitted finite-N decay law into an infinite-tail theorem.

This lead may materially narrow the search space even if it does not close RH: certified cumulative upper bounds can exclude ranges of N before enough downward movement is even available to reach zero.

## Supporting-stack upgrade — Control v2

PR #116 introduces an additive research-control layer around, not inside, theorem authority:

- FFBBP v1.6 assurance contracts: diagnostic/decision commutation, horizon, explicit witness/masking checks;
- deterministic RACR-style route ranking;
- MCM-style first-break declarations;
- retroactive Git archaeology across historical refs;
- counterfactual `as_of` replay restricted to the historical reachable DAG;
- hash/availability-bound external archive replay;
- dead-route revival records.

The qualified RUN42C profile is not rewritten and v1.6 does not inherit its qualification.

## Retroactive clue families to re-test

The supporting-stack archaeology has already identified a vocabulary lineage worth replaying against the current exact N-flow object:

~~~text
evolving canvas
residual headroom
restriction/prolongation round-trip residual
detectability budget
reverse reduction / equivalence wall
residual-aware computational routing
residual horizon / decision commutation
~~~

These are **historical clue families**, not imported RH lemmas. Their value is to nominate invariants, falsification tests and routing policies that must be re-derived against the canonical CCM object before use.

## Revival firewall

Do not let the deformation language silently revive DR-010. The dead route was the inference

~~~text
fitted small commutator -> eigenvector convergence.
~~~

The current exact N-flow/parity/cubic route is different. Any future proposal that again relies on a fitted generator, small commutator or assumed spectral gap must carry an explicit changed-premise `RevivalRecord`.

## Current priority

~~~text
PRIMARY THEOREM FRONTIER
  E1b/E2 cubic-normalized Schur
  -> E3 shifted block rigidity
  -> E4 parity resonance

PARALLEL DIAGNOSTIC / SEARCH-CONTRACTION FRONTIER
  deformation-budget first-break tests
  -> canonical q_N / beta_N behaviour
  -> certified horizon/tail feasibility
  -> only then consider theoremization

RH OPEN
~~~

**RH remains OPEN.**
