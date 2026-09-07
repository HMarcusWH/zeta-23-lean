# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + EXACT ZERO-SHIFT ENDPOINT/RESONANCE DICHOTOMY PROVED THROUGH PR #125; E4-A3 BRANCH RIGIDITY CURRENT. RH OPEN.**

## Current authority split

```text
theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
theorem tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427
theorem-bearing merged through = PR #125
E4-A2 kernel/range zero-shift dichotomy + strict regular endpoint = PROVED / MERGED

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
FIRST-BAD-RIGIDITY-E4-A2 exact resonant identity/lower bound      PROVED / #124
FIRST-BAD-RIGIDITY-E4-A2 canonical endpoint + complete square     PROVED / #125
FIRST-BAD-RIGIDITY-E4-A2 decoupled Re S0<0                       PROVED / #125
off-line zero -> strict endpoint OR resonant first-bad package    PROVED / #125
```

## Exact post-#125 first-bad state

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
- exact E4-A1 coupling classification on `ker A`;
- canonical decomposition `W=ker A⊕range A`;
- one of two exact E4-A2 mechanisms:

  ```text
  REGULAR:
    Ax0=b
    S0=<Tc,c>-<x0,b>
    endpoint independent of x0
    predecessorPart(Tu0)=0 for u0=-x0+c
    exact complete square
    Re S0<0

  RESONANT:
    ∃z∈ker A, <z,b>!=0
    <z,b>=(-lam)<z,R_lam b>
    |<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
  ```

This is a finite-dimensional rigidity package, not an RH proof.

## E4-A2 settlement

**PROVED / #124-#125.**

The decoupled branch no longer needs `A^-1` at zero: #124 proves range membership, existence of a preimage and solution-independence of the quadratic coupling. #125 turns that invariant scalar into the actual zero-shift endpoint, proves the exact complete square and forces `Re S0<0` at the negative secular root.

The resonant branch is not excluded. #124 already supplies an exact resolvent identity and denominator-free quantitative lower bound.

## Current route state — E4-A3 branch rigidity

### A3a — zero-shift shell response

**DERIVED / OPEN FORMALIZATION.**

#125 proves

```text
predecessorPart(Tu0)=0.
```

Since `V=W⊕S`, theoremize `T u0∈S`; then use the canonical cubic shell coordinate and `dim_C S=1` to identify the exact one-dimensional response coefficient and its relation to `S0`.

**Firewall:** this does not by itself prove `u0` is an eigenvector.

### A3b — exact resonant pole

**LEAD / OPEN.**

Use #124's `ker A⊕range A` split to decompose `b=bK+bR` and prove the exact kernel-pole contribution to the safe shifted resolvent. The target is an algebraic decomposition, not an asymptotic slogan.

### A3c — branch rigidity

**OPEN.**

Compose A3a/A3b with:

- rank-at-most-one parity defect;
- parity KKT / normal-space geometry;
- canonical cubic quotient coordinate;
- first-bad minimality and exact N-flow.

Attempt to exclude one or both branches or to classify the surviving finite countermodels more tightly.

## E4-B — parity shifted-nullity

**OPEN / PARALLEL.**

Use the existing algebraic D-equivalence and same-space parity defect with finrank <=1 to theoremize a shifted-nullity comparison. Do not import unitary interlacing through D.

## E3-C — monotonicity / root-count control

**OPEN / PARALLEL.**

The exact root detector is a real explicit scalar on `lam<0`. A shifted-resolvent identity may yield strict monotonicity and at most one negative root.

Permanent firewall:

```text
at most one negative root != no negative root.
```

## E3-B3 — general predecessor-floor theorem

**LEAD / OPEN FORMALIZATION.**

Generalize the #122 `mu=0` metric estimate. Under

```text
mu ||w||^2 <= Re <Aw,w>,
lam<mu,
```

prove the denominator `mu-lam` resolvent estimate and derive

```text
d_N(g_N+d_N) <= beta_N^2.
```

The shortcut `d_N<=beta_N^2/g_N` requires separately proved `g_N>0`.

## Deformation-budget composition and falsification lane

The theorem-backed ancestry is now

```text
#119 exact root detector
  -> #121 explicit Schur bridge
  -> #122 real metric/resolvent control
  -> #124 zero-shift/resonance split
  -> #125 strict regular endpoint
  -> E4-A3 branch rigidity.
```

The cheap diagnostic order remains

```text
g_N=q_N-mu_N
beta_N
beta_N^2/g_N.
```

Kill the route if the gap fails, coupling does not decay usefully, or the ratio cannot support a complete summable certified tail. A finite prefix, fitted tail or local residual is not a complete budget.

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
- `Re S0<0` is not branch exclusion;
- resonance is not automatically contradictory;
- `T u0∈S` would not by itself imply an eigenvector;
- root uniqueness is not root exclusion;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_125_DELTA.md`.

**RH remains OPEN.**