# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after PR #119 = d4175d2bb305e62863f593824b3f40e921a46ee6
live main tree = 1985472ac470822af279044261fa365fb9bb5535

theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
theorem-bearing merged through = PR #119
FIRST-BAD-RIGIDITY-E3-A exact canonical secular equivalence = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots. PRs #118/#119 advanced theorem authority but did not change Control-v2 semantics, so the separate control-plane anchor remains #117.

## Current RH-directed theorem ladder

```text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Hermitianity / Euclidean sector        PROVED / #96-#98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> exact reversal symmetry / even commutator collapse           PROVED / #102
  -> direct parity geometry / algebraic D-equivalence             PROVED / #103
  -> least/global first bad + predecessor nonnegative             PROVED / #105,#112
  -> 1d successor shell + negative first-bad eigenmode            PROVED / #105,#107
  -> exact parity normals + KKT                                   PROVED / #109
  -> cubic parity defect finrank <= 1                             PROVED / #110
  -> intrinsic W/S block + exact cubic factorization              PROVED / #112
  -> canonical V=W⊕S + safe shifted predecessor resolvent         PROVED / #113
  -> canonical cubic shell coordinate != 0                        PROVED / #115
  -> canonical cubic quotient coordinate + normalized Schur       PROVED / #118
  -> exact secular scalar root iff negative-shift eigenmode        PROVED / #119

NOW
  E3-B metric bridge:
    projected predecessor symmetry
    shifted coercivity / resolvent norm and positivity bounds
    identify #119 quotient secular scalar with explicit Schur scalar

PARALLEL / NEXT
  E4 zero-resonance / parity-nullity structure
  theorem-backed one-step deformation inequality if E3-B succeeds
  resolvent monotonicity / root uniqueness only after the explicit bridge

PARALLEL DIAGNOSTIC
  deformation-budget falsification lane
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
```

## What PR #118 changed

PR #118 selected the nonzero canonical cubic shell vector as the distinguished coordinate on the one-dimensional intrinsic successor shell. It proves exact reconstruction from that coordinate, identifies the successor/predecessor quotient with one complex scalar, and canonically normalizes a genuine negative eigenmode so its shell part is exactly `intrinsicCubicShellPart`.

It also proves that on the odd carrier the exact cubic parity defect coefficient is literally the canonical quotient coordinate of the intertwining defect. This does **not** prove that the defect functional is nonzero on a specific vector.

## What PR #119 changed

PR #119 closes the missing converse direction in the first-bad Schur reduction.

For every safe negative shift `lam < 0` under predecessor nonnegativity it constructs the canonical trial vector

```text
u_lam = -(A-lam I)^(-1) B c + c
```

with canonical cubic shell part `c`, defines the full residual

```text
r_lam = T u_lam - lam u_lam,
```

proves the predecessor coordinate of `r_lam` is zero, and defines

```text
cubicSecularScalar(lam) = intrinsicCubicQuotientCoordinate(r_lam).
```

The main theorem is the exact two-way criterion

```text
cubicSecularScalar(lam) = 0
  <-> exists nonzero v, T v = lam v
```

for `lam < 0` in the safe predecessor regime.

A hypothetical off-line zero is now reduced to a global-first-bad finite state carrying an exact negative root of this canonical scalar equation.

### Critical distinction after #119

The #119 secular scalar is the faithful **quotient coordinate of the full residual**. The older #113/#118 Schur expression

```text
<Tc,c> - lam<c,c> - <(A-lam I)^(-1)Bc,Bc>
```

is theorem-backed on genuine eigenmodes, but has not yet been identified pointwise with the #119 scalar for every safe negative shift.

That exact bridge is part of E3-B. Do not silently treat the two scalarizations as definitionally equal.

## Current mathematical frontier

### E3-B — projected metric / explicit secular bridge

The next theorem package should establish, in the repository's exact inner product:

1. `intrinsicPredecessorBlock` is symmetric;
2. `A-lam I` has quantitative coercivity for `lam<0`;
3. the shifted resolvent is symmetric, has real/nonnegative quadratic values, and obeys a safe norm bound;
4. the #119 quotient-coordinate scalar equals the normalized explicit Schur scalar.

Only after this bridge is proved should the project attempt scalar sign or monotonicity theorems.

### E4 — zero resonance is now a first-class obstruction

Global-first-bad gives predecessor **nonnegativity**, not strict positivity. Therefore `A` may have a zero kernel, and `(A-lam I)^(-1)` can become singular as `lam` approaches zero from below.

The high-value parallel question is whether the canonical shell coupling `b=Bc` annihilates `ker A`, or whether the zero-resonant component yields an alternative rigidity constraint. The rank-at-most-one parity defect and algebraic even/odd equivalence make parity nullity comparison a natural companion theorem.

### Deformation-budget composition

Once E3-B supplies a theorem-backed predecessor floor/resolvent estimate, the diagnostic quantities

```text
q_N
beta_N
g_N = q_N - mu_N
```

can be attached to a genuine operator inequality. The expected target is

```text
d_N (g_N + d_N) <= beta_N^2,
```

with `d_N = mu_N-lam`, and the shortcut

```text
d_N <= beta_N^2/g_N
```

only when `g_N>0` is independently certified.

A finite prefix, fitted tail, local residual or numerical decay pattern is never an infinite-horizon certificate.

## Permanent firewalls

- RH remains OPEN.
- `V=W⊕S` is proved; shell invariance under the compressed operator is not.
- nonzero shell coordinate does not imply a pure-shell eigenmode.
- D-equivalence is algebraic, not unitary or isometric.
- exact cubic factorization does not prove the defect functional is nonzero or the defect rank exactly one.
- #119 secular-root equivalence is a spectral reduction, not root exclusion.
- the #119 quotient scalar and the explicit Schur expression are distinct theorem objects until E3-B proves their bridge.
- predecessor nonnegative does not mean predecessor strictly positive; zero resonance remains possible.
- use `A-lam I` for `lam<0`; never assume `A^-1` at zero.
- root uniqueness, if later proved, is not root absence.
- no equal-spectrum, Hermitian interlacing or inertia transfer through D is proved.
- a diagnostic `2x2` formula is not an operator theorem.
- generic R002 taper-grid and Bombieri zero-height truncations remain distinct from the canonical deterministic CCM family except where exact bridge theorems say otherwise.
- the legacy printed `finiteMatrix` differs from the canonical source matrix by a scalar identity; sign-sensitive spectral claims must use the canonical source normalization.
- positivity, finite-to-infinite closure and RH remain OPEN unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_119_DELTA.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond the entries actually present in the registries.

**RH remains OPEN.**