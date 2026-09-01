# HMWH Zeta23 fork — current audit entry point

This file is the audit entry point for the active HMWH fork.

The pre-fork-facing Zeta23 audit is preserved verbatim in [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). It remains provenance for the inherited paper formalization; it is not a complete audit of the later RH research extensions.

## Current validation baseline

~~~text
repository: HMarcusWH/zeta-23-lean
main: 3e39ce86d27a4c642a1e0364f1954968ce22f1f4
tree: 6935902fbbb950847e1cdd16a61d95704e3a760d
merged through: PR #79
W0 theorem-green head: c8112f0ad12e0b2c2f1261cea3ba7726aa04be54
date: 2026-09-01
RH: OPEN
~~~

The exact W0 head passed the RHRC claim/regression suite, R003 normalization/source firewall, R004 scalar-shift audit, CCM build, ExceptionalZero build, no-placeholder gate, and the independent verification workflow. The headline W0 theorems have axiom surface `[propext, Classical.choice, Quot.sound]`.

Recent state history:

- PR #73 repaired source-normalization semantics;
- PR #75 synchronized G1-B1A;
- PR #76 added living research-control SSOTs;
- PR #77 theorem-locked W2-A;
- PR #78 synchronized the post-W2-A plan;
- PR #79 theorem-locked W0: off-line zero -> one compact C² pole-neutral negative genuine Weil test.


## Fork audit surfaces

The active fork is checked on multiple layers.

### Lean theorem builds

```bash
lake build
lake build Zeta23.ExceptionalZero
lake build Zeta23.CCM
```

Promoted fork theorem files are expected to contain:

- no `sorry`;
- no project-declared axioms;
- no hidden dependency on external Python/source-oracle code.

Headline route theorems are audited with `#print axioms`; accepted fork theorem surfaces use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` unless explicitly documented otherwise.

### RHRC regression and governance

```bash
python research/RHRC/tools/run_suite.py
```

The route/claim registry is fail-closed. Research evidence does not promote theorem status.

### R003 normalization/source firewall

```bash
python research/RHRC/routes/R003_ccm_bridge/check_source_normalization_firewall.py
```

This prevents direct semantic collapse of the legacy printed `finiteMatrix` into the canonical external source restriction.

The current canonical object map is recorded in `research/RHRC/routes/R003_ccm_bridge/CCM_CANONICAL_OBJECT_MAP_v3.json` and retains the matrix equalities:

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix
```

while `legacyPrintedMatrix = finiteMatrix`.

### R004 scalar-shift invariants

```bash
python research/RHRC/routes/R004_prolate_v2/check_normalization_shift_invariants.py
```

This guards the distinction between shift-invariant commutator/displacement structure and shift-sensitive absolute spectral claims.

## Comparator / inherited paper audit

The inherited paper theorem surface remains comparator-audited exactly as documented in:

- [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md);
- [comparator/README.md](comparator/README.md);
- [formalization.yaml](formalization.yaml).

Those files describe the preserved upstream formalization layer.

## Current claim firewall

G1-B1A remains merged and registered: finite source coordinate transport and zero-extended `kappa` image are theorem-locked. This does not include multiplicative-Haar/L² or ambient source-functional semantics.

W2-A is merged and registered:

~~~text
Summable Wsummand(f,g)
and
W(f,g) = EF.literatureRHS(EF.weilTest f g)
~~~

on the exact asymmetric compact-support regularity class.

W0 is now merged and registered as `R003_NEGATIVE_WEIL_TEST_CONTRACTION`. For every concrete off-line zero, Lean proves a compact C² test `h` with

~~~text
paperFT h ( I/2) = 0
paperFT h (-I/2) = 0
Re (zetaZeroConfig.W h h) < 0.
~~~

The physical contraction uses the exact coefficient convention

~~~text
h = ‖C‖ * k - conj(C) * translateRight k t.
~~~

This does **not** prove W1 recentering, W2-B reflection/evenization, W2-C additive identification, F0-B finite approximation, G1-B1B/G1-final/G23, F1, a first canonical crossing theorem, finite-negative exclusion, or RH.

The repository does **not** claim:

- the ambient external `QW_lambda/PsiSharp` correspondence;
- `QW_lambda|E_N = canonicalSourceMatrix`;
- source form-core / strict negative finite transfer;
- F1;
- a theorem-backed K0-K3 terminal reduction;
- canonical finite-negative exclusion;
- RH.

Merged repository truth is determined by live GitHub main plus the machine registries and exact Lean declarations.


## Audit authority

For current fork claims use, in order:

1. live compiler/CI on the exact head;
2. current merged Lean declarations;
3. `research/RHRC/CLAIM_REGISTRY.json`;
4. `research/RHRC/routes/ROUTE_REGISTRY.json`;
5. active route README;
6. historical settlements and receipts.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).
