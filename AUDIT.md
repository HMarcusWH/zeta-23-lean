# HMWH Zeta23 fork — current audit entry point

This file is the audit entry point for the active HMWH fork.

The pre-fork-facing Zeta23 audit is preserved verbatim in [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). It remains provenance for the inherited paper formalization; it is not a complete audit of the later RH research extensions.

## Current merged baseline

```text
repository: HMarcusWH/zeta-23-lean
main: f62171c3610c27190d9d3165a9c692ad08985077
merged through: PR #74
```

PR #73 repaired source-normalization semantics. PR #72 then merged the G1-B1A finite `kappa`/source-sector theorem layer on top of that repair, and PR #74 reset the living repository documentation. The exact compiler/CI evidence for individual PR heads is authoritative over this summary.

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

G1-B1A is merged and registered: the finite source coordinate transport and zero-extended `kappa` image are theorem-locked. This does not include multiplicative-Haar/L2 or ambient source-functional semantics.

W2-A has passed exact-head Lean/CI and is promoted in PR #77: for the concrete zeta configuration, admissible pairs satisfy both W-summand summability and

~~~text
W(f,g) = EF.literatureRHS (EF.weilTest f g).
~~~

The theorem requires `f` to be C² compactly supported and `g` only continuous compactly supported. The audited axiom surface is `[propext, Classical.choice, Quot.sound]`. This does not yet prove W2-B reflection/evenization, W2-C diagonal additive identification, W0 contraction, F1, or RH.

As of the merged state above, the repository does **not** claim:

- the ambient external `QW_lambda/PsiSharp` correspondence;
- `QW_lambda|E_N = canonicalSourceMatrix`;
- source form-core / Rayleigh-bottom convergence;
- fixed-aperture Suzuki closure;
- canonical finite-negative exclusion;
- RH.

Green work on a branch is not part of merged theorem state until it is merged and registered.

## Audit authority

For current fork claims use, in order:

1. live compiler/CI on the exact head;
2. current merged Lean declarations;
3. `research/RHRC/CLAIM_REGISTRY.json`;
4. `research/RHRC/routes/ROUTE_REGISTRY.json`;
5. active route README;
6. historical settlements and receipts.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).
