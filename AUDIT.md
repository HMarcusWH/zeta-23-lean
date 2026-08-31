# HMWH Zeta23 fork — current audit entry point

This file is the audit entry point for the active HMWH fork.

The pre-fork-facing Zeta23 audit is preserved verbatim in [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). It remains provenance for the inherited paper formalization; it is not a complete audit of the later RH research extensions.

## Current validation baseline

```text
repository: HMarcusWH/zeta-23-lean
base main before PR #77: 2ac1dccbefba01a4d3d4b0672fe87935ab159801
PR #77 theorem-green head: 509645ad2b30288d175ff2ef5a6651839991649e
PR #77 final promoted/synchronized head: cd20d84e30038a7d14da1e8ee1d2ca1920d344fd
final #77 workflow state: GREEN
```

The final #77 head passed the RHRC claim/regression suite, R003 normalization/source firewall, R004 scalar-shift audit, CCM build, ExceptionalZero build, no-placeholder gate, and the independent verification workflow. Live GitHub `main` and merge metadata remain authoritative for the eventual merge commit SHA; this audit records the exact validated theorem/promotion object.

Recent documentation history:

- PR #73 repaired source-normalization semantics;
- PR #72 theorem-locked G1-B1A finite `kappa`/source-sector transport;
- PR #74 reset the living repository documentation;
- PR #75 synchronized the merged G1-B1A state;
- PR #76 added the living lead ledger and current-plan SSOTs;
- PR #77 theorem-locked and promoted W2-A.


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

The repository does **not** claim:

- the ambient external `QW_lambda/PsiSharp` correspondence;
- `QW_lambda|E_N = canonicalSourceMatrix`;
- source form-core / Rayleigh-bottom convergence;
- fixed-aperture Suzuki closure;
- canonical finite-negative exclusion;
- RH.

Validated branch heads are evidence for the exact checked object; merged repository truth is determined by live GitHub main plus the machine registries.

## Audit authority

For current fork claims use, in order:

1. live compiler/CI on the exact head;
2. current merged Lean declarations;
3. `research/RHRC/CLAIM_REGISTRY.json`;
4. `research/RHRC/routes/ROUTE_REGISTRY.json`;
5. active route README;
6. historical settlements and receipts.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).
