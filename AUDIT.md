# HMWH Zeta23 fork — current audit entry point

This file is the audit entry point for the active HMWH fork.

The pre-fork-facing Zeta23 audit is preserved verbatim in [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). It remains provenance for the inherited paper formalization; it is not a complete audit of the later RH research extensions.

## Current validation baseline

~~~text
repository: HMarcusWH/zeta-23-lean
main before PR #81: 8960b80b4a871bd86f94509dfa872ecc6939b0cd
tree before PR #81: 956601c77d1e9f32bab339dbbb81130296d1b5c7
merged through: PR #80
W1 Stage-A theorem-green head: 7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
date: 2026-09-01
RH: OPEN
~~~

The exact W1 Stage-A head passed both repository workflows: RHRC claim/regression suite, R003 normalization/source firewall, R004 scalar-shift audit, CCM build, ExceptionalZero build, no-placeholder gate, and independent Permansson verification.

The headline W1 theorems have axiom surface

~~~text
[propext, Classical.choice, Quot.sound]
~~~

and prove exact closed-support transport plus the pointwise off-line-zero strict-aperture negative-test endpoint.

Recent state history:

- PR #77 theorem-locked W2-A;
- PR #79 theorem-locked W0: off-line zero -> compact C² pole-neutral negative Weil test;
- PR #80 promoted W0 and moved the roadmap frontier to W1;
- PR #81 Stage A theorem-locks W1: the same obstruction can be recentered into an explicit strict margin `(r,3r)` inside aperture `L=4r`, preserving both pole zeros and negative W self-value.

The PR #81 promotion/documentation head must pass the same exact-head gates before merge.

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
W(f,g) = EF.literatureRHS(EF.weilTest f g).
~~~

W0 is merged and registered:

~~~text
off-line zero
  -> compact C² pole-neutral h
  -> Re W(h,h) < 0.
~~~

W1 is theorem-green on the exact PR #81 Stage-A head and promoted on the branch as `R003_STRICT_APERTURE_NEGATIVE_WEIL_TEST`:

~~~text
off-line zero
  ->
exists L>0, r>0, h,
  L = 4r
  and tsupport h ⊆ Ioo r (3r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h (±I/2)=0
  and Re W(h,h)<0.
~~~

This does **not** prove:

- pole-neutrality transfer from `h` to `EF.weilTest h h`;
- mu/gamma reflection evenness;
- weighted gamma-channel integrability;
- W2-B/W2-C;
- F0-B;
- G1-B1B/G1-final/G23;
- F1;
- a first canonical crossing theorem;
- finite-negative exclusion;
- RH.

The repository does **not** claim the ambient external `QW_lambda/PsiSharp` correspondence, `QW_lambda|E_N = canonicalSourceMatrix`, a theorem-backed K0-K3 terminal reduction, or RH.

Merged repository truth remains determined by live GitHub main plus the machine registries and exact Lean declarations; the final PR #81 head must be green before merge.

## Audit authority

For current fork claims use, in order:

1. live compiler/CI on the exact head;
2. current merged Lean declarations;
3. `research/RHRC/CLAIM_REGISTRY.json`;
4. `research/RHRC/routes/ROUTE_REGISTRY.json`;
5. active route README;
6. historical settlements and receipts.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).
