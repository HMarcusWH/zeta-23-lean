# HMWH Zeta23 fork — current audit entry point

This file is the audit entry point for the active HMWH fork.

The pre-fork-facing Zeta23 audit is preserved verbatim in [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). It remains provenance for the inherited paper formalization; it is not a complete audit of the later RH research extensions.


## Current validation baseline

~~~text
repository: HMarcusWH/zeta-23-lean
main: 9e899ca322116e28a56a4412d48aef0052b86fbe
tree: ad636143768dcaa4dbeb23a0ea295d7b2d6b1c9b
merged through: PR #84
PR #83 theorem head: 556be6c2b42e912c58751988c580ab4e0091822d
PR #83 merge: 7b8e0cc9abbaeff97d88ec67ada40734619a8d07
PR #84 final validated head: 1a518c9ebd408fa559c5eff281eafe5ff3b2af48
date: 2026-09-01
RH: OPEN
~~~

PR #83 exact theorem head `556be6c2b42e912c58751988c580ab4e0091822d` passed both repository workflows and merged as `7b8e0cc9abbaeff97d88ec67ada40734619a8d07`. PR #84 exact head `1a518c9ebd408fa559c5eff281eafe5ff3b2af48` then passed both repository workflows and merged as current main `9e899ca322116e28a56a4412d48aef0052b86fbe`, preserving the #83 theorem files while cleaning the route/source governance state.

The headline W1 theorems have axiom surface

~~~text
[propext, Classical.choice, Quot.sound]
~~~

and prove exact closed-support transport plus the pointwise off-line-zero strict-aperture negative-test endpoint.

Recent state history:

- PR #77 theorem-locked W2-A;
- PR #79 theorem-locked W0: off-line zero -> compact C² pole-neutral negative Weil test;
- PR #80 promoted W0 and moved the roadmap frontier to W1;
- PR #81 theorem-locked, promoted and merged W1: the same obstruction can be recentered into an explicit strict margin `(r,3r)` inside aperture `L=4r`, preserving both pole zeros and negative W self-value;
- PR #82 synchronized the post-W1 documentation and selected concrete-zeta zero-side evenization as the next research spike;
- PR #83 theorem-locked W2-ZS, the generic diagonal `W = localizedWeilAdditiveRHS` identity, and the strict-aperture negative localized-additive witness;
- PR #84 cleaned the living authority/source-route state, fixed the boundary-ID lint hole, and made source negativity a separate OBS-015 gate.

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

**Source-sign firewall:** G1-B1B/G1-final are interface and restriction obligations. They do not by themselves theoremize `Re W(h,h)<0 -> QW<0`. A source proof of F1 still requires either an independent fixed-aperture negative-QW theorem (`S-NEG`) or an exact W/localized-additive/QW composition theorem.

W2-A is merged and registered:

~~~text
Summable Wsummand(f,g)
and
W(f,g) = EF.literatureRHS(EF.weilTest f g).
~~~

W0 and W1 are merged and registered, giving a compact C² pole-neutral test with strict negative W self-value and an explicit strict aperture margin.

PR #83 is merged and the Stage-B promotion records two new claims.

### R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE

For every compact C² concrete-zeta test `h`:

~~~text
zetaZeroConfig.W h h
  = Zeta23.CCM.localizedWeilAdditiveRHS h h.
~~~

Theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_eq_localizedWeilAdditiveRHS
~~~

Exact theorem head:

~~~text
556be6c2b42e912c58751988c580ab4e0091822d
~~~

The supporting W2-ZS proof package theoremizes concrete-zeta conjugation, the actual `rho -> 1-rho` carrier equivalence with multiplicity, `gammaOf` sign reversal, Fourier reflection, and summability-safe zero-sum reindexing. The proof does not open the pole/prime/gamma decomposition and has axiom surface `[propext, Classical.choice, Quot.sound]`.

### R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS

Every concrete off-line zeta zero yields

~~~text
exists L>0, r>0, h,
  L=4r
  and ContDiff R 2 h
  and HasCompactSupport h
  and tsupport h ⊆ Ioo r (3*r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h (±I/2)=0
  and Re(localizedWeilAdditiveRHS h h)<0.
~~~

This is the theorem-backed F0-B input.

The repository does **not** yet prove:

- F0-B finite approximation / strict-negativity transfer;
- a family-level W-continuity or uniform zero-side domination theorem for finite approximants;
- direct localized-additive continuity on the existing finite vectors;
- the old analytic W2-B reflection/gamma route;
- G1-B1B/G1-final/S-NEG/G23;
- F1;
- a first canonical crossing theorem;
- K0-K3 terminal exclusion;
- finite-negative exclusion;
- RH.

The old analytic W2-B route remains OPEN / DORMANT. Proving its intended diagonal conclusion by W2-ZS does not prove that historical proof route.

Merged repository truth remains determined by live GitHub main plus the machine registries and exact Lean declarations.

## Audit authority

For current fork claims use, in order:

1. live compiler/CI on the exact head;
2. current merged Lean declarations;
3. `research/RHRC/CLAIM_REGISTRY.json`;
4. `research/RHRC/routes/ROUTE_REGISTRY.json`;
5. active route README;
6. historical settlements and receipts.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).
