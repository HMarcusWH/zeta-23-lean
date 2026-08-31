# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **Claim firewall: the Riemann Hypothesis is OPEN in this repository.**
>
> Green supporting theorems, finite matrix identities, numerical experiments, source-formula agreement, displacement structure, or route closure below the terminal theorem do not constitute a proof of RH.

This repository began as a fork of Anthropic's Lean 4 formalization accompanying **"More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line"** (arXiv:2608.13637). The inherited Zeta23 formalization remains the baseline analytic and linear-algebra library.

The fork is now an active research repository pursuing exact, falsifiable routes toward the Riemann Hypothesis. The additional work includes exceptional-zero detectors, two-translate theorems, finite Guinand--Weil dictionaries, explicit-formula extensions, exact finite zero-side matrices, Connes--Consani--Moscovici (CCM) finite source normalization, localized Fourier spaces, and a developing fixed-aperture Weil-form / variational route.

The original upstream README is preserved at [UPSTREAM_README.md](UPSTREAM_README.md). The original upstream audit is preserved at [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). [formalization.yaml](formalization.yaml) describes that preserved upstream formalization layer; it is not a complete metadata description of the later HMWH RH research extensions.

## Repository identity

There are two deliberately separated layers.

### 1. Preserved Zeta23 baseline

The inherited project proves the paper's headline zero-proportion theorems and supporting analytic infrastructure in Lean 4 / Mathlib. Its baseline is pinned in [UPSTREAM_BASELINE.json](UPSTREAM_BASELINE.json).

Important inherited assets include:

- Weil explicit-formula machinery;
- Riemann--von Mangoldt counting;
- gamma/Stirling estimates;
- prime-side estimates;
- linear algebra including inertia, Weyl bounds, and rank--trace tools;
- the original comparator-checked theorem surface.

### 2. HMWH RH research fork

The fork adds theorem-bearing Lean code under, among other places:

- `Zeta23/ExceptionalZero/`;
- `Zeta23/CCM/`;
- selected supporting linear-algebra and route-integration modules.

Research governance, discovery tooling, source maps, falsifiers, route registries, and evidence receipts live under `research/RHRC/`.

The rule is strict:

> Research tooling may suggest or falsify. Lean/compiler/CI determines theoremhood.

## Current RH route map

The live research program is organized as four principal routes.

### R001 — exceptional-zero amplification

The zero-side exposed-pole / filtered-growth chain is formally strong, but the remaining scalar arithmetic upper-bound target has itself been proved RH-equivalent. R001 is therefore not treated as an easier terminal route.

### R002 — multi-probe / negative-index route

Exact block-level off-critical separation has been proved. Generic windowed visibility and its arithmetic leg remain open; the latter is a band-limited Weil-positivity problem. PR #66 also proved that the generic smooth-taper R002 production object is **not** simply the canonical CCM finite object in another basis.

### R003 — CCM / finite Weil bridge

This is the current critical finite-to-source route.

Merged work through the #71-#74 sequence has established, among other things:

- finite Guinand--Weil dictionary identities;
- the literal-tent explicit-formula extension;
- the exact finite zero-side bridge;
- the cutoff-free finite source matrix;
- localized hard-window Fourier basis geometry;
- the actual full-complex zero-extended additive finite space;
- the additive localized Weil RHS restriction;
- the direct Section-4 source matrix;
- canonical source-normalization repair;
- the finite source `kappa` coordinate/source-sector bridge, including actual zero-extended source finite vectors.

The next source-facing obligations are the actual `d*u` / `PsiSharp` / `QW_lambda` correspondence, and then the theorem

```text
QW_lambda restricted to E_N = canonicalSourceMatrix.
```

A validated green PR is not part of merged theorem state until it is actually merged and registered.

### R004 — finite displacement / structural route

The exact centered-index displacement law and rank-at-most-two consequence are theorem-authoritative. The older fitted-tridiagonal small-commutator -> eigenvector-convergence story is not supported because the fitted generator's spectral gaps collapse on tested finite cases.

R004 remains useful as a structural tool, not a proof of RH.

## Canonical CCM object firewall

After the source audit and normalization repair, the theorem-authoritative direct-source finite object is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix
  = zeroSideMatrix            (under the proved positive-aperture bridge).
```

The historical literal printed-(4.11)/(4.14) object is

```text
legacyPrintedMatrix = finiteMatrix.
```

Lean proves the scalar-shift relation

```text
canonicalSourceMatrix
  = legacyPrintedMatrix
    + 2*legacyPrintedCorrection(L)*I.
```

This distinction is mathematically important.

Scalar identity shifts preserve:

- commutators and displacement laws;
- eigenvectors/eigenspaces;
- eigenvalue gaps and ordering.

They do **not** preserve:

- absolute eigenvalues;
- positivity / PSD;
- inertia;
- lower bounds;
- trace or determinant.

Any downstream spectral-sign argument must therefore identify the canonical matrix explicitly.

## Current critical path

The stable work-package names, not historical PR numbers, define the mathematical route:

```text
finite dictionary / zero-side bridge                 CLOSED
  -> cutoff-free/canonical finite source matrix      CLOSED
  -> G0 localized basis + finite space               CLOSED
  -> G1-A additive finite restriction                CLOSED
  -> direct source normalization/firewall            CLOSED
  -> finite kappa/source-sector bridge               CLOSED
  -> G1-B1B d*u / PsiSharp / QW correspondence       OPEN
  -> G1-final QW_lambda|E_N = canonical matrix       OPEN
  -> canonical high-frequency falsifier              OPEN
  -> source form-core / lowest-eigenvalue transfer   OPEN
  -> fixed-aperture negative-bottom source theorem   OPEN
  -> canonical finite-negative exclusion             OPEN
  -> RH                                               OPEN
```

The detailed execution plan is maintained outside this README. This file states repository identity and merged theorem state; it is not a substitute for the current build-plan / handover document.

## Evidence and authority order

When documents disagree, use this order:

1. live GitHub head, Lean compiler, and CI;
2. `research/RHRC/CLAIM_REGISTRY.json` and `research/RHRC/routes/ROUTE_REGISTRY.json`;
3. the active route README, especially `research/RHRC/routes/R003_ccm_bridge/README.md`;
4. the current external build-plan / handover SSOT;
5. PR-specific settlement documents;
6. older route plans, numerical receipts, and historical audits.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).

## Post-green rule

Green is not the end of a research PR.

After every meaningful green result the project:

- verifies the exact checked head and theorem declarations;
- reads the successful proof and its assumptions;
- compares it with earlier attempts and route history;
- searches upstream and downstream implications;
- revisits previously failed routes whose prerequisites changed;
- tries to falsify new RH-relevant clues;
- updates route state without upgrading claims beyond what Lean proved.

RH remains OPEN unless the exact terminal RH theorem passes the full proof and claim-validation gates.

## Repository layout

```text
comparator/                      preserved upstream trusted-statement/comparator layer
Zeta23/                          Lean mathematics
Zeta23/ExceptionalZero/          R001/R002 theorem-bearing fork work
Zeta23/CCM/                      R003/R004 finite CCM/Weil formalization
research/RHRC/                   route control plane, source maps, audits, falsifiers, receipts
research/RHRC/routes/R001_*      exceptional-zero route
research/RHRC/routes/R002_*      multi-probe route
research/RHRC/routes/R003_*      CCM / finite Weil bridge
research/RHRC/routes/R004_*      displacement / prolate-structure diagnostics
UPSTREAM_BASELINE.json           immutable fork baseline
UPSTREAM_README.md               preserved pre-fork-facing README snapshot
UPSTREAM_AUDIT.md                preserved upstream audit snapshot
```

## Building and checking

The pinned Lean/Mathlib toolchain remains controlled by `lean-toolchain` and `lake-manifest.json`.

Useful checks include:

```bash
lake exe cache get
lake build
lake build Zeta23.ExceptionalZero
lake build Zeta23.CCM

python research/RHRC/tools/run_suite.py
python research/RHRC/routes/R003_ccm_bridge/check_source_normalization_firewall.py
python research/RHRC/routes/R004_prolate_v2/check_normalization_shift_invariants.py
```

The comparator instructions for the preserved upstream theorem surface remain in [comparator/README.md](comparator/README.md).

## Provenance

The fork preserves the inherited Apache-2.0 project and its upstream notices. See [NOTICE](NOTICE), [LICENSE](LICENSE), [UPSTREAM_BASELINE.json](UPSTREAM_BASELINE.json), and [FORK_NOTES.md](FORK_NOTES.md).

External numerical/source implementations under `research/RHRC/external/` are reference and falsification oracles only. They are forbidden from becoming Lean theorem dependencies.

## Current terminal status

```text
RIEMANN HYPOTHESIS: OPEN
```
