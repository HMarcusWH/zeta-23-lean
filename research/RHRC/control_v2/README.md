# RHRC Control v2 — deterministic evidence-gated research routing + retroactive memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 adds two capabilities around the existing RHRC theorem stack:

1. **Forward routing.** Rank admissible next research moves by explicit cost, information gain, falsification value, closure value, residual risk and dependency debt. Every serious route declares a first-break test.
2. **Retroactive archaeology and replay.** Search repository history using concept aliases, optionally search a normalized external archive, and support `as_of` counterfactual replay so old states cannot see future clues.

The current router is intentionally deterministic. Evidence completeness controls admissibility, while the configured score inputs determine ordering. Retro hit content does not silently alter route scores.

The controller answers **where to look next**, never **what is mathematically true**. Lean/CI and the machine claim surfaces retain theorem/claim authority.

## Separate theorem and control anchors

`CONTROL_STATE.json` records two distinct anchors:

```text
theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
```

PR #119 is the current merged theorem authority: exact canonical negative secular root iff negative-shift eigenmode. PR #117 remains the latest merged green Control-v2 authority because #118/#119 changed theorem files but not control semantics.

## Current routed frontier

`ACTION_REGISTRY.json` now routes from `FIRST_BAD_RIGIDITY_E3_B`.

Primary theorem actions:

```text
E3-B1 projected predecessor symmetry / shifted coercivity
E3-B2 exact pointwise quotient-secular <-> explicit-Schur bridge
E4-A zero resonance / parity shifted-nullity
E3-B3 theorem-backed predecessor-floor deformation inequality
E3-C resolvent monotonicity / root-count control
negative-root exclusion only after the preceding structure is available
```

The deformation-budget paper test remains parallel diagnostic research.

The controller must preserve one critical post-#119 distinction: the exact #119 `cubicSecularScalar` is the quotient coordinate of the full residual. It is not yet theorem-identified pointwise with the older explicit Schur inner-product expression. Sign/monotonicity work on the explicit scalar cannot be promoted to the exact #119 root detector until E3-B2 closes that bridge.

## Main objects

- `ACTION_REGISTRY.json` — current research actions, deterministic score inputs, first-break declarations and control requirements.
- `CONTROL_BOUNDARY.json` — physical authority cap for the controller.
- `CONTROL_STATE.json` — separate merged theorem/control anchors.
- `schemas.py` / `state.py` — typed theorem/control anchors and control state.
- `router.py` — deterministic fail-closed action ranking with explicit score formula and candidate diagnostics.
- `deformation_budget.py` — RH-native deformation-budget diagnostic with Decimal arithmetic, exact prefix coverage and assured tail certificates.
- `first_break.py` — MCM-style cheapest-decisive-falsifier ordering.
- `retro/` — vocabulary-aware Git archaeology, optional external archive ingestion/search, as-of replay and dead-route revival law.

## FFBBP v1.6 assurance integration

The existing RUN42C profile and `FFBBP_REFERENCE.json` remain frozen historical qualification authority. The additive `ffbbp/v16_*` modules expose v1.6 assurance contracts without inheriting RUN42C qualification:

- diagnostic vs decision commutation;
- residual horizon contracts;
- explicit witness visibility/margin/masking checks;
- fail-closed reduction assurance gates.

A small local residual is not a horizon certificate. Numerical closeness is not decision commutation.

## Deformation-budget hardening

The RH-native adapter tracks the proposed quantities

```text
mu_N       spectral-floor lower information
q_N        new-shell stiffness information
beta_N     shell/predecessor coupling information
D_N        certified one-step downward-deformation upper bound
R_N        certified remaining tail-deformation upper bound
H_N        certified headroom lower bound = mu_lower - R_upper
```

The safe one-step shortcut is

```text
D_N <= beta_upper^2 / gap_lower
```

and is available only when `gap_lower > 0` is independently certified.

A complete `TailBudgetCertificate` requires:

1. exact sorted contiguous prefix coverage `N, ..., M-1` with one typed `StepUpperBound` per step;
2. an explicit numeric tail upper bound;
3. a passed FFBBP v1.6 `HorizonCertificate` targeting `remaining_deformation_budget` and carrying a propagated upper bound no larger than the recorded tail bound;
4. declared trust-region validity.

A positive numeric headroom is not enough by itself. `PRUNE` is produced only by the combined fail-closed gate after the complete assured tail is present. If a reduced model is used for a decision-bearing calculation, passed decision commutation is additionally required.

A finite prefix sum, fitted tail or small local residual is not enough.

## Post-#119 deformation alignment rule

The deformation quantities must remain aligned with the theorem-backed E3 definitions.

The expected theorem ancestry is now

```text
#119 exact secular equivalence
  -> E3-B1 metric/resolvent control
  -> E3-B2 explicit scalar bridge
  -> E3-B3 certified predecessor-floor one-step inequality
  -> only then decision-bearing deformation bounds.
```

If a future theorem uses a lower predecessor floor `mu`, the diagnostic gap must use the same theorem-backed `mu` and shell stiffness convention. The controller may not mix an empirical spectral floor with a theorem statement and call the result certified.

## Zero-resonance routing rule

Global-first-bad gives predecessor nonnegativity, not strict positivity. Therefore `ker A` may be nontrivial and the shifted resolvent may be singular as `lam -> 0-`.

Control-v2 now treats these as high-information first breaks:

```text
prove shifted-nullity difference from rank-at-most-one parity defect
probe/prove whether Bc is orthogonal to ker A
```

This is a theorem/discovery routing question only. No kernel-decoupling statement is currently proved.

## Retro modes

### Archaeology — exhaustive within the declared Git paths

The normal archaeology mode searches **all Git refs with commits predating the theorem anchor within the declared search paths**. The default paths are

```text
research/RHRC
Zeta23
```

Those paths are recorded in the retro receipt and included in its hash. Therefore `ALL_REFS_BEFORE_ANCHOR_IN_DECLARED_PATHS` must not be paraphrased as "every repository byte".

The deformation-budget alias set intentionally excludes generic standalone terms such as `fold`, `rupture` and `slack`; the first real-history run showed that these produced overwhelming false-positive volume. Admission-quality archaeology favors specific conceptual aliases such as `residual headroom`, `detectability budget`, `distortion schedule` and `evolving canvas`.

The normal controller uses exhaustive archaeology with no hit/commit cap. `--quick-retro` exists for interactive exploration, but its receipts are marked incomplete and therefore cannot admit history-sensitive routes.

### Counterfactual replay

Searches only Git history reachable from the historical anchor, again within the declared search paths. External archives additionally require `RETRO_ARCHIVE_MANIFEST.json`; files with unknown/later `available_from_utc` or a mismatched SHA-256 are excluded/rejected. This prevents hindsight leakage and source mutation.

## External-history ingestion

CI cannot query private document libraries directly. Historical papers/implementation notes are first normalized to UTF-8 text/code, then ingested with a hash-bound availability manifest:

```bash
python research/RHRC/control_v2/retro/ingest.py ICW_NSG_v1.txt \
  --archive-root /path/to/rhrc-history \
  --source-family ICW_NSG \
  --source-version 1.0 \
  --authority HISTORICAL_ARCHITECTURE \
  --available-from-utc 2026-08-01T00:00:00Z
```

The ingestion tool copies the source under a SHA-prefixed name and maintains `RETRO_ARCHIVE_MANIFEST.json` deterministically.

## Usage

From the repository root:

```bash
python research/RHRC/control_v2/run_control.py
```

With an ingested external history corpus:

```bash
python research/RHRC/control_v2/run_control.py \
  --archive-root /path/to/rhrc-history \
  --output /tmp/RHRC_CONTROL_V2.json
```

The output is a route certificate plus retro-search receipt IDs. It always carries `RH_OPEN`, theorem/control anchors and a no-theorem-authority firewall.

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. `retro/revival.py` encodes the existing rule: a dead/quarantined route cannot be silently resurrected. A `RevivalRecord` must state the original blocker, what premise changed and evidence for that change.

DR-010 remains dead. The current exact N-flow / first-bad / secular route does not use fitted small commutators, spectral-gap heuristics or eigenvector convergence.

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history (`fetch-depth: 0`) and performs a real-history Control-v2 smoke run. Router recommendations themselves are not assertion targets; authority, completeness, leakage, exact interval coverage and assurance invariants are CI-fatal.

Detailed current post-green research implications: `../RESEARCH_LEADS_POST_119_DELTA.md`.

**RH remains OPEN.**