# RHRC Control v2 — adaptive research routing + retroactive research memory

> **Authority firewall:** Control v2 is a research-routing diagnostic. It cannot promote Lean theorems, write claim authority, emit the terminal RH answer, or turn numerical/search output into RH evidence. **RH remains OPEN.**

## Purpose

Control v2 adds two capabilities around the existing RHRC theorem stack:

1. **Forward routing.** Rank admissible next research moves by explicit cost, information gain, falsification value, closure value, residual risk and dependency debt. Every serious route declares a first-break test.
2. **Retroactive archaeology and replay.** Search repository history using concept aliases, optionally search a normalized external archive, and support `as_of` counterfactual replay so old states cannot see future clues.

The controller answers **where to look next**, never **what is mathematically true**. Lean/CI and the machine claim surfaces retain theorem/claim authority.

## Current theorem anchor

`CONTROL_STATE.json` is the living control-plane anchor. For this version it records merged green PR #115 (`a2fecffbef8fed1fdfba373aa5756acf2618e2a1`), where E1 cubic-shell incidence is in the authoritative CCM/ExceptionalZero import closure.

## Main objects

- `ACTION_REGISTRY.json` — current research actions, deterministic score inputs, first-break declarations and control requirements.
- `CONTROL_BOUNDARY.json` — physical authority cap for the controller.
- `schemas.py` / `state.py` — typed control state.
- `router.py` — deterministic fail-closed action ranking.
- `deformation_budget.py` — RH-native deformation-budget diagnostic with Decimal arithmetic and explicit tail certificates.
- `first_break.py` — MCM-style cheapest-decisive-falsifier ordering.
- `retro/` — vocabulary-aware Git archaeology, optional external archive ingestion/search, as-of replay and dead-route revival law.

## FFBBP v1.6 assurance integration

The existing RUN42C profile and `FFBBP_REFERENCE.json` remain frozen historical qualification authority. The additive `ffbbp/v16_*` modules expose v1.6 assurance contracts without inheriting RUN42C qualification:

- diagnostic vs decision commutation;
- residual horizon contracts;
- explicit witness visibility/margin/masking checks;
- fail-closed reduction assurance gates.

A small local residual is not a horizon certificate. Numerical closeness is not decision commutation.

## Deformation-budget diagnostic

The first RH-native adapter tracks the proposed quantities

~~~text
mu_N       spectral-floor lower information
q_N        new-shell stiffness information
beta_N     shell/predecessor coupling information
D_N        certified one-step downward-deformation upper bound
R_N        certified remaining tail-deformation upper bound
H_N        certified headroom lower bound = mu_lower - R_upper
~~~

The certified one-step shortcut is

~~~text
D_N <= beta_upper^2 / gap_lower
~~~

and is available only when `gap_lower > 0` is itself certified. A `PRUNE` decision requires a certified infinite-tail upper bound and strictly positive certified headroom. A finite prefix sum or fitted tail is not enough.

## Retro modes

### Archaeology — exhaustive by default

Searches **all Git refs with commits predating the theorem anchor**, not only main-reachable history. This is deliberate: older unmerged implementation branches may contain useful clues. Concept aliases recover vocabulary drift such as `deformation budget -> residual headroom / detectability budget / distortion schedule / evolving canvas`.

The normal controller uses exhaustive archaeology with no hit/commit cap. `--quick-retro` exists for interactive exploration, but its receipts are marked incomplete and therefore cannot admit history-sensitive routes.

### Counterfactual replay

Searches only Git history reachable from the historical anchor. External archives additionally require `RETRO_ARCHIVE_MANIFEST.json`; files with unknown/later `available_from_utc` or a mismatched SHA-256 are excluded/rejected. This prevents hindsight leakage and source mutation.

## External-history ingestion

CI cannot query private document libraries directly. Historical papers/implementation notes are first normalized to UTF-8 text/code, then ingested with a hash-bound availability manifest:

~~~bash
python research/RHRC/control_v2/retro/ingest.py ICW_NSG_v1.txt \
  --archive-root /path/to/rhrc-history \
  --source-family ICW_NSG \
  --source-version 1.0 \
  --authority HISTORICAL_ARCHITECTURE \
  --available-from-utc 2026-08-01T00:00:00Z
~~~

The ingestion tool copies the source under a SHA-prefixed name and maintains `RETRO_ARCHIVE_MANIFEST.json` deterministically.

## Usage

From the repository root:

~~~bash
python research/RHRC/control_v2/run_control.py
~~~

With an ingested external history corpus:

~~~bash
python research/RHRC/control_v2/run_control.py \
  --archive-root /path/to/rhrc-history \
  --output /tmp/RHRC_CONTROL_V2.json
~~~

The output is a route certificate plus retro-search receipt IDs. It always carries `RH_OPEN` and a no-theorem-authority firewall.

## Dead-route law

`DEAD_ROUTES.md` remains authoritative historical failure memory. `retro/revival.py` encodes the existing rule: a dead/quarantined route cannot be silently resurrected. A `RevivalRecord` must state the original blocker, what premise changed and evidence for that change.

## CI

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history (`fetch-depth: 0`) and performs a real-history Control-v2 smoke run. Router recommendations themselves are not assertion targets; authority, completeness and leakage invariants are CI-fatal.

**RH remains OPEN.**
