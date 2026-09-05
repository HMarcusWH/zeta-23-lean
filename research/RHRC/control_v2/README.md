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
- `retro/` — vocabulary-aware Git archaeology, optional external archive search, as-of replay and dead-route revival law.

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

### Archaeology

Searches all repository history reachable from the supplied anchor plus all text files in an optional archive. Historical hits remain clue provenance and require revalidation.

### Counterfactual replay

Searches only Git history reachable from the historical anchor. External archives additionally require `RETRO_ARCHIVE_MANIFEST.json`; files with unknown or later `available_from_utc` are excluded. This prevents hindsight leakage.

Example external archive manifest:

~~~json
{
  "sources": [
    {
      "path": "ICW_NSG_v1.txt",
      "source_family": "ICW_NSG",
      "source_version": "1.0",
      "authority": "HISTORICAL_ARCHITECTURE",
      "available_from_utc": "2026-08-01T00:00:00Z"
    }
  ]
}
~~~

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

`tools/run_suite.py` runs Control-v2 unit tests. The Python RHRC workflow checks out full Git history (`fetch-depth: 0`) so historical replay is actually available in CI. Router recommendations themselves are not assertion targets; only invariant failures are CI-fatal.

**RH remains OPEN.**
