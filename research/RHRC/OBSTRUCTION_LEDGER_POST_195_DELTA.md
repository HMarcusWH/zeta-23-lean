# Obstruction ledger supplement after PR #195

> **RH remains OPEN.**

This supplement preserves the historical obstruction ancestry and records how #195 narrows, but does not close, the parity-trajectory obstruction.

## OBS-055 — first-order centered parity-trajectory enclosure insufficiency

Historical state from PR #193:

```text
63 H1_UNRESOLVED
33 J_UNRESOLVED
0 J_NEGATIVE
0 J_POSITIVE
TRAJECTORY_RIGIDITY_UNRESOLVED
```

Interpretation: the first-order centered parity-trajectory enclosure could not propagate the positive exact-center orientation across any nonzero-width certified J cell. It did not falsify monotonicity and did not locate a fold.

## Post-#195 status: OBS-055 NARROWED

PR #195 keeps the exact same frozen Q14 hull, Q/N/K/parity, precision, depth and cell budget, adds a validated canonical second-aperture jet, and compares shared-cell representations A/B/C.

Executable outcome:

```text
classification = PARTIAL_TRAJECTORY_ORIENTATION
48 J_POSITIVE
48 J_UNRESOLVED
0 J_NEGATIVE
0 H1_UNRESOLVED
second_order_h1_recovery_count = 63
representation_conflict_count = 0
unresolved_span_count = 1
certified_t_fraction = 63/64
global_positive_hull = false
bounded_distinct_aperture_twin_exclusion = false
```

Therefore the H1 portion of OBS-055 is **resolved on the frozen #195 experiment**: every cell evaluated by the sharp second-order methods keeps the required parity positivity/H1 scope.

The orientation portion is **not closed**. One contiguous span remains unresolved, and no theorem certifies its sign.

## OBS-056 — residual one-span canonical trajectory orientation dependency

**Status:** OPEN / ACTIVE RESEARCH OBSTRUCTION.

Statement:

> On the exact frozen post-#195 Q14 trajectory, the validated direct-log-slope and centered-Wronskian second-order representations certify positive orientation over 63/64 of the trajectory parameter range, with zero certified negative cells and no representation conflicts, but one residual span remains unable to exclude `J=0` at the frozen budget. It is unresolved whether this is remaining interval dependency or genuine local trajectory behavior.

Evidence:

```text
B: 48 J_POSITIVE, 48 J_UNRESOLVED, 0 H1_UNRESOLVED
C: 48 J_POSITIVE, 48 J_UNRESOLVED, 0 H1_UNRESOLVED
representation_conflict_count = 0
unresolved_span_count = 1
certified_t_fraction = 63/64
```

The classification is `PARTIAL_TRAJECTORY_ORIENTATION`, not `GLOBAL_MONOTONE_ORIENTATION`.

## What would close OBS-056

Any one of the following, on the exact declared scope, would be decisive:

1. a rigorous positive enclosure of the final span, yielding a complete signed Q14 hull cover;
2. a rigorous negative or zero-containing local witness showing that global positive orientation is false on the hull;
3. an exact canonical structural inequality that controls the final span and is independently verified against the direct production evaluator.

Merely increasing precision/depth on the same dependency graph is not considered a new mechanism.

## Preferred next diagnostic

Use the now-validated canonical second-order production jet to inspect

```text
J' = o''e - e''o
```

by pole/arch/prime source channel, including all bilinear cross-channel terms, while requiring rigorous reconstruction of the direct canonical total. The objective is to identify whether the residual orientation is controlled by a stable source mechanism or by cancellation.

## Historical relation

`OBS-054` remains the ambient-selector insufficiency obstruction established around #190. `OBS-055` remains historical evidence that the first-order trajectory representation was inadequate. #195 narrows the live obstruction to `OBS-056`; it does not erase the earlier records.

## Claim firewall

```text
63/64 certified positive
  -/-> full-hull positivity

0 certified negative cells
  -/-> proof that no negative/fold point exists

H1 fully recovered in #195
  -/-> J sign on the final span

PARTIAL_TRAJECTORY_ORIENTATION
  -/-> bounded distinct-aperture twin exclusion
  -/-> FB-05 closure
  -/-> negative-root exclusion
  -/-> RH
```

**RH remains OPEN.**