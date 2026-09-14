# Post-#178 derivative-unresolved / centered-enclosure frontier delta

> **Claim firewall: RH remains OPEN.**
>
> This document records the post-green research state after merged research PR #178. It is a research-routing synthesis, not Lean theorem authority.

## Authority snapshot

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

LATEST RESEARCH EVIDENCE
merged research PR = #178
validated research head = 28df43faed0db8c0f12a25525df6c28467ce5b07
merged research commit = fb2a181ce0d95d90396ead7730e7bf365616a153
research tree = 96ab14953e9e8bff5245953082db8a6471648614
RHRC #1074 = SUCCESS
Permansson #847 = SUCCESS

CONTROL AUTHORITY
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

No Lean source changed in #178. Theorem authority therefore remains #163.

## What #178 validated in the research layer

PR #178 differentiates the complete fixed-Q canonical source

```text
M(L) = pole(L) - arch(L) - prime(L)
M'(L) = pole'(L) - arch'(L) - prime'(L)
```

inside the physical fixed-cutoff cells and propagates that derivative through the existing theorem-aligned `[W|c]` geometry to

```text
a', b', d'
Delta_2' = a'd + ad' - 2bb'.
```

The implementation checker independently compares analytic derivatives against centered finite differences of the already-green value evaluators at frozen Q13/Q14/Q15 points. It checks primitive derivatives, every upper-triangular entry of the complete 7x7 matrix derivative, theorem-aligned `a',b',d',Delta_2'`, and the odd-N2 predecessor derivative.

Derivative seam continuation is required only at the zero-von-Mangoldt seams `log 14` and `log 15`. No false derivative matching condition is imposed at the nonzero entering-atom seams `log 13` or `log 16`.

PR #178 also closes the #176 standalone replay-hardening debt: the #176 certifier now reconstructs the frozen benchmark schedule from its fixture and rejects missing, duplicate, relabeled, extra, or dyadically altered boxes. The new checker contains adversarial mutations for those cases.

## Exact #178 finite research result

The frozen derivative schedule contains six primary Q14 side boxes:

```text
det_left_o2^-10_r2^-13
det_right_o2^-10_r2^-13
det_left_o2^-13_r2^-16
det_right_o2^-13_r2^-16
det_left_o2^-16_r2^-19
det_right_o2^-16_r2^-19
```

The exact RHRC #1074 certifier returned:

```text
derivative disposition = DERIVATIVE_UNRESOLVED
orientation = NO_CERTIFIED_PRIMARY_DERIVATIVE_SIGN

left_negative_labels  = []
left_positive_labels  = []
right_negative_labels = []
right_positive_labels = []

derived_stationary_existence_if_continuity_used = false
uniqueness_claim = false
```

Separately:

```text
value event = NO_BAD_OR_H1_LOSS_INTERVAL_CERTIFIED
bad_labels = []
h1_loss_labels = []
```

This is a rigorous finite method result. It does **not** say that `Delta_2' = 0` on the primary boxes, and it does not prove stationary existence, contact, badness, strict positivity, or uniqueness.

## What changed

#176 established that the fixed-unit pullback materially improves the value-level `Delta_2` enclosure on the frozen Q14 benchmark.

#178 establishes a different fact: the same representation, when differentiated and evaluated by the raw assembled interval formula

```text
Delta_2' = a'd + ad' - 2bb',
```

does not yet certify a sign on any of the six primary side boxes.

Therefore value-level interval conditioning and derivative-level interval conditioning must be treated as separate problems.

## OBS-050 — fixed-unit value conditioning does not automatically yield derivative sign discrimination

**Status:** RIGOROUS FINITE RESEARCH OBSERVATION.

PR #176 materially narrows the frozen Q14 determinant intervals. PR #178 validates the complete fixed-unit canonical derivative implementation, but all six primary raw `Delta_2'` interval boxes remain sign-unresolved.

Consequently:

```text
fixed-unit value-width gain
  -/-> useful raw-box derivative sign enclosure.
```

In particular:

```text
DERIVATIVE_UNRESOLVED
  -/-> Delta_2' = 0
  -/-> stationary existence
  -/-> contact
  -/-> bad successor
  -/-> H1 loss.
```

## DR-027 candidate — raw assembled derivative boxes

The derivative route itself remains live. What #178 falsifies as the default next move is repeating the same raw assembled interval expression on more or smaller boxes without changing the dependency structure.

```text
raw interval evaluation of
  a'd + ad' - 2bb'
+ more precision / more subdivision
```

is not a substantive new strategy after #178.

A revival requires a changed enclosure representation, for example:

- rigorous point-ball derivative diagnostics;
- a correlation-preserving centered/mean-value form;
- a local Taylor enclosure using a bounded second derivative;
- an exact H1 Schur-factorized derivative representation;
- another analytic factorization that reduces repeated-parameter dependency.

## Upstream implications

The fixed-unit parameterization remains the preferred finite research representation. #178 does not refute the analytic derivative identities; it validates them operationally and reveals that the next bottleneck is how correlated value/derivative data are enclosed.

The natural next comparison is between the exact raw determinant derivative

```text
Delta_2' = a'd + ad' - 2bb'
```

and, in H1 where `P=Delta_2/a`, the exact factorization

```text
Delta_2 = a P
Delta_2' = a'P + aP'.
```

The determinant and pivot minima remain distinct optimization targets. The factorization is proposed only as an alternative enclosure graph for the same determinant derivative; it is not a revival of global Schur monotonicity.

## Downstream implications

Before implementing interval Newton/Krawczyk, the project should distinguish two possibilities:

1. the pointwise derivative has the expected left/right sign but interval dependency destroys that sign on boxes;
2. even rigorous point balls for `Delta_2'` are too close to zero to sign reliably.

Those lead to different repairs.

If rigorous point balls already show left-negative / right-positive behavior, then a centered mean-value/Taylor enclosure becomes the highest-leverage next experiment:

```text
Delta_2'(L)
  = Delta_2'(L0) + (L-L0) * Delta_2''(xi).
```

Only after a genuine two-sided derivative bracket is certified should interval Newton/Krawczyk be used to isolate `Delta_2' = 0`, and only after isolation should `Delta_2` at the stationary region be classified.

## Resurrected routes

The following remain viable **conditional** downstream tools:

```text
centered mean-value derivative enclosure
local Taylor model
interval Newton on Delta_2'
Krawczyk isolation
stationary-point value classification
```

They were premature after #174 and still remain premature if point derivatives themselves are sign-unresolved.

Global aperture Loewner monotonicity and global minimizing-Schur monotonicity remain quarantined.

## New RH-relevant clue

**LEAD / HYPOTHESIS:** the q13 barrier may be controlled by a smooth, cancellation-preserving local rigidity that is invisible to channelwise or raw interval factorization.

The evidence is not a sign theorem. The clue is methodological: #170-#178 repeatedly show that preserving the complete canonical cancellation structure matters more than assigning signs to individual channels.

If a centered/factorized derivative representation succeeds and the controlling inequality survives other q/N/parity states, it may expose an independent arithmetic restriction suitable for FB-05. If it only certifies one q13 finite cell, it remains a finite method/structure result.

## Falsification checks for the next research PR

- compute rigorous point `Delta_2'` balls at all primary and control centers before adding second derivatives;
- keep determinant-center and pivot-center diagnostics separate;
- compare at least two exact derivative representations where H1 permits;
- preserve physical Q=13/14/15 seam semantics and von Mangoldt prime powers;
- preserve odd N=2 ancestry tracking;
- keep the direct value evaluator as an independent baseline;
- do not infer a stationary point from a zero-containing derivative interval;
- do not assume `Delta_2'' > 0`;
- if second-derivative boxes are dependency-limited, stop rather than returning to brute subdivision;
- if a certified bad interval appears, replay it immediately through the post-#166/#161/#163 same-state machinery.

## Highest-leverage next move

Build a research PR that benchmarks **correlation-preserving Q14 determinant derivative enclosures** in this order:

```text
1. rigorous point Delta_2' scout at frozen centers
2. raw-vs-Schur-factorized derivative comparison in H1
3. only if point orientation is visible: Delta_2'' + centered mean-value/Taylor enclosure
4. only if a two-sided bracket emerges: interval Newton/Krawczyk
```

Green outcomes should include method falsification such as centered/factorized representations remaining unresolved. The next PR must discriminate methods rather than require a desired sign.

## Claim firewall

- theorem authority remains #163;
- #178 research green is not theorem promotion;
- derivative implementation validity is not a derivative theorem in Lean;
- `DERIVATIVE_UNRESOLVED` is not zero evidence;
- no stationary existence or uniqueness was derived in #178;
- no bad interval or H1-loss interval was certified;
- q13 whole-cell positivity/contact remains OPEN;
- simultaneous parity badness remains OPEN;
- odd-selected closure remains OPEN;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**