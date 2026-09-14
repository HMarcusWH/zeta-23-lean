# Post-#174 q13 scalar-dependency frontier delta

> **Claim firewall: RH remains OPEN.**

This dated delta records the required Post-Green Research Pass after merged-green research PR #174. It is research-routing evidence, not theorem authority.

## Exact authority state

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

LATEST RESEARCH EVIDENCE
merged research PR = #174
validated research head = 2d9fc5a5f7d552afb893c871fe84c9ed61a60ac0
merged research commit = 946788f09c871de5133e2a8c8f5c94d7d69b521d
research tree = 2a22b83c4d5903158c036d38420d9ae79b7726f2
RHRC #1070 = SUCCESS
Permansson #843 = SUCCESS

CONTROL AUTHORITY
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

No Lean source changed in #174, so theorem authority remains #163.

## What became validated research truth

PR #174 consumes the q13/N2/K3/even scalarization target selected after #172/#173. For the exact theorem-aligned one-step geometry,

```text
predecessor N=2 -> dimension 1
successor K*=3  -> dimension 2
```

and in `[W|c]` coordinates

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]]
Delta_2(L) = a(L)d(L) - b(L)^2.
```

The deterministic checker locks the exact basis geometry and the H1/sign reduction:

```text
H1 <-> a(L) > 0
P(L) = Delta_2(L) / a(L) in H1 scope
sign P(L) = sign Delta_2(L) in H1 scope.
```

The physical interval is audited piecewise over Q=13,14,15. The seam checks preserve the production cutoff convention and verify overlap of the reduced scalar continuations at the relevant integer-log boundaries.

The floating scout sharpens the dangerous Q14 basin but finds no sampled negative state. The smallest sampled determinant occurs near

```text
L ~= 2.667148454185885

a_even                ~= +2.2951379574642772e-08
Delta_even            ~= +5.584546144549801e-17
normalized Delta_even ~= +1.89950549134347e-21
unit-shell pivot      ~= +5.793350415455644e-12
odd N=2 predecessor   ~= +6.103347988117847e-07
```

The sampled determinant minimum and sampled Schur-pivot minimum are nearby but not identical.

## Exact rigorous finite-method result

At 384-bit precision the adaptive direct scalar interval audit returns

```text
Q=13: positive width = 0, bad width = 0, H1-loss width = 0, unresolved width = 1
Q=14: positive width = 0, bad width = 0, H1-loss width = 0, unresolved width = 1
Q=15: positive width = 0, bad width = 0, H1-loss width = 0, unresolved width = 1
```

No H2/H3 bad interval is certified. No zero/contact theorem is produced. No strict-positive interval is certified. No shifted-state handoff is emitted.

`UNRESOLVED` remains exactly unresolved.

## What changed

The key methodological correction is stronger than the post-#167 warning.

#167 showed that direct whole-matrix Arb subdivision suffers severe dependency inflation. #174 then removes most of the finite-dimensional geometry by reducing the target to the exact scalar observables `a_even`, `Delta_even`, and odd-N2 ancestry. The direct scalar formulas nevertheless remain unresolved on every nonzero-width physical cell.

Therefore matrix dimension is not the sole cause of certification failure. The current direct canonical scalar representation itself carries enough repeated aperture dependence and cancellation to defeat naive interval subdivision.

This kills the strategy

```text
same direct scalar formulas + more precision/depth/leaves
```

as the current next move. A revival requires changed enclosure mathematics, not merely more of the same subdivision.

## Upstream implications

The earlier aperture-analytic work becomes relevant again.

PR #148 theoremized fixed-unit parameter holomorphy for the production archimedean cores on an explicit common strip. The research Arb backend still evaluates the corresponding real production quantities in a representation where `L` appears both in the integration endpoint and repeatedly inside the oscillatory frequency.

The substitution

```text
z = L*s,   0 <= s <= 1
```

is therefore a high-value research lead: the integration domain becomes fixed and factors such as `(2*pi*n/L)*(L*s)` collapse to `2*pi*n*s`. This may materially reduce dependency inflation and make aperture differentiation/variation bounds cleaner.

This is a **LEAD / HYPOTHESIS**, not a theorem or a certified improvement yet. The first obligation is numerical/interval equivalence against the existing evaluator plus a measurable enclosure-width improvement on the dangerous Q14 basin.

## Downstream implications

The next research target is no longer to discover the 2x2 scalar reduction; that reduction is consumed infrastructure.

The next target is to resolve the scalar minimum/contact problem using a changed enclosure representation while retaining the exact theorem-aligned geometry and physical cutoff semantics.

Candidate mechanisms, in order of increasing machinery, are:

1. fixed-unit pullback of the production archimedean integrals;
2. certified variation/derivative bounds for `a(L)` and `Delta_2(L)`;
3. local centered Taylor models around the dangerous Q14 basin;
4. interval Newton/Krawczyk isolation for roots of `Delta_2'` or possible zero contact;
5. analytic scalar factorization/root exclusion if the preceding steps expose one.

The desired classification remains:

```text
A. H1 loss: a(L) <= 0 somewhere
B. strict bad successor: a(L) > 0 and Delta_2(L) < 0 somewhere
C. zero/contact: a(L) > 0 and Delta_2(L) = 0 somewhere
D. strict barrier: a(L) > 0 and Delta_2(L) > 0 everywhere
```

Case C must not be inferred merely because an interval enclosure contains zero.

## Resurrected route

The #148 fixed-unit analytic parameterization is worth reusing as research infrastructure for #174's interval-dependency problem. This does not revive global Loewner monotonicity or global Schur monotonicity. It uses analytic parameterization locally to tighten scalar enclosures.

## New reusable classifications

### OBS-047 — scalarization alone does not eliminate canonical interval dependency

The exact reduction

```text
full canonical matrix -> theorem-aligned 2x2 block -> a,b,d -> Delta_2
```

simplifies the geometry but does not by itself produce useful whole-cell direct Arb enclosures. Future interval work must distinguish geometric dimension reduction from analytic dependency reduction.

### OBS-048 — determinant and Schur-pivot minima are distinct targets

Even in H1 where `P=Delta_2/a`, minimizing `Delta_2` and minimizing `P` are different optimization problems because `a(L)` varies. The #174 floating minima are nearby but nonidentical. Future minimum/root isolation must name the scalar being controlled.

### DR-026 candidate — brute scalar subdivision of the direct q13 formulas

Treat repeated adaptive subdivision of the same direct `a(L), Delta_2(L)` formulas as sufficient to classify the physical q13 cells.

**Status:** dead as the current certification strategy after #174.

**Revival requirement:** change the enclosure representation or add new analytic control. More precision, depth, or leaf budget alone is not a route change.

The permanent ledgers should absorb these classifications in the next synchronization edit without rewriting older history.

## Falsification checks for the next implementation PR

- new fixed-unit evaluator must agree with the existing production evaluator at rigorously chosen points;
- physical Q=13/14/15 seam semantics must remain intact;
- von Mangoldt prime powers must remain intact;
- opposite-parity N=2 ancestry must remain tracked;
- determinant and pivot minima must remain distinct diagnostics;
- interval-width improvement must be measured rather than assumed;
- global derivative sign must not be assumed;
- a local stationary-point isolation must not be promoted to whole-cell positivity without outer-region control;
- zero-containing intervals must not be promoted to root existence;
- a positive q13 whole-cell certificate is still only a finite method/structure result unless its controlling inequality generalizes to the arbitrary retained first-bad state.

## Highest-leverage next move

Build a research PR that first benchmarks a fixed-unit/dependency-reduced production evaluator against the existing q13 scalar evaluator, then only if the interval widths improve, add derivative/Taylor/Newton machinery to isolate the dangerous Q14 minimum or zero-contact set.

The first acceptance gate is therefore methodological:

```text
old evaluator agrees with new evaluator at certified points
AND
new representation gives materially tighter enclosures on the dangerous basin.
```

Only after that gate should the project invest in higher derivative machinery.

## Standing questions

> Given everything theoremized through #163 and validated experimentally through #174, what analytic representation preserves the exact q13 scalar geometry while reducing interval dependency enough to decide the minimum/contact problem?

> If the q13 barrier is ultimately positive, what arithmetic inequality causes that positivity and does it survive other q/N/parity states?

> If it crosses or touches zero, can the resulting finite state be replayed through the #166 shifted-state discriminator and composed with #161/#163?

FB-05 remains OPEN. Negative-root exclusion remains OPEN. **RH remains OPEN.**
