# RHRC research delta — post-#176 fixed-unit method acceptance and Q14 stationary frontier

> **Claim firewall: RH remains OPEN.**
>
> This is a research-state synchronization document. It does not promote #176 research code or finite Arb evidence to Lean theorem authority.

## Authority ledger

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #176
validated research head = c6f53131b91b18aff2a50a6db2ddaa2761e7e5aa
PR integration commit tested by Actions = ad6c904cf38c64d61c7990b3b6e87eec27ad0064
merged research commit = 96cccf715c02ed2bd4ae58f8362180020ae90854
research tree = 28bd302c17a6128e538a3510917dafb670f6dce8
RHRC #1072 = SUCCESS
Permansson #845 = SUCCESS

CONTROL AUTHORITY
control semantic anchor = PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The theorem and research anchors remain deliberately separate.

## What #176 actually ran

PR #176 implements an independent fixed-unit Arb path for the q13/N2/K3 production laboratory while retaining the existing direct `[0,L]` evaluator as the baseline comparator.

The exact RHRC #1072 pipeline ran, in order:

```text
check_post175_fb05_q13_fixed_unit_enclosure_scope.py
probe_post175_fb05_q13_fixed_unit_enclosure_scope.py
certify_post175_fb05_q13_fixed_unit_enclosure_scope.py
```

The validation layer checks agreement of the direct and fixed-unit representations for:

- archimedean primitives;
- the complete `7x7` canonical source matrix used by the N=3 ambient calculation;
- theorem-aligned even scalar restrictions;
- odd N=2 predecessor ancestry;
- physical-cell seam behavior;
- zero-weight inertness.

The frozen benchmark then uses six primary Q14 boxes:

```text
determinant_minimum_r2^-12
determinant_minimum_r2^-16
determinant_minimum_r2^-20
pivot_minimum_r2^-12
pivot_minimum_r2^-16
pivot_minimum_r2^-20
```

The predeclared material width-gain factor is `2.0`.

## Exact #176 finite result

The exact CI certifier reports

```text
status = PASS
method_classification = FIXED_UNIT_METHOD_ACCEPTED
```

and all six primary Q14 boxes report

```text
delta_strictly_narrower = true
delta_material_gain = true
```

Therefore the fixed-unit representation passes the predeclared finite method-selection gate on the frozen q13/Q14 laboratory.

### Classification

**EXPERIMENTAL SIGNAL / RIGOROUS FINITE METHOD EVIDENCE.**

It is legitimate to conclude that, on this frozen benchmark, the fixed-unit pullback materially reduces the interval width of the theorem-aligned determinant observable relative to the direct evaluator while enclosing the same finite object.

It is **not** legitimate to conclude any of the following:

```text
Delta_2(L) > 0
Delta_2(L) >= 0
Delta_2 has a stationary point
Delta_2 has a unique stationary point
q13/N2/K3/even is positive on the whole physical cell
the retained hypothetical off-line-zero state lies in this q13 cell
FB-05 is closed
negative roots are excluded
RH
```

## What changed relative to #174

#174 established that exact scalarization alone did not cure the dependency problem: every nonzero-width direct scalar cell in Q=13/14/15 remained unresolved under the configured audit.

#176 answers the immediate representation-selection question that #174 left open. The fixed-unit pullback is now the **preferred research enclosure representation for this finite q13/Q14 laboratory**, because it passed the predeclared agreement and width-improvement gate.

The direct production evaluator is not discarded. It remains an independent comparator and a valuable falsification path.

## OBS-049 — fixed-unit pullback materially reduces q13/Q14 determinant enclosure width on the frozen benchmark

**Status:** RIGOROUS FINITE RESEARCH / METHOD EVIDENCE FROM PR #176; NOT LEAN THEOREM AUTHORITY.

The direct `[0,L]` archimedean representation was a substantive contributor to the observed enclosure inflation on the frozen Q14 determinant benchmark. Moving to a fixed integration domain and removing repeated `L` dependence from the oscillatory phase materially tightens the determinant enclosure in all six primary boxes under the predeclared factor-2 routing criterion.

**Permanent scope warning:** this is not a global conditioning theorem and should not be generalized to arbitrary q/N/parity states without fresh evidence.

## Validation caveat exposed by review

A post-implementation review identified a software-hardening gap in the standalone certifier: it accepts a supplied benchmark JSON whose status is `PASS` without independently rebinding every schedule-defining field to the frozen fixture.

For the exact #176 CI result, this does not invalidate the recorded method classification: the workflow generated the benchmark from the frozen fixture immediately before invoking the certifier, and the logs show all six intended primary boxes were present and accepted.

Still, a future replay-hardening patch should make the certifier reject stale or hand-modified benchmark schedules that omit or relabel required boxes. This is a validation-engineering debt, not a mathematical theorem or counterexample.

## Upstream implications

The #148 fixed-unit aperture work has acquired a new role beyond holomorphy infrastructure. Its fixed-domain parameterization now has executable evidence of better interval conditioning on a cancellation-sensitive canonical observable.

That makes it reasonable to revisit the analytic differentiation of the fixed-unit primitives rather than differentiating the old moving-domain representation. The likely reusable objects are

```text
alpha_L'(n)
beta_L'(n)
gamma_L'(n)
```

followed by theorem-aligned contractions

```text
a'(L), b'(L), d'(L)
Delta_2'(L) = a'(L)d(L) + a(L)d'(L) - 2b(L)b'(L).
```

This is a research lead, not yet a theorem.

## Downstream implications

The next finite problem is no longer “which representation should we benchmark?” It is:

> Does the fixed-unit representation remain sufficiently well conditioned after differentiation to certify the local Q14 stationary structure of `Delta_2`?

A high-information route is:

1. implement analytic fixed-unit first derivatives of the production primitives;
2. independently compare them against high-precision centered finite differences at frozen points;
3. bound `Delta_2'` on outer Q14 subregions;
4. if the derivative changes sign or remains unresolved only locally, isolate that local stationary basin;
5. only then use interval Newton/Krawczyk and centered Taylor/second-derivative bounds to classify the local minimum/contact.

The determinant and Schur pivot must remain separate optimization targets because `P=Delta_2/a` in H1 and `a(L)` varies.

If a strict bad state appears, immediately replay it through the #166 shifted-state discriminator and compose with the same-state #161/#163 theorem package.

If the finite q13 cell is instead certified strictly positive, do not theoremize the finite fact in isolation. First extract the analytic/arithmetic inequality that makes the barrier turn away from zero and test it on other q/N/parity states.

## Resurrected routes

The earlier #145-#150 analytic aperture line is worth revisiting in a narrower form:

```text
analytic aperture dependence
  -> explicit fixed-unit derivative identities
  -> rigorous local derivative bounds
  -> stationary/root/minimum exclusion on a scalar canonical observable.
```

This does **not** resurrect global Loewner or Schur monotonicity. The target is local, scalar and cancellation-preserving.

## New RH-relevant clues

### LEAD / HYPOTHESIS — cancellation-preserving derivative rigidity

The q13 barrier sits near a cancellation scale of roughly `1e-12` while the underlying channels are many orders larger. #176 indicates that an appropriate analytic coordinate change can materially reduce interval inflation without changing the object.

A possible deeper clue is that the decisive arithmetic information may live not in a sign of any individual channel but in a stable derivative relation among the fully recombined canonical channels.

If such a relation generalizes across first-bad cells, it could provide the independent canonical restriction required by FB-05 without merely restating successor positivity.

This is explicitly a hypothesis.

## Falsification checks

The next route should fail closed against each of these possibilities:

- derivative formulas disagree with independent finite differences;
- value-level conditioning gain disappears after differentiation;
- `Delta_2'` remains dependency-dominated everywhere;
- determinant and pivot stationary points are accidentally conflated;
- apparent monotonicity exists only on one sampled side of the basin;
- a zero-containing interval is mistaken for a certified contact;
- physical Q-cell seam behavior is lost;
- prime powers or von Mangoldt weights are altered;
- opposite-parity N=2 ancestry is dropped;
- the finite q13 result is silently promoted to an arbitrary first-bad theorem.

## Highest-leverage next move

Build the next research PR as a **derivative discriminator**, not as a promised stationary-point proof.

Suggested scope:

```text
R003: discriminate fixed-unit Q14 determinant derivatives and stationary basin
```

First green criterion:

```text
analytic fixed-unit derivative evaluator agrees with independent numerical checks
AND
rigorous Delta_2' enclosures are demonstrably useful near/outside the Q14 basin.
```

Only if that criterion passes should the same PR or its successor attempt certified stationary-point isolation and local Taylor minimum/contact classification.

## Standing questions

Given everything now formally true through #163 and experimentally validated through #176:

1. Does fixed-unit dependency reduction survive differentiation?
2. Can `Delta_2'` be signed on both sides of one rigorously isolated Q14 stationary region?
3. If a local minimum is isolated, is `Delta_2` negative, zero, or strictly positive there?
4. If positive, what cancellation-preserving arithmetic inequality forces the turn?
5. Does that inequality survive other q/N/parity states and the actual retained first-bad interfaces?
6. Can it compose with #161/#163 without assuming successor positivity in disguise?
7. What closes simultaneous parity badness and odd-selected coverage?

**RH remains OPEN.**
