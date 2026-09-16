# Post-#195 parity-trajectory sharp-enclosure research delta

> **Claim firewall: RH remains OPEN.**
>
> This is a post-green research synthesis. It records executable finite research evidence; it does not move Lean theorem authority.

Exact research anchor:

```text
PR #195
validated research head = ef8af439b4723062061553bfee0ae3eba0205684
merged research commit = 380b0011ffa3fac9684ec05496e241b47878be69
validated research tree = cc403fc55454c0f865c17a36d971a9e7947f1a1a
research disposition = PARTIAL_TRAJECTORY_ORIENTATION
```

Theorem authority remains PR #184. Control semantic authority remains PR #117. Terminal claim remains `RH_OPEN`.

# What became formally true

No new Lean theorem was added by #195. The exact theorem authority remains the #184 Hermitian/log-cover/contact package. In particular, #195 does not prove source-specific remainder domination, global canonical injectivity, FB-05 closure, negative-root exclusion, or RH.

# What became research-certified

PR #195 adds and independently checks the complete fixed-Q canonical second-aperture jet

```text
M(L)   = pole(L)   - arch(L)   - prime(L)
M'(L)  = pole'(L)  - arch'(L)  - prime'(L)
M''(L) = pole''(L) - arch''(L) - prime''(L)
```

before parity restriction, so the same canonical production lineage yields

```text
e,e',e''
o,o',o''.
```

The dedicated implementation checker passed primitive, complete 7x7 matrix, scalar/predecessor, centered first-difference, centered second-difference, and inherited zero-von-Mangoldt seam checks. Finite differences remain implementation checks, not theorem authority.

The #193 baseline was replayed exactly:

```text
baseline classification = TRAJECTORY_RIGIDITY_UNRESOLVED
63 H1_UNRESOLVED
33 J_UNRESOLVED
0 J_NEGATIVE
0 J_POSITIVE
```

The new shared-cell A/B/C run returned:

```text
classification = PARTIAL_TRAJECTORY_ORIENTATION
96 evaluated cells
49 leaves
48 J_POSITIVE
48 J_UNRESOLVED
0 J_NEGATIVE
0 H1_UNRESOLVED
second_order_h1_recovery_count = 63
representation_conflict_count = 0
unresolved_span_count = 1
certified_t_fraction = 63/64
uniform_orientation = null
global_positive_hull = false
bounded_distinct_aperture_twin_exclusion = false
```

Method counts:

```text
A (#193 first-order Wronskian):
  0 J_POSITIVE
  33 J_UNRESOLVED
  63 H1_UNRESOLVED

B (direct log-slope):
  48 J_POSITIVE
  48 J_UNRESOLVED
  0 H1_UNRESOLVED

C (centered Wronskian transport):
  48 J_POSITIVE
  48 J_UNRESOLVED
  0 H1_UNRESOLVED
```

Thus second order completely removes the #193 H1 bottleneck in the frozen run, and B/C agree with no rigorous sign conflict. The surviving obstruction is a single unresolved orientation span covering the remaining 1/64 of the frozen trajectory parameter range.

# What changed

The post-#193 question was whether higher-order canonical transport could distinguish a mathematical fold from an interval-dependency failure. #195 answers part of that question:

```text
#193: H1 failure dominates and no finite-width J cell is signed.
#195: H1 failure is eliminated; 63/64 of the trajectory parameter range is covered by positive orientation; one orientation span remains unresolved.
```

No negative cell was certified. This is not a proof that no fold exists in the unresolved span.

The active bottleneck is therefore no longer parity positivity/H1 recovery. It is the residual finite-width orientation dependency inside one span.

# Upstream implications

The canonical `M''` evaluator is reusable research infrastructure. It should be treated as a production-jet backend rather than as a one-off #195 experiment.

For the inherited orientation quantity

```text
J = o'e - e'o
```

differentiation gives the exact algebraic cancellation

```text
J' = o''e - e''o.
```

Also, when `e>0` and `o>0`,

```text
(o/e)' = J/e^2
(log(o/e))' = J/(oe).
```

These identities suggest that parity-ratio/log-slope ordering is the natural structural object beneath P1/P2/J. They are DERIVED algebraic observations here, not new source-specific Lean theorems.

# Downstream implications

The 63/64 positive cover is strong bounded evidence that the canonical trajectory is locally one-sided over almost all of the frozen hull, but because `global_positive_hull = false`, the implication

```text
J>0 on full hull
 -> P2>0
 -> P1'>0
 -> bounded strict monotonicity
 -> distinct-aperture complete-seven-vector exclusion
```

is not yet available.

The remaining work is much smaller and better localized than after #193: identify why the single residual span is unresolved and whether the obstruction is representational or genuinely contains a zero/fold.

# Resurrected routes

The centered second-order route proposed after #181 is now validated infrastructure rather than a speculative next step. The old brute first-order subdivision route remains consumed.

The source-channel mechanism route is newly attractive because the surviving quantity has the simplified derivative

```text
J' = o''e - e''o.
```

A channel decomposition can test whether the observed orientation is driven by one source term, a stable interaction, or cancellation.

# New RH-relevant clues

**LEAD / HYPOTHESIS — parity-ratio monotonicity.** The finite #195 result is consistent with the canonical ratio `o/e` increasing across the frozen Q14 hull, but the remaining 1/64 span prevents promotion to a complete bounded result.

**LEAD / HYPOTHESIS — source-channel orientation mechanism.** Because `J'` loses the mixed first-derivative terms exactly, a source-channel decomposition of `o''e-e''o` may expose a smaller arithmetic inequality worth theoremizing.

**DERIVED — narrowing of the ambient-reflection problem.** If the final span is eventually certified positive, #190's identical seven-vector reflected ambiguity cannot be realized by two distinct apertures on this bounded canonical branch because P1 would be strictly monotone.

# Falsification checks

Before theoremizing the clue:

- inspect the exact remaining unresolved span rather than increasing precision/depth blindly;
- require any source-channel decomposition to reconstruct the direct canonical total exactly/rigorously;
- remember that `J'` is bilinear in source channels, so cross-channel terms cannot be discarded;
- treat any certified negative or zero-containing local interval as a route-changing result;
- test whether the apparent orientation depends on normalization or the frozen Q14 interval;
- do not infer arbitrary-Q behavior from the Q14 branch;
- check that any proposed source inequality is not merely FB-05/RH restated.

# Highest-leverage next moves

1. Synchronize the post-#195 state into the living SSOT/control docs without moving theorem authority.
2. Audit the remaining one-span orientation failure on the exact same frozen Q14 hull.
3. Decompose the canonical second-order orientation mechanism through pole/arch/prime source channels, including all cross-channel terms, and require exact reconstruction of the direct `J'` object.
4. If a stable mechanism appears, falsify it on inherited controls/adjacent canonical cells before Lean theoremization.
5. Only after a full bounded `J>0` cover exists, formalize the smallest abstract parity-ratio monotonicity bridge and then the source-specific premise.

# Standing questions

> Given everything now formally true, what becomes possible that was not possible before?

We can evaluate the complete canonical second-aperture jet and carry it through the same-state parity projection, so the residual trajectory obstruction can now be studied through curvature/source structure rather than only first-order interval subdivision.

> If this contains a clue toward RH, where does that clue propagate?

Source-channel/log-slope ordering would propagate to `J>0`, then bounded parity-ratio monotonicity, then canonical distinct-aperture reflected-twin exclusion, shrinking the admissible FB-05 counterexample space.

> What experiment or lemma most efficiently tells us whether the clue is real?

Explain or falsify the one remaining unresolved orientation span by decomposing the exact canonical second-order quantity `o''e-e''o` while preserving same-state reconstruction.

**RH remains OPEN.**