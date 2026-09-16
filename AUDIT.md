# RHRC formal audit — theorem authority through PR #184; research evidence through PR #195

> **RH remains OPEN.**

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Authority split

```text
THEOREM AUTHORITY
PR #184
head  = a756494ebe7e2530715e996b9a9a341fbe07c683
merge = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
tree  = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH EVIDENCE
PR #195
head  = ef8af439b4723062061553bfee0ae3eba0205684
merge = 380b0011ffa3fac9684ec05496e241b47878be69
tree  = cc403fc55454c0f865c17a36d971a9e7947f1a1a
research disposition = PARTIAL_TRAJECTORY_ORIENTATION

CONTROL SEMANTIC AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

## Formal theorem state

No Lean theorem has been added after PR #184. The formal production-facing package still proves, in its exact scopes:

```text
Hermitian P = d - |b|^2/a
contact-local determinant/pivot derivative orientation transfer under H1
full frozen parity production family M~(t) = -t I + R~(t)
exact fixed-cell bridge to parityCompressedCanonical
N2 predecessor/canonical-shell reconstruction
canonical shell != 0
predecessor ⟂ shell
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0
```

Still not proved: source-specific remainder domination, contact existence/uniqueness, opposing first-bad orientation on the same state, first-bad exclusion, negative-root exclusion or RH.

## Research audit: #186 -> #195

### #186 -> #190 — ambient selector surface consumed

#186 returned `DOMINATION_SIGNAL_MIXED`. #188 froze the normalization-safe selector surface. #189 showed every selector individually ambiently separable from the target sign. #190 then certified the exact reflected pair with identical complete seven-vector and identical nonboundary threshold signature but opposite target signs:

```text
JOINT_EXACT_VECTOR_SEPARABLE
JOINT_THRESHOLD_SIGNATURE_SEPARABLE
```

Thus all 127 nonempty selector subsets are insufficient in that ambient algebra.

### #192 — canonical production realizability ladder

The Layer 0 -> Layer 5 canonical production realizability audit was executed:

```text
Layer 0  AMBIENT_NORMALIZED
Layer 1  SOURCE_CHANNEL_COUPLING
Layer 2  SCALAR_APERTURE
Layer 3  COMMON_ARCH_APERTURE
Layer 4  COMMON_SCHUR_GEOMETRY
Layer 5  CANONICAL_PRODUCTION
```

The specific #190 negative-scalar witness is excluded by the exact positive scalar-aperture identity. An adversarial exact positive-scalar reflected construction survives that identity. Bounded full canonical replay remains `UNRESOLVED` for general twin existence; the six primary production states report 0/15 seven-vector overlaps. Search failure is not nonexistence.

### #193 — parity trajectory rigidity

PR #193 reuses the fixed-Q Q14 trajectory and inherited P1/P2 graph:

```text
J = o'e - e'o
P2 = L*J/(o*e)
sign(P1') = sign(P2) = sign(J)   under L,e,o>0
```

All six exact inherited primary centers certify `e>0`, `o>0`, `J>0`, `P2>0`, but the frozen finite-width cover reports:

```text
96 evaluated cells
63 H1_UNRESOLVED
33 J_UNRESOLVED
0 J_NEGATIVE
0 J_POSITIVE
TRAJECTORY_RIGIDITY_UNRESOLVED
```

This does not locate a fold and does not falsify trajectory monotonicity.

### #195 — sharp second-order trajectory enclosure

PR #195 keeps the exact same frozen Q14 hull, Q/N/K/parity, 384-bit precision, depth and cell budget. It adds a validated analytic second derivative for the complete canonical fixed-Q source,

```text
M'' = pole'' - arch'' - prime'',
```

and transports one same-state `(M,M',M'')` lineage to `e,e',e''` and `o,o',o''`.

The #193 baseline is replayed exactly. The new shared-cell A/B/C result is:

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

Methods B and C both return 48 positive and 48 unresolved cell evaluations with no H1 failures and no sign conflicts. The higher-order representation therefore completely removes the #193 H1 bottleneck in the frozen experiment and narrows the surviving problem to one unresolved orientation span.

The result does **not** certify full-hull `J>0`.

## Current post-green frontier

Do not repeat #192, resume selector mining, or simply turn up #195 precision/depth on the same dependency graph.

On the **same frozen Q14 hull**, use the now-validated canonical second-order jet to inspect the residual orientation mechanism. The key identity is

```text
J' = o''e - e''o.
```

The next experiment should decompose the pole/arch/prime contributions, including all bilinear cross-channel terms, and require rigorous reconstruction of the independently evaluated total. The point is to determine whether the remaining 1/64 span is unresolved because of interval dependency or because the canonical trajectory genuinely approaches/crosses zero there.

A future complete signed cover with `J>0` would imply bounded strict monotonicity of P1 and exclude distinct-aperture complete-seven-vector twins on that branch. #195 does not yet supply that consequence.

## Claim firewall

```text
#184 theorem package
  -/-> source-specific sign law

#190 joint ambient separability
  -/-> canonical arithmetic separability

#192 specific-witness exclusion
  -/-> general reflected-class exclusion

6/6 positive #193 centers
  -/-> J>0 on the hull

63/64 positive #195 coverage
  -/-> 64/64 full-hull positivity

PARTIAL_TRAJECTORY_ORIENTATION
  -/-> bounded twin exclusion
  -/-> FB-05 closure
```

Global Schur monotonicity remains quarantined. Negative-root exclusion remains OPEN. The terminal zeta/Mathlib seam remains OPEN. **RH remains OPEN.**