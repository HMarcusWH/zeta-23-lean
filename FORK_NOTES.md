# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

## Theorem package remains #184

Lean theorem authority still ends at the complex-Hermitian/log-cover package:

```text
P = d - |b|^2/a
M~(t) = -t I + R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0
```

with exact fixed-cell attachment to production and N2 predecessor/canonical-shell reconstruction plus orthogonality. The arithmetic premise needed for the sign step remains open.

## Research progression after #184

```text
#186  broad remainder domination -> DOMINATION_SIGNAL_MIXED
#188  frozen normalization-safe selector audit
#189  every individual frozen selector abstractly separable from target sign
#190  complete seven-selector vector jointly separable from target sign
#192  Layer 0 -> Layer 5 canonical production realizability audit executed
#193  fixed-Q Q14 parity-trajectory rigidity audit -> TRAJECTORY_RIGIDITY_UNRESOLVED
#195  canonical second-order sharp enclosure -> PARTIAL_TRAJECTORY_ORIENTATION
```

#192 excludes the specific negative-scalar #190 witness once the exact scalar-aperture identity is imposed, but an adversarial positive-scalar reflected pair survives that identity and the bounded canonical replay does not prove general nonexistence. Among the six primary production states, the replay has 0/15 seven-vector overlaps; that is a bounded structural signal only.

#193 then evaluates the inherited parity trajectory using

```text
J = o'e - e'o
P2 = L*J/(o*e)
```

and certifies `e>0`, `o>0`, `J>0`, `P2>0` at all six exact inherited centers. Its first-order finite-width cover nevertheless returns 63 `H1_UNRESOLVED`, 33 `J_UNRESOLVED`, no signed J cells, and overall `TRAJECTORY_RIGIDITY_UNRESOLVED`.

#195 keeps the exact same frozen Q14 hull and validates the complete fixed-Q canonical second-aperture jet `M,M',M''`. Its shared-cell A/B/C result is:

```text
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
PARTIAL_TRAJECTORY_ORIENTATION
```

Thus #195 completely removes the frozen H1 obstruction but does not sign the final 1/64 span.

## Current route

The higher-order enclosure is now completed research history, not the next experiment. The live bottleneck is the mechanism behind the single unresolved orientation span.

Do not resume selector mining, repeat the #192 replay, infer a full-hull sign from `63/64`, or merely raise the #195 subdivision/precision budget. On the **same frozen Q14 hull**, use

```text
J' = o''e - e''o
```

and audit the canonical pole/arch/prime source decomposition, retaining all bilinear cross-channel terms and requiring rigorous reconstruction of the direct canonical total.

The research question is whether the residual span is unresolved because of interval dependency/cancellation or because the actual canonical trajectory reaches a zero/fold there.

## Permanent warnings

- theorem authority remains #184;
- research authority through #195 remains executable/finite research evidence;
- #190 killed selector composition only in its declared ambient algebra;
- #192 killed the specific reflected witness, not the general reflected class;
- #193 did not find a fold;
- #195 eliminates H1 failure on the frozen run but leaves one J span unresolved;
- `63/64` positive coverage is not a complete monotonicity theorem;
- `global_positive_hull = false` is binding;
- `J>0` on the full Q14 hull remains OPEN;
- global Schur monotonicity remains quarantined;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**
