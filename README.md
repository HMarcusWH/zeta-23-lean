# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

Live GitHub head + exact compiler/CI evidence are authoritative dynamically.

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #195
validated research head = ef8af439b4723062061553bfee0ae3eba0205684
merged research commit = 380b0011ffa3fac9684ec05496e241b47878be69
validated research tree = cc403fc55454c0f865c17a36d971a9e7947f1a1a
research disposition = PARTIAL_TRAJECTORY_ORIENTATION

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The theorem, research and control anchors are intentionally separate. Research green is not theorem promotion.

## Theorem frontier

The compiler-validated theorem ladder remains through PR #184. Lean proves the complex-Hermitian 2x2 Schur calculus, the frozen production family on the logarithmic cover, the exact fixed-cell bridge to `parityCompressedCanonical`, N2 predecessor/canonical-shell reconstruction and orthogonality, and

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

PR #184 does **not** prove source-specific remainder domination, contact existence/uniqueness, an opposing first-bad orientation, negative-root exclusion or RH.

## Completed research history

```text
#186  broad production-remainder domination
      -> DOMINATION_SIGNAL_MIXED

#188  frozen normalization-safe selector audit
#189  every individual frozen selector ambiently separable from target sign

#190  complete seven-dimensional strong selector vector
      -> JOINT_EXACT_VECTOR_SEPARABLE
      -> JOINT_THRESHOLD_SIGNATURE_SEPARABLE
      -> all 127 nonempty subsets insufficient in ambient algebra

#192  Layer 0 -> Layer 5 canonical production realizability audit
      -> specific negative-scalar #190 witness excluded by exact scalar-aperture identity
      -> adversarial positive-scalar reflected construction survives that identity
      -> six-primary production replay has 0/15 seven-vector overlaps
      -> general reflected-twin mechanism remains UNRESOLVED

#193  fixed-Q Q14 parity-trajectory rigidity audit
      -> J = o'e - e'o for inherited P1/P2 orientation
      -> 6/6 exact inherited centers: e>0, o>0, J>0, P2>0
      -> 63/96 H1_UNRESOLVED
      -> 33/96 J_UNRESOLVED
      -> 0 J_NEGATIVE, 0 J_POSITIVE
      -> TRAJECTORY_RIGIDITY_UNRESOLVED

#195  canonical second-order sharp parity-trajectory enclosure
      -> complete M,M',M'' backend independently validated
      -> second_order_h1_recovery_count = 63
      -> 48 J_POSITIVE, 48 J_UNRESOLVED
      -> 0 J_NEGATIVE, 0 H1_UNRESOLVED
      -> representation_conflict_count = 0
      -> unresolved_span_count = 1
      -> certified_t_fraction = 63/64
      -> PARTIAL_TRAJECTORY_ORIENTATION
```

The #195 result is a strong representation improvement, not a complete hull sign theorem. `global_positive_hull = false` and `bounded_distinct_aperture_twin_exclusion = false` remain binding outputs.

## Current active path — FB-05 / residual trajectory mechanism

PR #195 completely removes the #193 H1 obstruction on the frozen run. The remaining issue is a single unresolved orientation span.

Do not:

```text
resume selector mining or threshold refits
repeat the #192 Layer 0 -> Layer 5 replay
infer full-hull J>0 from 63/64 coverage
blindly increase #195 precision/depth on the same dependency graph
```

Stay on the same frozen Q14 hull, same inherited Q/N/K/parity state and no target labels. Use the newly validated second-order jet and the exact identity

```text
J' = o''e - e''o
```

to audit the source mechanism behind the residual orientation. The next research build should decompose pole/arch/prime contributions, including all bilinear cross-channel terms, and rigorously reconstruct the direct canonical total.

If the final span is eventually certified positive, then under `L,e,o>0`:

```text
P2 = L*J/(o*e)
J>0 -> P1' > 0
```

so P1 is strictly monotone on that bounded canonical branch and distinct apertures cannot share the complete seven-vector there. That remains bounded research evidence until separately theoremized.

## Current open obligations

```text
residual one-span Q14 orientation mechanism                               OPEN / ACTIVE
source-channel audit of J' = o''e - e''o                                 OPEN / ACTIVE
J(L) > 0 on the full inherited Q14 hull                                  OPEN
actual N2 production remainder scalar derivative witnesses               OPEN
actual production HasDerivAt Schur identity                               OPEN
same-state first-bad opposing contact orientation                         OPEN
sourceMoment <-> M4 canonical-state rigidity                              OPEN
simultaneous even/odd bad exclusion                                       OPEN
odd-selected first-bad branch closure                                     OPEN
negative-root exclusion                                                    OPEN
outside-strip/trivial-zero terminal seam                                  OPEN
RiemannHypothesis                                                          OPEN
```

## Permanent firewalls

- compiler/CI evidence outranks prose;
- theorem authority remains #184 until a later Lean-bearing PR passes theorem gates;
- #190 closes the frozen selector surface only in its declared ambient normalized algebra;
- #192 excludes the specific #190 witness but not the general reflected class;
- #193 exact-center positivity is not finite-width monotonicity;
- `TRAJECTORY_RIGIDITY_UNRESOLVED` was a first-order representation result, not a fold;
- #195's `PARTIAL_TRAJECTORY_ORIENTATION` is not a complete hull theorem;
- 63/64 certified positive coverage is not 64/64;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

See `research/RHRC/CURRENT_RESEARCH_PLAN.md`, `research/RHRC/RESEARCH_LEADS.md`, `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`, and `research/RHRC/RESEARCH_LEADS_POST_195_PARITY_TRAJECTORY_SHARP_ENCLOSURE_DELTA.md` for the current execution route.