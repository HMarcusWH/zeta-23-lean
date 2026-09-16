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
merged research PR = #197
validated research head = 2d936f9764abdfeaa82127d5c834c6c3e429da25
merged research commit = 162df6ce8bc13a816937d747f2965bff6764fad0
validated research tree = 97f6372a4c7c131006b4abc090c86767b9e99990
research disposition = GLOBAL_MONOTONE_ORIENTATION

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

Research green is not theorem promotion.

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
      -> J = o'e - e'o
      -> 6/6 exact inherited centers: e>0, o>0, J>0, P2>0
      -> 63/96 H1_UNRESOLVED
      -> 33/96 J_UNRESOLVED
      -> TRAJECTORY_RIGIDITY_UNRESOLVED

#195  canonical second-order sharp parity-trajectory enclosure
      -> complete M,M',M'' backend independently validated
      -> second_order_h1_recovery_count = 63
      -> 48 J_POSITIVE, 48 J_UNRESOLVED
      -> 0 J_NEGATIVE, 0 H1_UNRESOLVED
      -> unresolved_span_count = 1
      -> certified_t_fraction = 63/64
      -> PARTIAL_TRAJECTORY_ORIENTATION
      -> historical global_positive_hull = false

#197  unique post-#195 budget-leaf replay
      -> exactly one 1/64 MAX_CELL_BUDGET leaf evaluated once
      -> A = J_UNRESOLVED
      -> B = J_POSITIVE
      -> C = J_POSITIVE
      -> GLOBAL_MONOTONE_ORIENTATION
      -> uniform orientation = J_POSITIVE
      -> certified t-fraction = 1
      -> global_positive_hull = true
      -> bounded_distinct_aperture_twin_exclusion = true
```

The #195 `PARTIAL_TRAJECTORY_ORIENTATION` / `63/64` result remains historical evidence. PR #197 completes the exact frozen Q14 cover at research-certification level; it does not create a Lean theorem.

## Current active path — FB-05 / canonical parity-ordering mechanism

The bounded sign-recovery question on the frozen Q14 hull is consumed. The live question is now **why** the complete canonical trajectory is positively oriented and whether that reason generalizes to the exact retained first-bad/contact state.

Do not resume selector mining, threshold refits, the #192 Layer 0 -> Layer 5 replay, or blind precision/depth escalation.

Stay on the same canonical source lineage and inspect

```text
J = o'e - e'o
J' = o''e - e''o
```

through the pole/arch/prime source channels, retaining every bilinear cross-channel term and requiring rigorous reconstruction of the independent direct total. The goal is to identify or falsify a compact canonical arithmetic mechanism behind

```text
(o/e)' = J/e^2 > 0
(log(o/e))' = J/(o*e) > 0.
```

## Current open obligations

```text
OBS-056 residual frozen-Q14 orientation span                           CLOSED in exact frozen Q14 research scope
OBS-057 bounded-to-structural parity-ordering mechanism gap            OPEN / ACTIVE
source-channel mechanism audit of J' = o''e - e''o                    OPEN / ACTIVE
arbitrary-state source law implying the parity ordering                OPEN
actual N2 production remainder scalar derivative witnesses             OPEN
actual production HasDerivAt Schur identity                            OPEN
same-state first-bad opposing contact orientation                      OPEN
sourceMoment <-> M4 canonical-state rigidity                           OPEN
simultaneous even/odd bad exclusion                                    OPEN
odd-selected first-bad branch closure                                  OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero terminal seam                               OPEN
RiemannHypothesis                                                       OPEN
```

## Permanent firewalls

- compiler/CI evidence outranks prose;
- theorem authority remains #184 until a later Lean-bearing PR passes theorem gates;
- #190 closes the frozen selector surface only in its declared ambient normalized algebra;
- #192 excludes the specific #190 witness but not the general reflected class;
- #193 exact-center positivity is not finite-width monotonicity;
- historical #195 `PARTIAL_TRAJECTORY_ORIENTATION` and `63/64` must not be rewritten away;
- #197 complete frozen-Q14 coverage is rigorous bounded research, not arbitrary-Q or FB-05 theorem authority;
- bounded distinct-aperture twin exclusion is not global canonical injectivity;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

See `research/RHRC/CURRENT_RESEARCH_PLAN.md`, `research/RHRC/RESEARCH_LEADS.md`, `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`, and `research/RHRC/RESEARCH_LEADS_POST_197_Q14_RESIDUAL_CELL_REPLAY_DELTA.md` for the current execution route.