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
merged research PR = #199
validated research head = fabe301c95277345f0efe764252ce1c1213a4112
merged research commit = 27dda545b7ccdb2870088ebaf317d85e3d999555
validated research tree = 85eb8ea25d240c4a9c339262bdc611fae881f7f0
research disposition = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED

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

#197  unique post-#195 budget-leaf replay
      -> exactly one 1/64 MAX_CELL_BUDGET leaf evaluated once
      -> A = J_UNRESOLVED; B = J_POSITIVE; C = J_POSITIVE
      -> GLOBAL_MONOTONE_ORIENTATION
      -> uniform orientation = J_POSITIVE
      -> certified t-fraction = 1
      -> global_positive_hull = true
      -> bounded_distinct_aperture_twin_exclusion = true

#199  canonical source-mechanism audit on exact #197 cover
      -> exact #197 GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE replayed
      -> four-way source split = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
      -> collapsed three-way split = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
      -> selected_collapsed_uniform_lock_group = null
      -> control_transfer_status = NO_UNIQUE_COLLAPSED_UNIFORM_LOCK
      -> direct bounded J_POSITIVE remains intact
```

PR #199 advances the research-evidence anchor because it consumes the next mechanism audit. It does **not** supersede or weaken the bounded #197 sign certificate; it shows that the present source-separated interval graph is not dependency-preserving enough to expose the already-certified sign.

## Current active path — FB-05 / cancellation-preserving parity mechanism

Do not resume selector mining, threshold refits, the #192 replay, blind precision/depth escalation, or the already-consumed #199 independent source split.

The next research action is a representation change that preserves known pole-prime cancellation before enclosure:

```text
D = pole + prime_signed
A = direct_arch_signed
M = D + A
```

Construct `D,D',D''` and `A,A',A''` before parity restriction and interval transport. Then form only the discrepancy-self, discrepancy/arch cross, and arch-self parity-Wronskian interactions and require their sum to rigorously reconstruct the same independent direct Method-C `J` on every inherited #197 leaf.

This is a theorem-motivated LEAD / HYPOTHESIS. Existing Lean work proves useful pole-prime discrepancy identities; it does not yet prove that discrepancy-first parity transport forces `J>0`.

## Current open obligations

```text
OBS-056 residual frozen-Q14 orientation span                           CLOSED in exact frozen Q14 research scope
OBS-057 bounded-to-structural parity-ordering mechanism gap            OPEN / NARROWED
OBS-058 cancellation-preserving source representation gap              OPEN / ACTIVE
discrepancy-first parity mechanism audit                               OPEN / ACTIVE
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
- historical #195 `PARTIAL_TRAJECTORY_ORIENTATION` and `63/64` remain preserved;
- #197 complete frozen-Q14 coverage is rigorous bounded research, not arbitrary-Q or FB-05 theorem authority;
- #199 source-decomposition nonresolution does not downgrade #197 direct `J_POSITIVE`;
- bounded distinct-aperture twin exclusion is not global canonical injectivity;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

See `research/RHRC/CURRENT_RESEARCH_PLAN.md`, `research/RHRC/RESEARCH_LEADS.md`, `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`, and `research/RHRC/RESEARCH_LEADS_POST_199_Q14_SOURCE_DECOMPOSITION_DELTA.md` for the current execution route.