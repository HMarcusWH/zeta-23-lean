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
merged research PR = #201
validated research head = be5b98dfce12777436bc40b39a37b04669ae4311
merged research commit = 319db6f68f65bdcffc0657c03bea76502da59a57
validated research tree = 840a2e8b0bf690507bc3385fbe122210e6d32c7a
research disposition = DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED

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
      -> EXACT_TWIN_SURVIVES at ambient/source-coupling layers
      -> specific negative-scalar witness EXACT_TWIN_EXCLUDED_BY_IDENTITY
      -> general reflected-twin mechanism remains UNRESOLVED

#193  fixed-Q Q14 parity-trajectory rigidity audit
      -> J = o'e - e'o
      -> 6/6 exact inherited centers: e>0, o>0, J>0, P2>0
      -> TRAJECTORY_RIGIDITY_UNRESOLVED
      -> Do **not** infer this from points

#195  canonical second-order sharp parity-trajectory enclosure
      -> complete M,M',M'' backend independently validated
      -> exact identity J' = o''e - e''o
      -> PARTIAL_TRAJECTORY_ORIENTATION / certified t-fraction = 63/64

#197  unique post-#195 budget-leaf replay
      -> GLOBAL_MONOTONE_ORIENTATION
      -> uniform orientation = J_POSITIVE
      -> certified t-fraction = 1
      -> global_positive_hull = true
      -> bounded_distinct_aperture_twin_exclusion = true

#199  canonical source-mechanism audit on exact #197 cover
      -> direct Method-C J remains J_POSITIVE on all 49 leaves
      -> SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
      -> no unique collapsed uniform lock

#201  cancellation-preserving discrepancy-first audit
      -> D = pole + prime_signed and A = direct_arch_signed
         formed at M,M',M'' level before parity restriction/transport
      -> paired M/M'/M'' reconstruction PASS
      -> direct #197 J_POSITIVE replay remains intact
      -> paired_source_sum_positive_leaf_count = 0
      -> paired_source_sum_unresolved_leaf_count = 49
      -> DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED
      -> selected_uniform_lock_group = null
      -> NO_UNIQUE_PRIMARY_LOCK
```

PR #201 advances the research-evidence anchor because it consumes the theorem-motivated paired-channel escape left open by #199. It does **not** weaken the bounded #197 sign certificate. Instead it shows that even upstream pole-prime pairing does not preserve enough interval correlation to expose the already-certified direct sign.

## Current active path — FB-05 / full-composite parity mechanism

Do not resume selector mining, threshold refits, the #192 replay, blind precision/depth escalation, the consumed #199 independent source split, or nearby linear source regroupings merely to search for a sign.

Source chopping has now been tested in three materially different representations:

```text
four-way source split                         -> dependency unresolved
collapsed pole/direct-arch/prime split       -> dependency unresolved
upstream pole-prime discrepancy/direct-arch  -> dependency unresolved
```

The next research action is therefore a **higher-level exact correlated parity identity** of the assembled canonical object. The first candidate family is a normalized parity-gap/full-composite formulation built from the same canonical even/odd predecessor levels, with a cheap exact-center falsification gate before any full 49-leaf run.

`(o/e)' = J/e^2` and `(log(o/e))' = J/(oe)` remain DERIVED equivalent reformulations under `e,o>0`; merely reproving ratio monotonicity would not count as a new mechanism.

## Current open obligations

```text
OBS-056 residual frozen-Q14 orientation span                           CLOSED in exact frozen Q14 research scope
OBS-057 bounded-to-structural parity-ordering mechanism gap            OPEN / FURTHER NARROWED
OBS-058 cancellation-preserving source representation gap              OPEN / NARROWED THROUGH #201
higher-level full-composite parity mechanism audit                     OPEN / ACTIVE
arbitrary-state source/parity law implying the ordering                OPEN
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
- `M~(t)=-tI+R~(t)` remains the production/log-cover theorem interface;
- **Do not count them as two independent** when two proposed constraints instantiate the same mechanism;
- #190 closes the frozen selector surface only in its declared ambient normalized algebra;
- #192 excludes the specific #190 witness but not the general reflected class;
- #193 exact-center positivity is not finite-width monotonicity;
- historical #195 `PARTIAL_TRAJECTORY_ORIENTATION` and `63/64` remain preserved;
- #197 complete frozen-Q14 coverage is rigorous bounded research, not arbitrary-Q or FB-05 theorem authority;
- #199 source-decomposition nonresolution does not downgrade #197 direct `J_POSITIVE`;
- #201 discrepancy-representation nonresolution also does not downgrade #197 direct `J_POSITIVE`;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

## Post-#203 authoritative synchronization

This section supersedes the older "latest research" and "next experiment" wording above while preserving it as auditable history.

```text
LATEST RESEARCH EVIDENCE
PR #203
head  = c8196830a8b49e657b28d36b364e1cff68c568d6
merge = ab660e812a78d482145eadc3e42d186a63fa812b
tree  = 7360e366fe8d623ef63ca902c23522bb72935848
research disposition = COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED

center_kill_switch_survives = false
full_cover_executed = false
completed_leaf_count = 0
control_transfer_status = PATTERN_FALSIFIED_BEFORE_FULL_COVER
```

PR #203 faithfully executes the preregistered full-composite Pair-A falsifier after repairing an implementation-only exact-rational conversion bug. The repaired parity contrast independently reconstructs `G = O-E`, `G' = O'-E'`, and `G'' = O''-E''`; the frozen sign pattern `E > 0`, `G > 0`, `G' >= 0`, `E' <= 0` then fails the six-center kill-switch. The expensive 49-leaf audit is therefore correctly not run.

This does **not** weaken PR #197 `GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE`, and it does not prove all Pair-A mathematics impossible. It consumes the planned simple Pair-A representation-engineering sequence. The next highest-information research route is **Pair D — same-state two-parity squeeze**. **Pair B — negative-index separation versus localized critical-line sampling rigidity** is secondary.

Theorem authority remains PR #184, the selected formal first break remains `E4A4-SCHUR-FB-05`, R003 remains `DISCOVERY`, negative-root exclusion remains OPEN, and **RH remains OPEN.**

See `research/RHRC/RESEARCH_LEADS_POST_203_Q14_COMPOSITE_PARITY_GAP_DELTA.md` for the current post-green state.