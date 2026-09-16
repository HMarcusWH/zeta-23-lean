# RHRC formal audit — theorem authority through PR #184; research evidence through PR #201

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
PR #201
head  = be5b98dfce12777436bc40b39a37b04669ae4311
merge = 319db6f68f65bdcffc0657c03bea76502da59a57
tree  = 840a2e8b0bf690507bc3385fbe122210e6d32c7a
research disposition = DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED

CONTROL SEMANTIC AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

## Formal theorem state

No Lean theorem has been added after PR #184. The formal package still proves the Hermitian Schur/contact algebra, frozen parity production/log-cover family, exact fixed-cell production bridge, N2 predecessor/canonical-shell geometry, and the conditional decomposition

```text
M~(t)=-tI+R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

Still not proved: source-specific domination, contact existence/uniqueness, same-state opposing first-bad orientation, first-bad exclusion, negative-root exclusion or RH.

## Research audit: #186 -> #201

### #186 -> #190 — ambient selector surface consumed

PR #186 returned `DOMINATION_SIGNAL_MIXED`. PR #188 froze the normalization-safe selector family. PR #189 showed individual ambient separability. PR #190 then established `JOINT_EXACT_VECTOR_SEPARABLE` and `JOINT_THRESHOLD_SIGNATURE_SEPARABLE`, so all 127 nonempty selector subsets are insufficient in the audited ambient normalized algebra.

### #192 — canonical production realizability

The Layer 0 -> Layer 5 canonical production realizability ladder was executed. `EXACT_TWIN_SURVIVES` records the reflected mechanism surviving the early ambient/source-coupling layers; `EXACT_TWIN_EXCLUDED_BY_IDENTITY` records exclusion of the specific negative-scalar witness by the exact scalar-aperture identity. The general reflected class remains `UNRESOLVED`.

### #193 — first-order parity trajectory

```text
J = o'e - e'o
P2 = L*J/(o*e)
sign(P1') = sign(P2) = sign(J) under L,e,o>0
```

All six exact inherited centers satisfy `e>0`, `o>0`, `J>0`, `P2>0`, but the first-order finite-width result was `TRAJECTORY_RIGIDITY_UNRESOLVED`. **Do not infer this from points:** exact-center positivity did not establish finite-width monotonicity.

### #195 — second-order sharp enclosure

Historical exact result:

```text
J' = o''e - e''o
PARTIAL_TRAJECTORY_ORIENTATION
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
```

### #197 — unique residual-cell replay

The unique inherited `MAX_CELL_BUDGET` leaf is evaluated once with the unchanged evaluator:

```text
A = J_UNRESOLVED
B = J_POSITIVE
C = J_POSITIVE
GLOBAL_MONOTONE_ORIENTATION
uniform orientation = J_POSITIVE
certified t-fraction = 1
global_positive_hull = true
bounded_distinct_aperture_twin_exclusion = true
```

This remains a complete signed Arb interval cover of the declared frozen Q14 domain, hence `RIGOROUS BOUNDED RESEARCH`.

### #199 — source-mechanism audit

PR #199 first replays the exact #197 49-leaf complete positive cover. It then validates four-way and collapsed source-interaction reconstruction against independent direct Method C.

```text
mechanism_classification = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
four_way_classification = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
collapsed_three_way_classification = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
selected_collapsed_uniform_lock_group = null
control_transfer_status = NO_UNIQUE_COLLAPSED_UNIFORM_LOCK
```

This is a representation/dependency diagnosis, not a loss of direct `J_POSITIVE`.

### #201 — cancellation-preserving discrepancy-first audit

PR #201 tests the explicit escape left open after #199. It constructs

```text
D = pole + prime_signed
A = direct_arch_signed
M = D + A
```

at matrix `M,M',M''` level **before** parity restriction and centered second-order interval transport. The paired matrix, first-derivative and second-derivative reconstructions all pass, and the direct #197 `GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE` replay remains intact.

The final certified result is:

```text
completed_leaf_count = 49
paired_source_sum_positive_leaf_count = 0
paired_source_sum_unresolved_leaf_count = 49
mechanism_classification = DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED
selected_uniform_lock_group = null
control_transfer_status = NO_UNIQUE_PRIMARY_LOCK
theorem_promotion = false
fb05_closed = false
negative_root_exclusion = false
rh_claim = false
```

This is stronger than the #199 representation diagnosis: even theorem-motivated pole-prime pairing performed upstream does not retain enough interval dependency information to expose the sign of the already-signed direct total.

It still does **not** prove that no arithmetic/source mechanism exists.

## Current post-green frontier

Do not continue rearranging linear source buckets without a new theorem that singles out the representation. The consumed source-level sequence is now:

```text
four-way source attribution                    -> dependency unresolved
collapsed three-way attribution                -> dependency unresolved
discrepancy/direct-arch upstream pairing       -> dependency unresolved
```

The next Pair-A test should preserve the fully assembled canonical parity object and ask whether a higher-level composite identity exposes a simpler independent sign mechanism. Merely re-encoding `J>0` as `(o/e)'>0` does not add mathematical information.

## Claim firewall

```text
#184 theorem package
  -/-> source-specific sign law

#197 GLOBAL_MONOTONE_ORIENTATION on frozen Q14
  -> rigorous bounded research
  -/-> arbitrary-Q theorem
  -/-> global canonical injectivity

#199 SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
  -> independent source attribution is dependency-limited

#201 DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED
  -> upstream pole-prime pairing still loses sign resolution
  -/-> loss of direct #197 J_POSITIVE
  -/-> source mechanism impossible
  -/-> FB-05 closure
  -/-> negative-root exclusion
  -/-> RH
```

## Post-#203 audit addendum — current research authority

The stale #201 authority/frontier wording above is preserved as history. Current research authority is PR #203:

```text
head  = c8196830a8b49e657b28d36b364e1cff68c568d6
merge = ab660e812a78d482145eadc3e42d186a63fa812b
tree  = 7360e366fe8d623ef63ca902c23522bb72935848
research disposition = COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED
center_kill_switch_survives = false
full_cover_executed = false
completed_leaf_count = 0
control_transfer_status = PATTERN_FALSIFIED_BEFORE_FULL_COVER
```

The repaired #203 implementation validates exact-rational parity-contrast transport and independent `G = O-E`, `G' = O'-E'`, `G'' = O''-E''` reconstruction. The preregistered sign pattern `E > 0`, `G > 0`, `G' >= 0`, `E' <= 0` fails before full-cover execution. This is a successful falsification result, not CI failure.

Pair-A **representation engineering** is therefore consumed/downgraded as the default research tactic. This does not prove that every possible Pair-A theorem is false. The next highest-information route is Pair D — same-state two-parity squeeze; Pair B — negative-index separation versus localized critical-line sampling rigidity — is secondary.

**Do not count them as two independent** constraints when two formulations instantiate the same underlying mechanism. Global Schur monotonicity remains quarantined. Theorem authority remains #184; negative-root exclusion remains OPEN; **RH remains OPEN.**