# RHRC documentation authority and update law

This file defines which documentation is authoritative and how to prevent research-state drift after rapid theorem and discovery changes.

## Authority order

When sources disagree:

1. **Live GitHub head + Lean compiler + CI** — exact checked object wins.
2. **Merged theorem declarations and machine registries** — theorem/claim surfaces.
3. **Active route README**.
4. **Living research-control SSOTs** — newest dated research delta plus `CURRENT_RESEARCH_PLAN.md` and current RHRC/root summaries.
5. **Current external build-plan / handover SSOT**.
6. **PR-specific settlement documents**.
7. **Historical roadmaps, audits, numerical receipts, external reviews and old implementation plans**.

Research certificates, exact-rational audits, Arb output and external reviews are routing evidence unless separately theoremized in Lean.

<!-- RHRC_CURRENT_STATE_BEGIN -->
## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #222
- validated final head = c46939488ead9535a63b547c38d64938a882a9f1
- merge commit = 001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5
- tree = fd151afbcae3155cc4d32a75da08b6f7e0119099

MERGED THEOREM-STAGE PROVENANCE
- PR #222
- validated theorem head = e42dbce1bbbc68b5cf9612e7c8a8dab2a2eca543
- validated theorem tree = 48d8752950c28e0d3bbd385646e71075abef9e76
- status = MERGED_VIA_PR_222
- theorem family = BIREGULAR_FIRST_BAD_ZERO_SHIFT_NORMAL_FORM

LATEST RESEARCH EVIDENCE
- PR #223
- validated head = 5e01e55544be937b0f0e389f1f279e13a89f2b3a
- merge commit = 8c57ce445a2223dab4a3e8aedbd3db67171e96b0
- tree = 3588cd964a3346b20e359b41c02eb8caaed3221a
- disposition = NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED
- qualified retained points = 0
- retained-state implication = FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE

CONTROL AUTHORITY
- PR #117
- selected formal first break = E4A4-SCHUR-FB-05
- active subobligation = OBS-059I
- next research target = RETAINED_BIREGULAR_ZERO_SHIFT_SCALAR_DISCRIMINATION
- R003 phase = DISCOVERY
- confirmatory execution = NOT AUTHORIZED
- terminal claim = RH_OPEN
<!-- RHRC_CURRENT_STATE_END -->

## Living-current-surface rule

Every file designated as a living/current SSOT must expose the current three-anchor state before historical material. A later append-only override does **not** cure a stale top-level declaration of what is current.

`control_v2/CONTROL_STATE.json` is the machine source for the present descriptive research state. `control_v2/ACTION_REGISTRY.json` remains the frozen PR #117 control-semantic contract unless a deliberate semantic migration changes that contract and its tests together. In particular, `ACTION_REGISTRY.current_frontier` must not be silently reinterpreted as the latest research operation.

## Historical three-anchor model through PR #201

### Theorem-state anchor

```text
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
```

PR #184 remains the current compiler-validated mathematical authority.

### Research-evidence anchor

```text
latest merged research PR = #201
validated research head = be5b98dfce12777436bc40b39a37b04669ae4311
merged research commit = 319db6f68f65bdcffc0657c03bea76502da59a57
validated research tree = 840a2e8b0bf690507bc3385fbe122210e6d32c7a
research disposition = DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED
```

PR #201 is research/falsification authority only. It consumes PR #199's explicit cancellation-preserving escape by forming `D = pole + prime_signed` and `A = direct_arch_signed` at matrix-jet level before parity restriction/transport. The direct #197 `GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE` certificate still replays unchanged, while the paired representation remains dependency-unresolved on all 49 completed leaves. No Lean theorem authority moves.

### Control-plane semantic anchor

```text
control-plane semantic anchor = PR #117
merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
```

This changes only when controller capability/authority semantics change.

## Living SSOT update law

Update these when their underlying state changes:

- root `README.md`, `FORK_NOTES.md`, `AUDIT.md`;
- `research/RHRC/README.md`;
- active route README;
- `research/RHRC/RESEARCH_LEADS.md`;
- newest dated research delta;
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md` when validation anchors/evidence classes change;
- obstruction/dead-route ledgers when reusable classifications change;
- `control_v2/CONTROL_STATE.json` when theorem/control anchors or descriptive research state change;
- `control_v2/ACTION_REGISTRY.json` only when routing priority/first-break semantics change;
- `routes/ROUTE_REGISTRY.json` when route state/claim surfaces or its living route note changes;
- retro aliases/regression tests when intentionally hard-coded research vocabulary changes.

Historical dated deltas are not rewritten to look current. Historical regression tests are not repurposed to erase earlier consumed layers.

## Historical synchronized state through PR #201

### Theorem authority through #184

Lean proves the Hermitian 2x2 Schur/contact calculus, exact frozen production log-cover family, fixed-cell production bridge, N2 predecessor/canonical-shell reconstruction and orthogonality, and

```text
M~(t)=-tI+R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

No later research PR promotes additional Lean theorem authority.

### Completed research history through #201

```text
#186 -> broad remainder domination returns DOMINATION_SIGNAL_MIXED
#190 -> complete seven-selector vector jointly ambiently separable from target sign
        -> EXACT_TWIN_SURVIVES / EXACT_TWIN_EXCLUDED_BY_IDENTITY retained as historical contracts
#192 -> canonical production realizability Layer 0 -> Layer 5 executed
#193 -> first-order Q14 parity trajectory remains finite-width unresolved
        -> Do **not** infer this from points
#195 -> validated M,M',M''; J' = o''e - e''o
        -> PARTIAL_TRAJECTORY_ORIENTATION / 63/64 historical
#197 -> unique residual leaf replay closes the frozen Q14 cover
        -> GLOBAL_MONOTONE_ORIENTATION / uniform J_POSITIVE
        -> certified fraction 1
        -> bounded distinct-aperture twin exclusion
#199 -> exact #197 cover replayed unchanged
        -> four-way and collapsed source mechanisms = SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED
        -> direct bounded J_POSITIVE unchanged
#201 -> discrepancy/direct-arch pairing performed before parity restriction/transport
        -> paired M,M',M'' reconstruction passes
        -> direct bounded J_POSITIVE unchanged
        -> paired positive source sums = 0/49
        -> paired unresolved source sums = 49/49
        -> DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED
        -> NO_UNIQUE_PRIMARY_LOCK
```

Historical #195, #197 and #199 states remain preserved. PR #201 advances only the latest research-evidence anchor.

### Historical route after PR #201

```text
PROVED THROUGH #184
  exact Hermitian/log-cover/contact algebra

RESEARCHED THROUGH #201
  frozen Q14 direct orientation is complete and positive
  independent source attribution loses sign resolution
  theorem-motivated upstream pole-prime pairing also loses sign resolution

NOW
  stop source chopping as the default route
  do not change only source parentheses and call it new mathematics
  preserve the assembled canonical parity object
  test a higher-level exact composite parity identity
  predeclare an exact-center falsification pattern before any full-hull run
  reuse the exact #197 49-leaf partition only if the center pattern survives
  if the composite mechanism also fails -> downgrade Pair A representation work and pivot to Pair D / Pair B
```

A complete signed finite-width cover supports **rigorous bounded research**, not arbitrary-Q theorem authority. A dependency-unresolved decomposition does not negate an independently certified direct sign.

## Historical-state rule

The post-#190, post-#193, post-#195, post-#197 and post-#199 deltas remain historical evidence and must not be edited to pretend they were written after #201. `RESEARCH_LEADS_POST_201_Q14_DISCREPANCY_MECHANISM_DELTA.md` is the newest current delta.

Historical `test_post195_sync.py`, `test_post197_sync.py` and `test_post199_sync.py` continue to verify that their evidence remains represented. `test_post201_sync.py` owns the current #201 assertions.

## Claim firewall

- green research is not theorem promotion;
- exact executable algebra is not automatically a Lean theorem;
- ambient algebra countermodels are not automatically canonical arithmetic states;
- #197 `GLOBAL_MONOTONE_ORIENTATION` is complete bounded research on one frozen Q14 domain;
- #199 `SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED` is a representation/mechanism classification, not a loss of #197 `J_POSITIVE`;
- #201 `DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED` is another representation/mechanism classification, not a loss of #197 `J_POSITIVE`;
- 0/49 paired positive source sums means the paired interval graph is unresolved, not that the direct Wronskian is nonpositive;
- no unique source lock is not a theorem that no source law exists;
- **Do not count them as two independent** when equivalent formulations encode the same mechanism;
- theorem authority remains #184;
- control semantic authority remains #117;
- negative-root exclusion remains OPEN;
- **RH remains OPEN.**

## Historical post-#203 authority override

This section is the current synchronization and supersedes any earlier `latest merged research PR`, `newest current delta`, or `NOW` wording above while preserving that wording as history.

### Historical research-evidence anchor at that point

```text
latest merged research PR = #203
validated research head = c8196830a8b49e657b28d36b364e1cff68c568d6
merged research commit = ab660e812a78d482145eadc3e42d186a63fa812b
validated research tree = 7360e366fe8d623ef63ca902c23522bb72935848
research disposition = COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED
```

PR #203 is research/falsification authority only. Its repaired theorem-aligned parity contrast validates exact rational conversion, scalar cancellation before interval transport, and independent normalized `O-E` reconstruction through second order. The preregistered conjunction `E > 0`, `G > 0`, `G' >= 0`, `E' <= 0` fails its six-center gate, so `center_kill_switch_survives = false`, `full_cover_executed = false`, `completed_leaf_count = 0`, and `control_transfer_status = PATTERN_FALSIFIED_BEFORE_FULL_COVER`.

The direct #197 `GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE` certificate is unchanged. The failure consumes the planned simple Pair-A representation-engineering lane; it does not prove every Pair-A theorem impossible.

### Historical route after #203

```text
Pair-A representation engineering = CONSUMED / DOWNGRADED
Pair D — same-state two-parity squeeze = HIGHEST INFORMATION / NEXT RESEARCH ROUTE
Pair B — negative-index separation vs localized critical-line sampling rigidity = SECONDARY
OBS-059 = OPEN / ACTIVE same-state two-parity squeeze / simultaneous-badness exclusion gap
```

The theorem anchor remains PR #184. The control-plane semantic anchor remains PR #117. `ACTION_REGISTRY.json` does not change because the selected formal frontier, action scores, concept ID, and `E4A4-SCHUR-FB-05` first-break semantics remain unchanged.

`RESEARCH_LEADS_POST_203_Q14_COMPOSITE_PARITY_GAP_DELTA.md` is the newest current research delta. `OBSTRUCTION_LEDGER_POST_203_DELTA.md` and `DEAD_ROUTES_POST_203_DELTA.md` carry the corresponding obstruction/dead-route updates. Historical post-#201 files and tests remain historical and are not rewritten.

R003 remains `DISCOVERY`; confirmatory execution remains unauthorized. Negative-root exclusion remains OPEN. **RH remains OPEN.**

## Historical post-#205 authority override

This section supersedes the post-#203 authority pointer while preserving all earlier state as history.

### Historical research-evidence anchor at that point

```text
latest merged research PR = #205
validated research head = 73b78297da54b9f5b2d47584a8033356a6b2e2a8
merged research commit = deaa69ae190ada511cf8228f174846184673ff3a
validated research tree = 3d715612eabf25a9056ab84b0c5e968f71354666
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

PR #205 is exact executable research only. It reconstructs historical fixture C1 on the repository's actual radius-3 centered parity geometry and certifies both predecessor sectors positive (`70`, `10`) while both successor sectors admit exact negative witnesses (`-130`, `-410`), with selected even compressed root `-13/42`, reversal symmetry, and exact centered-index commutation. `canonical_realizability=false`.

Evidence class:

```text
EXACT EXECUTABLE RESEARCH
RIGOROUS FINITE SYNTHETIC COUNTERMODEL
```

This strengthens the old DR-012/DR-013 structural countermodel conclusion: generic first-bad/parity/shell/displacement structure is insufficient for simultaneous-badness exclusion. It does not show a canonical retained state has both parities bad.

### Historical route after #205

```text
Pair-A representation engineering = CONSUMED / DOWNGRADED
generic structural Pair-D simultaneous-bad exclusion = CONSUMED / FALSIFIED BY C1
Pair D canonical-arithmetic same-state squeeze = HIGHEST INFORMATION / ACTIVE
Pair B negative-index separation vs localized critical-line sampling rigidity = SECONDARY
OBS-059 = OPEN / ACTIVE / CANONICAL-ARITHMETIC ONLY
```

The next research falsifier is the generic quadratic-normal-defect-versus-`M4` implication. A synthetic pairing must not be named `explicitCanonicalSourceMoment`. If the generic bridge fails, only the generic bridge is consumed; the canonical arithmetic relation remains open.

`RESEARCH_LEADS_POST_205_PAIR_D_STRUCTURAL_COUNTERMODEL_DELTA.md` is the newest current research delta. `OBSTRUCTION_LEDGER_POST_205_DELTA.md` and `DEAD_ROUTES_POST_205_DELTA.md` carry the new obstruction/dead-route refinements. Historical deltas and their evidence classes remain unchanged.

The theorem anchor remains PR #184. The control-plane semantic anchor remains PR #117. `ACTION_REGISTRY.json` remains unchanged because the formal first break and action semantics do not move. R003 remains `DISCOVERY`; confirmatory execution remains unauthorized. Negative-root exclusion remains OPEN. **RH remains OPEN.**

## Historical post-#207 authority override

This section supersedes the post-#205 theorem pointer while preserving all earlier state as history.

### Historical theorem-state anchor at that point

```text
latest theorem-bearing PR = #207
validated theorem head = 7e186ede13beece95e8a08b2449cd3accbe5b2f5
merged theorem commit = 76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0
validated theorem tree = d6509407cc7b667b0ff3e7faab2acd525ae32db9
```

### Historical research-evidence anchor at that point

```text
latest merged research PR = #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

The three-anchor model is therefore now: theorem authority PR #207, research-only authority PR #205, control semantic authority PR #117.

PR #207 proves the canonical Pair-D sourceMoment/`M4` energy orientation on the retained even-selected odd-good branch. The living theorem inventory must include

```text
evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad
evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad
evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
oddBad_or_sourceMomentMomentFour_re_pos_of_even
```

The old generic `genericQuadraticNormalPairing != 0 ?-> M4 != 0` next-step proposal is **SUPERSEDED / UNNECESSARY**, not falsified and not a dead route. No unconditional `sourceMoment -> M4` implication has been proved.

`RESEARCH_LEADS_POST_207_PAIR_D_SOURCE_M4_ENERGY_DELTA.md` is the newest current theorem/research delta. `OBSTRUCTION_LEDGER_POST_207_DELTA.md` records the split state of `OBS-059`. Historical post-#205 files remain historical and are not rewritten.

The next theorem extraction is quantitative Pair-D coercivity `-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)` and its retained specialization, followed by #163 mixed-jet/Riesz composition. `ACTION_REGISTRY.json` remains unchanged because the first-break semantics do not move. R003 remains `DISCOVERY`; confirmatory execution remains unauthorized. Negative-root exclusion remains OPEN. **RH remains OPEN.**

## Historical post-#209 authority override

This section supersedes the post-#207 current theorem pointer while preserving all earlier state as history.

### Historical theorem-state anchor at that point

```text
latest theorem-bearing PR = #209
validated theorem head = a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392
merged theorem commit = e029af769e01a547ebbc6ed045509bb2cbdd6cff
validated theorem tree = 6a75278ebf3f2bd19a77419238872cb81835ec13
```

### Historical research-evidence anchor at that point

```text
latest merged research PR = #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

The three-anchor model is now: theorem authority PR #209, research-only authority PR #205, control semantic authority PR #117.

PR #209 proves quantitative Pair-D coercivity, strict complete-source/seventh-jet anti-alignment on the even-negative/odd-good branch, the retained `oddBad_or_sourceMomentMixedJet_re_neg_of_even` fork, and the nondegenerate `R8 = R9 <-> endpointScalar(L,8)=0` boundary equivalence.

`RESEARCH_LEADS_POST_209_PAIR_D_COERCIVITY_ANTI_ALIGNMENT_DELTA.md` is the newest current theorem/research delta. `OBSTRUCTION_LEDGER_POST_209_DELTA.md` records `OBS-059Q` as CLOSED / PROVED BY #209 and introduces `OBS-059I` as the active independent complete-functional incompatibility sub-obligation. Historical post-#207 files remain historical and are not rewritten.

The next research step is not another extraction from the #207/#209 energy identity. It is a preregistered falsification search for genuinely independent complete-canonical-functional sign/magnitude information, or an independent Riesz high-order limit/sign theorem, on the same retained state.

`ACTION_REGISTRY.json` remains unchanged because the first-break semantics do not move. R003 remains `DISCOVERY`; confirmatory execution remains unauthorized. Endpoint-scalar sign, simultaneous odd-bad exclusion, odd-selected closure, negative-root exclusion and **RH remain OPEN.**

## Historical post-#211 authority override

This section supersedes the post-#209 current theorem pointer while preserving all earlier state as history.

### Historical theorem-state anchor at that point

```text
latest theorem-bearing PR = #211
validated theorem head = 704a69e41871269814ba091e9476fe76b2d09844
merged theorem commit = dd42e6368e48957c9922a9e917e10f60a2582b9f
validated theorem tree = a735f6149aeaa9f8358394c33fd6dcee8062f68e
```

### Historical research-evidence anchor at that point

```text
latest merged research PR = #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

### Control-semantic anchor

```text
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The newest current post-green delta is `RESEARCH_LEADS_POST_211_COMPLETE_FUNCTIONAL_REPRESENTATION_DELTA.md`. The newest obstruction delta is `OBSTRUCTION_LEDGER_POST_211_DELTA.md`. Historical post-#209 files remain historical and are not rewritten.

PR #211 closes the complete-functional representation prerequisite but not OBS-059I. The next theoremization target is `SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL`; the required new information remains `INDEPENDENT_COMPLETE_CANONICAL_FUNCTIONAL_INCOMPATIBILITY`.

`ACTION_REGISTRY.json`, claim IDs, route digests, action scores and first-break semantics remain unchanged. R003 remains `DISCOVERY`; confirmatory execution remains unauthorized. **RH remains OPEN.**

## Historical post-#213 authority override

```text
latest theorem-bearing PR = #213
validated theorem head = 703c3764a7d35aa4801e791a1929efa54c2533a1
merged theorem commit = ee341a6071d177c75bbea0a5f92ebe3b3bb16696
validated theorem tree = db00686b2bbb821adb857e5c68f422d19c4f91cd

latest research-only evidence = PR #205
control semantic authority = PR #117
terminal claim = RH_OPEN
```

Newest post-green delta: `RESEARCH_LEADS_POST_213_COMPLETE_SOURCE_KERNEL_DELTA.md`.

Newest obstruction delta: `OBSTRUCTION_LEDGER_POST_213_DELTA.md`.

PR #213 closes `SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL` but does not close `OBS-059I`. The next research operation is `EXACT_KERNEL_ADVERSARIAL_FALSIFICATION`.

Historical post-#211 files remain immutable evidence. No claim IDs, action scores, first-break semantics, route digests, or confirmation permissions change. **RH remains OPEN.**

## Post-#215 authority — retained negative-root secular frontier

Current authority split after merged-green research PR #215:

```text
THEOREM AUTHORITY
PR #213
validated head = 703c3764a7d35aa4801e791a1929efa54c2533a1
merge          = ee341a6071d177c75bbea0a5f92ebe3b3bb16696
tree           = db00686b2bbb821adb857e5c68f422d19c4f91cd

LATEST RESEARCH EVIDENCE
PR #215
validated head = 5469fbac77c82ccfc9dad0da4c7ce2b0ba67c47a
merge          = 191b1b648448c92010286dae54df8502df1f55ce
tree           = 4e6111c974ae8abbf59a5063d4b1ea760fa39ffd
disposition    = FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED
sign result    = FULL_SPACE_SIGN_INDEFINITE_CERTIFIED
controls       = DUAL_INDEPENDENCE_SURVIVES_Q13_Q15_CONTROLS

CONTROL SEMANTIC AUTHORITY
PR #117

terminal claim = RH_OPEN
```

PR #215 is rigorous bounded Arb research, not Lean theorem promotion. On the exact frozen K=3 even boundary-flat carrier it certifies the M4 covector `(24,144)`, a nonzero source/M4 wedge at Q14
`[-7.92856142933793718521707742118e-7 +/- 2.44e-37]`, and generalized pairing extrema relative to `||Dv||^2`

```text
R_min = -7.60547660138399452560501190345e-11
R_max =  1.02497161190896926446719955942e-6
```

so the full-carrier pairing is sign-indefinite. Universal full-carrier source/M4 sign and proportionality routes are therefore consumed at this research scope.

The retained-state implication was explicitly `NOT_TESTED` by #215. The next route is not a guessed contact state. It is the already theorem-backed **retained negative-root cross-parity secular state**: preserve the same aperture, size, selected parity, negative shift and canonical source functional, and investigate whether the old exact cross-parity secular transfer combines with #209/#213 into an independent incompatibility.

```text
next research target = RETAINED_CROSS_PARITY_SECULAR_COMPLETION
contact-locus route  = LEAD / REQUIRES SAME-STATE CONTACT BRIDGE
zero-shift response  = RESURRECTED SECONDARY
resonant pole/tube   = RESURRECTED SECONDARY
OBS-059I             = OPEN / ACTIVE
RH                    = OPEN
```

No claim IDs, action scores, first-break semantics, route digests, confirmation permissions or theorem declarations change in this synchronization.
