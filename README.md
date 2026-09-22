# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

<!-- RHRC_CURRENT_STATE_BEGIN -->
## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #236
- validated final head = 45491342f5661429679579c7889c1ad8b96728b6
- merge commit = a66e1c617033f4adaa52e935668399efb93048ac
- tree = 5ef597b1d75075ec2299261a4193432a36932ffe
- status = MERGED_VIA_PR_236
- theorem family = RETAINED_CANONICAL_REAL_PHASE_COLLAPSE
- exact flagship theorem = `oddBad_of_even_of_realSourceDeficit_pos_of_radius_gap`
- exact compatibility theorem = `retainedRealSourceDeficit_or_radius_of_even_of_not_oddBad`
- retained canonical trial/source phase = conjugation-fixed / real
- `normSq(S) = (Re S)^2`
- workflow harvest = 13/13 ATTACHED WORKFLOWS GREEN on the validated #236 head

LATEST RESEARCH EVIDENCE
- PR #223
- disposition = NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED
- retained-state implication = FROZEN_SCOPE_DID_NOT_REACH_RETAINED_STATE

POST-#236 WORKFLOW HARVEST
- post-200 = DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED / NO_UNIQUE_PRIMARY_LOCK
- post-202 = COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED
- post-214 = full-space dual independence preserved; full-space complete-functional sign remains indefinite
- post-222 = NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED
- theorem promotion from research replays = false

POST-#234 NUMERICAL FIREWALL
- numerical D/E prerequisite = CANONICAL_CUBIC_SHELL_NORMALIZATION
- latest post-#165 shifted-state scout = 672 attempted / 0 shifted states
- numerical theorem promotion = NOT AUTHORIZED

CONTROL AUTHORITY
- PR #117
- selected formal first break = E4A4-SCHUR-FB-05
- active subobligation = OBS-059I
- next research target = RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR
- required new information = REALITY_OF_RETAINED_M4_AND_SCALAR_COMPOSITION
- R003 phase = DISCOVERY
- confirmatory execution = NOT AUTHORIZED
- sharp radius / shell barrier = OPEN
- simultaneous odd-bad branch = OPEN
- odd-selected first-bad branch = OPEN
- parity-complete retained-state exclusion = OPEN
- terminal Mathlib RH seam = OPEN
- terminal claim = RH_OPEN
<!-- RHRC_CURRENT_STATE_END -->

## Post-#231 current-state override

PR #231 proves the generic correction/source-coupling bridge, its production-channel
rewrite, the exact Gamma shell balance, and the retained factor-preserving source
balance. On the selected-even / odd-good retained branch, the existing source
nonvanishing theorem cancels the source factor and gives the exact same-state
balance
`q - J = M4 - S*C`.

PR #231 does **not** prove alpha reality/sign, a sign for the source coupling,
canonical simultaneous odd-bad exclusion, odd-selected closure, parity-complete
retained-state exclusion, negative-root exclusion, the terminal Mathlib RH seam,
or RH.

The #231 workflow harvest completed 11/11 attached workflows green on the exact
validated head `f9623be705955bd98ef563aa75d3244712009cac`. Latest independent
research evidence remains PR #223; Control-v2 semantic authority remains PR #117.

The next theorem target is `RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK`: use
good-sector Gram control only as an intermediate bridge, then compose it with
the #231 same-state source balance. The required new information is
`GOOD_SECTOR_GRAM_CONTROL_COMPOSED_WITH_RETAINED_SOURCE_BALANCE`.
A proof of `canonicalOneStepDomination` obtained merely by restating successor
positivity is not by itself independent FB-05 information.

Detailed post-green pass:
`RESEARCH_LEADS_POST_231_SOURCE_BALANCE_DELTA.md` and
`OBSTRUCTION_LEDGER_POST_231_DELTA.md`.

Any older "current", "next", or routing labels below this override are historical
snapshots unless re-established above.

```text
ACTION_REGISTRY.current_frontier
  = frozen PR #117 control-semantic frontier

CONTROL_STATE.active_research_route.next_research_target
  = current descriptive research operation
  = RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK
```

## Post-#229 current-state override

PR #229 proves the generic correction-functional Riesz representation
`chi(y) = <R b,y>/<c,c>` and the exact alpha/Gamma mixed-resolvent corollaries.
It does **not** prove that alpha is real, positive, or sign-controlled.

The next theorem target is `CROSS_PARITY_CORRECTION_SOURCE_COUPLING`: formalize
the derived bridge `star (1-alpha) * <c,c> = cubicShellCoupling (R d)`, rewrite
it through the production canonical source channels, and then derive the
retained source-balance identity under an explicit nonzero source moment.
Those statements are **OPEN / NEXT**, not theorem authority yet.

The #229 workflow harvest completed 13/13 green jobs. Latest independent
research evidence remains PR #223; Control-v2 semantic authority remains PR #117.
OBS-059I, simultaneous odd-bad exclusion, odd-selected closure,
parity-complete retained-state exclusion, the terminal Mathlib RH seam, and RH
remain OPEN.

Detailed post-green pass:
`RESEARCH_LEADS_POST_229_RIESZ_DELTA.md` and
`OBSTRUCTION_LEDGER_POST_229_DELTA.md`.

Any older "current", "next", or routing labels below this override are
historical snapshots unless re-established above.

## Historical post-#227 closure override

PR #226 and PR #227 close the predecessor-correction and two-coefficient transfer stages that the historical section below still describes as open.

**PROVED**
- `oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul` (#226):
  `a_N = -((2N-1)/6) d_N`.
- #227 propagates that identity through the safe secular functional, direct zero-shift overlaps, predecessor-kernel transport, and the selected-even bi-regular retained state.
- `Gamma_lambda = 1 + kappa_N * (1 - alpha_lambda)`, with denominator-free one-coefficient transfer.
- The direct zero-shift selected-even normal form is theorem-backed.

**NEXT / OPEN**
- `CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION`: export the generic theorem
  `chi(y) = <R b, y> / <c,c>` underlying both alpha and Gamma.
- Alpha reality/sign is not proved; the natural numerator is a mixed resolvent pairing.
- Odd-selected closure, simultaneous canonical odd-bad exclusion, parity-complete retained-state exclusion, the terminal Mathlib seam, and RH remain OPEN.

Do not identify the safe negative-shift state with the zero-shift retained state without an explicit bridge, and do not treat selected-even as WLOG.


## Historical post-#224 RH closure plan — predecessor-correction stage

This is the current **research/proof plan**, not a claim that RH is closed. Compiler/CI evidence remains authoritative, and every step below must be proved without project axioms, `sorry`, hidden RH-equivalent assumptions, or promotion beyond the exact checked declaration.

### Already established in the live theorem stack

1. **Exceptional-zero seam — PROVED:** a hypothetical off-critical-line zero in the project's open-strip `zetaZeroConfig` feeds the finite exceptional-zero/CCM obstruction machinery and yields a canonical negative finite witness.
2. **First-bad reduction — PROVED:** a negative finite witness reduces to a regular, cell-minimal first-bad certificate.
3. **Bi-regularization (#222) — PROVED:** the retained cell-minimal first-bad state can be chosen with both predecessor parities regular at the same aperture and cutoff.
4. **Zero-shift classification (#221/#222) — PROVED:** on the bi-regular retained state predecessor resonance is eliminated. In the selected-even branch,
   ```text
   Re sigmaPlus < 0
   sigmaMinus = alpha0 * sigmaPlus + Gamma0 * mu0
   odd badness <-> Re sigmaMinus < 0
   ```
5. **Exact odd cubic projection (#224) — PROVED:** Lean proves
   ```text
   d^3 - g_K = ((3*K^2 + 3*K - 1)/5) * d.
   ```
   Exact promoted declaration: `cubicProjectionResidual_eq_oddCubicProjectionSlope_smul`.

### Immediate theorem target after #224

The next theorem is **not** already proved by #224. Define the coefficient in the scalar field, not with natural-number subtraction/division:

```lean
def crossParityCubicCorrectionKappa (N : ℕ) : ℂ :=
  (2 * (N : ℂ) - 1) / 6
```

Then prove, for the nontrivial range used by the shell machinery,

```lean
theorem oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
    (N : ℕ) (hN : 1 ≤ N) :
    oddCubicGeneratorPredecessorPart N =
      -(crossParityCubicCorrectionKappa N) •
        oddIndexCubicShellPredecessorPart N := by
  ...
```

Mathematically this is

```text
a_N = -((2N - 1)/6) d_N.
```

Status: **OPEN / NEXT**.

### Conditional downstream collapse

If the predecessor-correction proportionality is proved, then the existing definitions give the affine transfer-coefficient relation

```text
Gamma0 = 1 + ((2N - 1)/6) * (1 - alpha0)
6*Gamma0 + (2N - 1)*alpha0 = 2N + 5
```

and the selected-even retained scalar becomes

```text
6*sigmaMinus
  = alpha0 * (6*sigmaPlus - (2N - 1)*mu0)
    + (2N + 5)*mu0.
```

These are currently **DERIVED CONDITIONAL / NOT YET FORMALIZED**, not theorem authority.

### Parity-complete retained-state closure

The selected-even normal form is not by itself a complete finite contradiction: the retained first-bad certificate may have selected parity `odd`, and the repo does not prove the centered-index map preserves canonical energy strongly enough to make the even case WLOG.

The terminal finite argument therefore must do at least one of:

1. prove the selected parity may be taken even;
2. build the mirrored odd-to-even arithmetic squeeze; or
3. prove one parity-symmetric retained-state contradiction covering both cases.

A sufficient strong endpoint remains

```lean
theorem no_biRegular_cellMinimal_negativeEnergyCertificate
    (Q : ℕ) :
    IsEmpty (BiRegularCellMinimalNegativeEnergyCertificate Q) := by
  ...
```

but this is **stronger than required**. A contradiction specialized to the off-line-zero-generated retained certificate also closes the route and may use extra canonical ancestry that arbitrary finite certificates do not possess.

### Zeta-level contradiction direction

The route does **not** require a new finite-to-infinite spectral convergence theorem. The proved direction already runs from a hypothetical off-line zeta zero down to the finite obstruction:

```text
hypothetical off-line strip zero
    -> canonical finite negative witness
    -> regular cell-minimal first-bad certificate
    -> bi-regular retained negative-energy certificate
    -> parity-complete retained-state contradiction
    -> no off-line zero in zetaZeroConfig.
```

The final result is obtained by contradiction/contrapositive packaging.

### Terminal Mathlib RH seam

The project's `zetaZeroConfig` carrier already restricts to zeros in the open critical strip. Mathlib's exact `RiemannHypothesis` quantifies over every nontrivial zeta zero except the known trivial negative even zeros and the pole point.

Therefore, after proving all `zetaZeroConfig` zeros lie on `Re = 1/2`, one final formal seam remains: show every Mathlib-nontrivial zero is either one of the excluded trivial zeros or lies in the open critical strip, using the available nonvanishing/functional-equation machinery.

Status: **OPEN terminal seam**.

### Claim firewall

- PR #224 is theorem authority **only** for its exact compiled cubic-projection declaration; its PR title/body do not prove the stronger predecessor-correction proportionality.
- PR #223 remains the latest rigorous bounded research evidence and did not reach the theorem-guaranteed retained state.
- OBS-059I remains OPEN.
- simultaneous canonical odd-bad exclusion remains OPEN.
- odd-selected first-bad closure remains OPEN.
- parity-complete retained-state exclusion remains OPEN.
- negative-root exclusion remains OPEN as a stronger historical route, but a direct retained-certificate contradiction could bypass it.
- the terminal Mathlib `RiemannHypothesis` seam remains OPEN.
- **RH remains OPEN.**

## Historical authority snapshot through PR #201

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

## Historical theorem frontier through PR #184

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

## Historical active path after PR #201 — FB-05 / full-composite parity mechanism

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

## Post-#205 authoritative synchronization

This section is the current research-state override.

```text
THEOREM AUTHORITY
PR #184

LATEST RESEARCH EVIDENCE
PR #205
head  = 73b78297da54b9f5b2d47584a8033356a6b2e2a8
merge = deaa69ae190ada511cf8228f174846184673ff3a
tree  = 3d715612eabf25a9056ab84b0c5e968f71354666
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED

CONTROL SEMANTIC AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

PR #205 promotes the historical C1 radius-3 structural fixture to `EXACT EXECUTABLE RESEARCH / RIGOROUS FINITE SYNTHETIC COUNTERMODEL`. Exact values are

```text
N = 2
K = 3
even predecessor form = 70
odd predecessor form  = 10
even negative witness energy = -130
odd negative witness energy  = -410
selected even compressed root = -13/42
reversal symmetric = true
centered-index commutator = 0
canonical_realizability = false
```

Therefore generic predecessor positivity, actual parity/boundary-flat/shell geometry, reversal symmetry and centered-index displacement structure do not exclude simultaneous even/odd successor badness. The **generic structural Pair-D lane is consumed**. Pair D itself remains active only as a **canonical-arithmetic same-state squeeze**: any successful exclusion must spend a property of the actual `canonicalSourceMatrix` absent from C1.

`OBS-059` remains OPEN / ACTIVE / CANONICAL-ARITHMETIC ONLY. The canonical simultaneous-parity exclusion, `sourceMoment <-> M4` rigidity, same-state canonical composition, and odd-selected first-bad closure remain open. The next research falsifier should attack the generic quadratic-normal-defect-versus-`M4` implication before any new Lean theorem investment. Pair B remains secondary.

No Lean theorem, claim registry, promoted binding, `ACTION_REGISTRY` score, first-break semantics or confirmatory status changes here. R003 remains `DISCOVERY`; negative-root exclusion remains OPEN; **RH remains OPEN.**

## Post-#207 theorem-authority synchronization

This section supersedes the earlier theorem/frontier wording while preserving it as history.

```text
THEOREM AUTHORITY = PR #207
validated theorem head = 7e186ede13beece95e8a08b2449cd3accbe5b2f5
merged theorem commit = 76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0
validated theorem tree = d6509407cc7b667b0ff3e7faab2acd525ae32db9

LATEST RESEARCH EVIDENCE = PR #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED

CONTROL SEMANTIC AUTHORITY = PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

PR #207 proves the exact canonical Pair-D self-energy identity and, on an even negative compressed eigenmode with the odd sector good,

```text
0 < re(star(explicitCanonicalSourceMoment) * M4).
```

On the retained even-selected first-bad state the theorem package includes

```text
evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad
evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad
evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
oddBad_or_sourceMomentMomentFour_re_pos_of_even
```

Thus the even-selected + odd-good retained branch is **PROVED THROUGH #207**. The canonical simultaneous odd-bad branch remains OPEN, the odd-selected first-bad branch remains OPEN, and no unconditional `sourceMoment -> M4` implication is proved.

The planned neutral `genericQuadraticNormalPairing != 0 ?-> M4 != 0` falsifier is **SUPERSEDED / UNNECESSARY** as the next gate; it was not executed and is not a dead route. The highest-information next theorem extraction is the quantitative coercive bound

```text
-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)
```

first generically and then on the retained shifted trial, followed by composition with the #163 mixed seventh-jet/Riesz boundary package.

R003 remains `DISCOVERY`; confirmatory execution is not authorized. Negative-root exclusion remains OPEN. **RH remains OPEN.**

## Post-#209 theorem-authority synchronization

This section supersedes the post-#207 current-frontier wording while preserving all earlier sections as historical ancestry.

```text
THEOREM AUTHORITY = PR #209
validated theorem head = a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392
merged theorem commit = e029af769e01a547ebbc6ed045509bb2cbdd6cff
validated theorem tree = 6a75278ebf3f2bd19a77419238872cb81835ec13

LATEST RESEARCH EVIDENCE = PR #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED

CONTROL SEMANTIC AUTHORITY = PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

PR #209 proves the quantitative Pair-D coercive law and its exact mixed-source reformulation:

```text
-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)
re(star(sourceMoment) * h^(7)(0))
  <= 2*(2*pi)^6*lam*||Dv||^2
```

and on a genuine negative eigenmode with odd successor good,

```text
re(star(sourceMoment) * h^(7)(0)) < 0.
```

The retained theorem package includes

```text
evenShiftedSourceMomentMomentFour_coercive_of_even_of_not_oddBad
evenShiftedSourceMomentMixedJet_re_le_of_even_of_not_oddBad
evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad
oddBad_or_sourceMomentMixedJet_re_neg_of_even
evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad
```

Hence the even-selected + odd-good retained branch is **PROVED THROUGH #209**. `OBS-059Q` is CLOSED / PROVED BY #209. The simultaneous odd-bad branch, odd-selected first-bad branch, endpoint-scalar sign, terminal FB-05 incompatibility and negative-root exclusion remain OPEN.

The active information gate is `OBS-059I`: find an **independent complete canonical functional incompatibility** with the #209 anti-alignment or compulsory magnitude budget on the same retained state. Do not count a rearrangement of the same odd-sector self-energy identity as independent information, and do not return to source-component interval chopping without a theorem preserving cancellation.

The Riesz lane is reactivated/nondegenerate on the even-selected odd-good branch because #209 removes the `J7 = 0` escape hatch, but no endpoint-scalar sign or high-order Riesz limit theorem is claimed.

R003 remains `DISCOVERY`; confirmatory execution is not authorized. `ACTION_REGISTRY.json`, claim IDs, route digests, action scores and first-break semantics remain unchanged. **RH remains OPEN.**

## Post-#211 theorem-authority synchronization

This section is the current authority override and preserves earlier post-green sections as historical ancestry.

```text
THEOREM AUTHORITY = PR #211
validated theorem head = 704a69e41871269814ba091e9476fe76b2d09844
merged theorem commit = dd42e6368e48957c9922a9e917e10f60a2582b9f
validated theorem tree = a735f6149aeaa9f8358394c33fd6dcee8062f68e

LATEST RESEARCH EVIDENCE = PR #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED

CONTROL SEMANTIC AUTHORITY = PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

PR #209 remains the provenance of quantitative Pair-D coercivity, strict sourceMoment/seventh-jet anti-alignment and Riesz-8/Riesz-9 nondegeneracy. PR #211 proves the mixed dictionary bridge and the exact complete-functional representation

```text
explicitCanonicalSourceMoment L K v
  = canonicalQuadraticNormalSourceFunctional L (quadraticNormalSourceAtom K v).
```

On the retained state the fork can now be stated as

```text
odd successor bad
OR
re(star(Λ_L(h_v)) * h_v^(7)(0)) < 0.
```

This is a representation/interface rewrite of the #209 obstruction, not an independent opposing sign theorem.

`OBS-059I` remains **OPEN / ACTIVE**. Its representation prerequisite is CLOSED / PROVED BY #211. The next theoremization target is `SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL`: derive the exact source-coordinate integral-plus-prime representation from the theorem-authoritative `literatureRHS` and the proved endpoint identities, without prerecording guessed constants or signs.

The required new information remains `INDEPENDENT_COMPLETE_CANONICAL_FUNCTIONAL_INCOMPATIBILITY`. The simultaneous odd-bad branch, odd-selected first-bad branch, endpoint-scalar sign, negative-root exclusion and **RH remain OPEN.**

## Post-#213 theorem-authority synchronization

```text
THEOREM AUTHORITY = PR #213
validated theorem head = 703c3764a7d35aa4801e791a1929efa54c2533a1
merged theorem commit = ee341a6071d177c75bbea0a5f92ebe3b3bb16696
validated theorem tree = db00686b2bbb821adb857e5c68f422d19c4f91cd

LATEST RESEARCH EVIDENCE = PR #205
CONTROL SEMANTIC AUTHORITY = PR #117
terminal claim = RH_OPEN
```

PR #209 remains the provenance of quantitative Pair-D coercivity and strict anti-alignment. PR #211 remains the complete-functional interface milestone. PR #213 proves the exact complete physical/source-coordinate kernel and the retained source-kernel anti-alignment rewrite.

```text
SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL
  = CLOSED / PROVED #213

OBS-059I
  = OPEN / ACTIVE

next research operation
  = EXACT_KERNEL_ADVERSARIAL_FALSIFICATION
```

The next research lanes are SIGN, MAGNITUDE, and DUAL / GRAM / EXTREMAL GEOMETRY.

Same-observable firewall: existing `CanonicalPolePrimeRiesz` results act on `sourceAtomRealEnergy`; #213 acts on `quadraticNormalSourceAtom`. Direct composition is not established.

No claim IDs, action scores, first-break semantics, route digests, or confirmation permissions change. **RH remains OPEN.**

## Historical RH/CCM frontier after PR #215

Theorem authority remains merged-green **PR #213**. Latest research evidence is merged-green **PR #215**, which rigorously certifies on the frozen K=3 even carrier that the complete source functional and M4 are independent duals and that their full-carrier pairing is sign-indefinite. This kills the universal arbitrary-vector sign/proportionality version of Pair D, not the retained first-bad route.

At that stage, the next target was **RETAINED_CROSS_PARITY_SECULAR_COMPLETION** on the exact forced negative root. Contact-locus ideas are explicitly demoted until a same-state contact bridge exists. The exact zero-shift response and resonant `1/(-lambda)` branch are resurrected secondary routes.

**RH remains OPEN.**
