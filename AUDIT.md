# RHRC formal audit — merged theorem authority PR #229; research evidence PR #223

> **RH remains OPEN.**

<!-- RHRC_CURRENT_STATE_BEGIN -->
## Current RHRC state

THEOREM AUTHORITY
- merged theorem authority = PR #229
- validated final head = 9d4f81c171264be424fbac40f1211263c3cc6abd
- merge commit = 992398c810de5fb84919846fc4192d709d51e783
- tree = d9ae07d1ca92cb23b4a3ae3ccae0b32e9b7d38c8
- theorem family = CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION
- prior theorem authority = PR #227 `CROSS_PARITY_ONE_COEFFICIENT_TRANSFER_COLLAPSE`
- exact flagship theorem = `oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div`
- exact alpha consequence = `one_sub_crossParitySecularAlpha_eq_resolvent_pairing_div`
- exact Gamma consequence = `one_sub_crossParitySecularGamma_eq_resolvent_pairing_div`
- alpha reality/sign = OPEN / NOT PROVED BY #229
- workflow harvest = 13/13 GREEN JOBS on the validated #229 head

MERGED THEOREM-STAGE PROVENANCE
- PR #229
- validated theorem head = 9d4f81c171264be424fbac40f1211263c3cc6abd
- validated theorem tree = d9ae07d1ca92cb23b4a3ae3ccae0b32e9b7d38c8
- status = MERGED_VIA_PR_229
- theorem family = CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION

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
- next research target = CROSS_PARITY_CORRECTION_SOURCE_COUPLING
- required new information = CANONICAL_SOURCE_COUPLING_AND_RETAINED_SOURCE_BALANCE
- R003 phase = DISCOVERY
- confirmatory execution = NOT AUTHORIZED
- terminal claim = RH_OPEN
<!-- RHRC_CURRENT_STATE_END -->

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

## Historical post-#227 audit settlement

Exact merged theorem authority is PR #227: final head `b8d29733167a95e16f5721eddfced6b650a3b641`, merge `7aace87a5644f837e2c8b64bdcf5e66b2dc0b020`, tree `1dd1cdefcf4f4f7929b310697fdd1615a861ca1a`. The PR synthetic merge that passed the full Lean/RHRC gate had the same tree.

PR #226 proves the predecessor correction proportionality. PR #227 proves the safe and zero-shift alpha/Gamma affine collapses, denominator-free one-coefficient transfer, kernel-direction collapse, and the selected-even bi-regular one-coefficient normal form. Headline `#print axioms` output is restricted to `propext`, `Classical.choice`, and `Quot.sound`; the CCM and ExceptionalZero builds and forbidden-placeholder scan passed.

Not proved: alpha reality/sign, simultaneous odd-bad exclusion, selected-even WLOG, odd-selected closure, negative-root exclusion, the terminal Mathlib RH seam, or RH.

Current theorem-extraction target: `CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION`.


## Historical post-#224 audit settlement

PR #224 advances theorem authority only for the exact cubic projection closed form
`cubicProjectionResidual_eq_oddCubicProjectionSlope_smul`.

The advertised predecessor-correction proportionality remains OPEN. The current next theorem target is `CROSS_PARITY_PREDECESSOR_CORRECTION_PROPORTIONALITY`; the alpha/Gamma and one-coefficient zero-shift collapses remain derived conditional statements until separately formalized.

The odd-selected branch and terminal Mathlib RH seam remain OPEN. **RH remains OPEN.**


Live GitHub head + exact compiler/CI evidence outrank this prose.

## Historical authority split through PR #201

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

## Historical formal theorem state through PR #184

No Lean theorem has been added after PR #184. The formal package still proves the Hermitian Schur/contact algebra, frozen parity production/log-cover family, exact fixed-cell production bridge, N2 predecessor/canonical-shell geometry, and the conditional decomposition

```text
M~(t)=-tI+R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

Still not proved: source-specific domination, contact existence/uniqueness, same-state opposing first-bad orientation, first-bad exclusion, negative-root exclusion or RH.

## Historical research audit: #186 -> #201

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

## Historical post-#203 audit addendum — research authority at that point

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

## Post-#205 audit addendum — generic Pair-D lane consumed

Historical post-#205 research authority was PR #205:

```text
head  = 73b78297da54b9f5b2d47584a8033356a6b2e2a8
merge = deaa69ae190ada511cf8228f174846184673ff3a
tree  = 3d715612eabf25a9056ab84b0c5e968f71354666
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

The exact executable C1 fixture uses the actual radius-3 centered boundary-flat parity geometry with a generic reversal-symmetric diagonal operator. It certifies both predecessor parity forms positive (`70`, `10`), while exact negative successor witnesses exist in both parities (`-130`, `-410`). The selected even compressed root is `-13/42`, and the centered-index commutator vanishes exactly.

This is `EXACT EXECUTABLE RESEARCH / RIGOROUS FINITE SYNTHETIC COUNTERMODEL`, not Lean theorem authority and not a canonical CCM counterexample. `canonical_realizability = false`.

Therefore generic predecessor positivity + parity/shell geometry + reversal symmetry + displacement commutation cannot supply the simultaneous-badness contradiction. DR-012 and DR-013 are strengthened by current executable evidence. Pair D remains open only in a **canonical-arithmetic** form: a later exclusion must identify a property of `canonicalSourceMatrix` that fails on C1.

The next cheapest falsifier should attack the generic quadratic-normal-defect-versus-`M4` implication. The canonical `sourceMoment <-> M4` question, odd-selected first-bad closure, FB-05, negative-root exclusion and RH remain OPEN. Theorem authority remains #184.

## Post-#207 audit addendum — theorem authority advances

```text
THEOREM AUTHORITY = PR #207
validated theorem head = 7e186ede13beece95e8a08b2449cd3accbe5b2f5
merged theorem commit = 76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0
validated theorem tree = d6509407cc7b667b0ff3e7faab2acd525ae32db9

LATEST RESEARCH EVIDENCE = PR #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

PR #207 is compiler-validated theorem authority. It proves the canonical Pair-D self-energy identity and the retained odd-good branch theorem

```text
evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad
evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad
evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
oddBad_or_sourceMomentMomentFour_re_pos_of_even
```

Hence the even-selected + odd-good retained branch is PROVED THROUGH #207: the exact sourceMoment/`M4` Hermitian pairing is strictly positive, the source moment is nonzero, `M4` is nonzero, and the mixed seventh source jet is nonzero.

The simultaneous odd-bad branch remains OPEN. The odd-selected first-bad branch remains OPEN. No unconditional `sourceMoment -> M4` implication is proved. The generic defect/`M4` falsifier is **SUPERSEDED / UNNECESSARY** as the next gate, not falsified.

The next theorem-level information gain is quantitative coercivity:

```text
-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)
```

which is DERIVED from the #207 proof pattern but not yet separately formalized. Negative-root exclusion remains OPEN. **RH remains OPEN.**

## Post-#209 audit addendum — quantitative Pair-D theorem authority

```text
THEOREM AUTHORITY = PR #209
validated theorem head = a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392
merged theorem commit = e029af769e01a547ebbc6ed045509bb2cbdd6cff
validated theorem tree = 6a75278ebf3f2bd19a77419238872cb81835ec13

LATEST RESEARCH EVIDENCE = PR #205
research disposition = PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED
```

PR #209 is compiler-validated theorem authority. It proves quantitative Pair-D coercivity, the exact sourceMoment/seventh-jet rewrite, the quantitative upper bound, and strict anti-alignment on a genuine negative even eigenmode with odd successor good.

On the retained even-selected state, the theorem package includes

```text
evenShiftedSourceMomentMomentFour_coercive_of_even_of_not_oddBad
evenShiftedSourceMomentMixedJet_re_le_of_even_of_not_oddBad
evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad
oddBad_or_sourceMomentMixedJet_re_neg_of_even
evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad
```

Thus `OBS-059Q` is CLOSED / PROVED BY #209. The even-selected + odd-good branch is PROVED THROUGH #209 and now carries a quantitative complete-source/local-jet anti-alignment. The simultaneous odd-bad branch and odd-selected first-bad branch remain OPEN. Endpoint-scalar sign remains OPEN.

The active research sub-obligation is `OBS-059I`: find genuinely independent complete-canonical-functional information incompatible with the #209 anti-alignment or magnitude budget on the same retained state. A rearrangement of #209 itself is not independent information. The Riesz lane is reactivated/nondegenerate on this branch, but no endpoint-scalar sign or high-order Riesz limit theorem is claimed.

Negative-root exclusion remains OPEN. **RH remains OPEN.**

## Post-#211 audit addendum — complete-functional theorem authority

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

## Post-#215 audit settlement

PR #215 passed its dedicated rigorous Arb certificate and the ordinary RHRC/Lean workflow family. Exact research disposition:
```text
FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED
FULL_SPACE_SIGN_INDEFINITE_CERTIFIED
DUAL_INDEPENDENCE_SURVIVES_Q13_Q15_CONTROLS
```
Q14 primary values:
```text
wedge  = -7.92856142933793718521707742118e-7
R_min  = -7.60547660138399452560501190345e-11
R_max  =  1.02497161190896926446719955942e-6
```

No Lean theorem changed. Theorem authority remains #213. The retained-state implication was not tested. The current active target is the exact retained negative-root cross-parity secular composition, not a universal full-carrier sign and not an unproved contact-state substitution.

**RH remains OPEN.**
