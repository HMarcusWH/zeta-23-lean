# PR #292 completion campaign — handover for the next code agent (2026-10-17)

Claim cap: **RH_OPEN**. Nothing in this handover, in the work branch, or in a
green CI run proves the Riemann hypothesis or any of the three Step 4
antecedents (A-X, B-Y, C-Schur). D2 remains **OPEN**.
`producer_complete` and `independent_assumption_review_pass` must stay
**false**. Never set them by hand.

---

## 0. Hard rules (from the user's campaign brief; still binding)

- **Do not merge PR #292.** The user decides.
- **Do not claim RH.** Green CI is not a proof of RH.
- **Do not start, retry, expand or re-scope any D2 search** (approved run
  `38569316691` failed; see §9). If D2 work becomes necessary, stop and
  present an approval request with scope, cost, missing tiles and a
  validation plan.
- **No self-certified review.** The external semantic review must come from
  an eligible GitHub account that authored neither the PR nor its source
  commits. Do not impersonate a reviewer, invent a review reference,
  fabricate an approval, or loosen `verify_semantic_review_provenance.py`.
- The 16κ theorem bounds prime forcing **in terms of** the local norm of X.
  It is not a bound on X itself and does not prove A-X/B-Y/C-Schur.
- No status-label-only fixes, no vacuous wrappers, no conclusion smuggled in
  as a hypothesis (`caller_can_supply_unproved_bridge = false` for all 44
  contract fields).
- Do not force-push, rebase or otherwise rewrite history on the PR branch
  `research/post290-step123-output`; do not overwrite concurrent changes.
- Commit generated state only under the five governed roots:
  `research/RHRC/graph/compiler/`, `research/RHRC/graph/generated/`,
  `research/RHRC/integration/generated/`, `research/RHRC/ffbbp/generated/`,
  `research/RHRC/ool/generated/`.
- Historical `.lean` review fixtures must never become active theorem roots
  (graph source-discovery firewall).
- Avoid cosmetic pushes to the PR branch: `rhrc.yml` uses
  `cancel-in-progress` and Control v2 smoke alone takes ~1h47m.

---

## 1. Where things are

| Item | Value |
|---|---|
| Repository | `HMarcusWH/zeta-23-lean` |
| PR | https://github.com/HMarcusWH/zeta-23-lean/pull/292 (DRAFT) |
| PR branch | `research/post290-step123-output` @ `64b0056ba3a64bf9fc1ed6647e2557564117e2a4` (last green head: 54 jobs = 52 success + 2 intentional skips) |
| Work branch (this campaign) | `claude/eloquent-brown-dm8n8s` @ `6fb3782` (plus this handover commit) |
| Relationship | Work branch = PR head + WIP commits; the PR branch is an ancestor, so a fast-forward is possible |
| Toolchain | Lean 4.33.0-rc2, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` only |

**Nothing from this campaign is on the PR branch yet.** All new work is on
the work branch as WIP commits (`wip(PR292/...)`). They are not registered
in `Step123OutputBindings`, the workflow target list, or the RHKG graph,
and the RHKG derived state on the work branch is therefore **stale**. Do not
push the work branch onto the PR branch until §5 (registration and RHKG) is
done, or CI will fail on freshness and module-disposition checks.

Work-branch commits after `64b0056` (oldest first):

```
4644923 wip(PR292/N14): checkpoint in-progress same-state field module (unverified)
da0d218 wip(PR292/N21): checkpoint interrupted stored-ground branch module (compiles; unverified)
98569f7 wip(PR292/N21): implementer-completed stored-ground branch certificate (unverified)
58679f0 wip(PR292/G03): typed 34-field record on one stored packet (compiles; unverified)
ccf9b43 wip(PR292/N23): singular-safe tie completion on the stored ground (unverified)
3938ce0 wip(PR292/G03): complete N01-N40 + G01-G04 record skeleton (N36-N38 pending)
0624772 wip(PR292/N36,N37): source-channel forcing identity and composed forcing-error rate (compile; unverified)
2bc6fc4 wip(PR292/MC): consume the complete output in MC02/MC14/MC15 and N21 branch facts in MC08
6fb3782 wip(PR292/G03): attach N36 source-channel identity; state that N37/N38 are still missing
```

Earlier work in this PR (already on the PR branch, green): `a73ddaf` proved
the four-history 16κ local-X bound
(`Zeta23/CCM/OriginalDetectorFourHistoryLocalXBound.lean`, T11), `e654666`
refreshed stale output-mutation evidence, `3731e66`/`64b0056` materialized
RHKG state.

---

## 2. Why this work exists (the author's source-based review)

PR comment `6216873211` (by the PR owner; **NOT** an approval, it says so)
reviewed head `64b0056` against the frozen 44-field contract
`research/RHRC/integration/post290/review_execution_2026-10-14/spec/OUTPUT_FIELD_CONTRACT.json`.
It found 37 fields with supporting components and listed seven obligations:

- **N14** `image.errors`: `Step123NativeSourceSpectralEvidence.finite_image_H1`
  bounds H1 size relative to 0, not the error against the original smooth
  trial; apply the actual rate to the stored detector with one common L0.
- **N21** `retained.branch`: MC08 only had `Nonempty PoleNeutralGroundBranch`;
  branch facts must be instantiated on the actual stored selected ground.
- **N23** `retained.tie`: produce the tied-branch output at the stored `lam`
  and stored ground, keeping the kernel component; never assert `S0 ≠ 0`.
- **N36** `forcing.source_channels`: one source-linked projected-forcing
  channel expansion (Arch, poles, four prime histories, `+eta`, approximation)
  on identical tests, plus the q*X bridge.
- **N37** `forcing.error`: compose the actual forcing-error inequality with
  the quartic H1 budget, the common threshold, and the eta/mode factors.
- **N38** `forcing.ambient_residuals`: the legal/neutral/normal/outer split
  exists only for the selected ground; build it for the ORIGINAL detector.
- **G03** `generated.native_packet`: a single producer filling every
  N01-N40 field, then re-audit the 99 APIs and 44 fields.

---

## 3. What is done on the work branch (all compile; none independently verified)

All files below elaborate with `lake env lean <file>` (exit 0, no errors),
contain no `sorry`/`admit`/`native_decide`/custom axiom/`opaque`/
`implemented_by`, and every printed footprint is
`[propext, Classical.choice, Quot.sound]`.
`check_lean_proof_escapes.py --scope promoted` passes (679 files).
Their `.olean` files were built locally with `lake build <Module>`.

### 3.1 N14 — `Zeta23/ExceptionalZero/Step123SameStateN14.lean` (326 lines)
- `Zeta23.CCM.Step123NativeOutput.detectorCoefficients_eq_paddedUnit`,
  `...detectorNativeEnergy_eq_paddedNativeEnergy`,
  `...physicalSourceError_eq_storedDetector`,
  `...physicalFiniteImage_ae_eq_paddedUnit`: identify the stored detector,
  its native energy, its physical image and `out.physicalSourceError` with
  the literal padded source objects.
- **`Zeta23.CCM.step123NativeOutput_imageErrors_commonThreshold`**:
  `∃ L0, 4 ≤ L0 ∧ ∀ β σ a (out : Step123NativeOutput β σ a), L0 ≤ L →`
  (i) physical H1 error of the stored detector's synthesis against
  `out.originalTrial` ≤ `L^(17/2)·exp(-c·rootScale L)`;
  (ii) `nativePhysicalH1Norm out.physicalSourceError` ≤ same;
  (iii) `|Re⟨A p,p⟩ − Re W(f,f)|` ≤ `(1+L)·L^(17/2)·exp(L/2 − c·rootScale L)`,
  with `c = originalDetectorRetainedDecayRate fixedScale`, constant 1. L0
  comes from `originalDetectorPaddedFinitePhysicalUnit_common_error_rates`.
- `Zeta23.ExceptionalZero.exists_generatedStep123Output_imageErrors_cofinal`
  and `..._cofinal_atLateness`: producer called at lateness `max R L0`.
- Workflow implementer reported COMPLETE. **Independent verify never ran**
  (session limits).

### 3.2 N21 — `Zeta23/CCM/Step123SameStateN21.lean` (948 lines)
- `inductive Zeta23.CCM.DetectorRetainedSelectedGroundBranch state : Prop`
  with constructors `strictEven` / `strictOdd` / `tie`, comparing the actual
  `poleNeutralEvenRayleighBottom` and `poleNeutralOddRayleighBottom` at the
  stored L and stored selected cutoff K. Each branch carries facts about
  the stored ground and stored `lam`:
  - strict even: `PoleNeutralStrictEvenGroundFacts` (R2 + SE: rank-one source
    equation `(B0−lam)D0u = S0(u)•g0`, source-moment identity and positivity,
    `S0(u) ≠ 0`, shifted ray, det identities); stored parity derived = even.
  - strict odd: `PoleNeutralStrictOddGroundFacts` (SO: adjoint equation with
    the negative Riesz source, `⟨g0,w⟩ ≠ 0`, adjoint ray); parity = odd.
  - tie: `lam = E = O`, `PoleNeutralShiftedPositivity`, and
    `PoleNeutralTiedStoredGroundFacts` (kernel compatibility, range
    membership, complementary response with kernel term; **no `S0 ≠ 0`**).
- `DetectorRetainedSchurState.selectedGround_branch` (all states),
  `...groundBranchFacts` / `...groundBranchFacts_holds` (indexed by the old
  `PoleNeutralGroundBranch` tag).
- Packet level: `Step123NativeOutput.n21_retained_branch` (main),
  `n21_groundBranch_facts`, `n21_selected_ground_branch_consumer`,
  `n21_retained_branch_package`, `n21_strictEven_selectedGround`,
  `n21_strictOdd_selectedGround`, `n21_tie_selectedGround`,
  `n21_selectedGround_shell_kernel`.
- Implementer COMPLETE; **verify never ran**. Build is slow (~5 min).

### 3.3 N23 — `Zeta23/CCM/Step123SameStateN23.lean` (612 lines; imports N21)
- **`Step123NativeOutput.n23_retained_tie`**: given only the tie equation
  `E = O` at the stored L, K, concludes
  `PoleNeutralTieRetainedCompletion out.aperture_pos K hK lam selectedParity selectedGround`:
  `lam = E`, `lam = O`, shifted positivity, nonzero vectors in BOTH shifted
  kernels (so no full inverse exists), and
  `PoleNeutralTiedStoredRetainedInverseFacts` (projected kernel
  compatibility, dichotomies `S0(u)=0 ∨ P_ker g0 = 0`, cross-parity pairing
  `S0(u)=0 ∨ ⟨g0,w⟩=0`, and a `NativeRetainedKernelComplementInverse`
  certificate: two-sided inverse on `(ker T)ᗮ`, uniqueness, strict positivity
  on the complement, `x = P_ker x + response`).
- Readouts `n23_tie_even_readout`, `n23_tie_odd_readout`,
  `n23_retained_tie_even`, `n23_retained_tie_odd`; generic
  `NativeRetainedKernelComplementInverse.of_apply`,
  `nativeKernelComplementResponse_*`,
  `poleNeutral_eigen_pair_source_pairing_eq_zero`,
  `poleNeutral_shiftedKernels_nontrivial_of_eq_bottoms`.
- Implementer COMPLETE; **verify never ran**.

### 3.4 N36 — `Zeta23/CCM/Step123SameStateN36.lean` (845 lines)
Recovered from an implementer that was interrupted before reporting; it
compiled when recovered. I appended `#print axioms` for all 25 theorems
(all clean). Key content:
- Channel definitions on the stored packet: `Step123NativeOutput.forcingTest`,
  `storedFiniteDetector`, `archChannel`, `poleChannel`, `primeChannel`,
  `fkHistoryChannel`, `spectralShiftChannel`, `approximationChannel`.
- **`Step123NativeOutput.n36_forcing_source_channels_eq`**: for every
  predecessor test `v`,
  `⟪v, predecessorForcing⟫ = Arch + Pole − κ·[(F(x−c)+F(c−x)) + sign·(F(L−x−c)+F(x+c−L))] + Shift + Approx`
  and `Pole = 0`.
- **`structure Step123NativeOutput.ForcingSourceChannels`** and
  **`Step123NativeOutput.n36_forcingSourceChannels`**: coordinate identity,
  `storedFiniteDetector = originalTrial + physicalSourceError`, expansion,
  pole zero, four literal histories, Arch as a Fourier/gammaBracket
  integral, prime-power series, spectral shift `eta·∫ f·conj(test)`,
  16κ local-X bound on the prime channel, approximation bound
  (`C_Q (1+L) e^{L/2} √(1+(2π(K−1)/L)²) + eta) · ‖err‖_H1 · ‖v‖`), and the
  q*X bridge (`P F_k = X` and `k ⋆ F_k = q ⋆ X`).
- **Not independently verified.** It has no module docstring; add one
  (what is and is not proved; no RH / A-X / B-Y / C-Schur claim).

### 3.5 N37 — `Zeta23/ExceptionalZero/Step123SameStateN37.lean` (501 lines; imports N14)
Also recovered from an interrupted implementer; compiles, 5 clean footprints:
- **`Zeta23.CCM.step123NativeOutput_imageErrors_forcingError_commonThreshold`**:
  `∃ C_Q C_W L0, 0<C_Q ∧ 0<C_W ∧ 4≤L0 ∧ ∀ out, L0 ≤ L →` (the three N14
  bounds) ∧ (stored-eta upper bound) ∧ (forcing error with stored eta) ∧
  (forcing error with eta replaced by its proved upper bound), all at the
  quartic rate.
- `step123NativeOutput_forcingError_quarticRate_commonThreshold`,
  `step123NativeOutput_forcingError_etaBound_commonThreshold`,
  `step123NativeOutput_storedDetectorForcingError_etaBound_commonThreshold`,
  `Zeta23.ExceptionalZero.exists_generatedStep123Output_forcingError_cofinal_atLateness`.
- **Not independently verified; not yet attached to G03** (see §4.3).

### 3.6 G03 part 1 — `Zeta23/CCM/Step123NativeFieldRecord.lean` (1162 lines)
`structure Step123NativeFieldRecord (out) : Prop` with one field per id for
the 34 ids N01-N13, N15-N20, N22, N24-N35, N39, N40, each instantiated on the
stored packet; `theorem Step123NativeFieldRecord.fromNative out` with no other
hypothesis. Builder's own judgment (not independent): 33 FULL, 1 PARTIAL:
- **N39 PARTIAL**: no theorem proves the original interior history is not
  identically zero. It is kept as the genuine restriction and never replaced
  by zero. Under the BUILD_SPEC §7.5 / MC12 reading ("retain, never assert
  zero") the field is satisfied; flag this to the reviewer.
- Absence clauses held by construction, not stated: N20 "no transferred
  trial moments", N24 "not both deep", N34 "no zero limit".
- N22 is stated for every vector of the even carrier at the stored (L, K);
  specialization to the stored ground lives in N21.

### 3.7 G03 part 2 — `Zeta23/ExceptionalZero/Step123CompleteOutput.lean` (~375 lines)
- `step123SameStateThreshold := Classical.choose step123NativeOutput_imageErrors_commonThreshold`
  (N14's L0), `four_le_step123SameStateThreshold`,
  `Step123ImageErrorRates out` (N14 content), `step123ImageErrorRates_of_threshold`.
- `structure Step123SameStateFieldRecord (out) : Prop` with
  `n14_image_errors` (conditional on the threshold), `n21_retained_branch`,
  `n23_retained_tie` (conditional on the genuine tie equation),
  `n36_forcing_source_channels`. **Missing: n37, n38.**
- `structure Step123CompleteNativeOutput β σ a` = `native` + `fields`
  (34-field record) + `sameState`; `Step123CompleteNativeOutput.ofNative`.
- `structure GeneratedStep123RangeObstruction ρ hoff : Prop` (G04: reflected
  right zero and Re > 1/2, multiplicity, damping bounds, transform point,
  exact Laplace order `m−1`, witness annihilates the range, exact input jet
  value, jet ≠ 0, range-closure nonmembership, residual lower bound) with
  `GeneratedStep123RangeObstruction.ofOffLine`.
- `structure GeneratedStep123CompleteOutput ρ β σ R`: `generated`
  (existing producer output), `fields`, `sameState` (on
  `generated.native`, so one retained state), `thresholds_paid :
  max R step123SameStateThreshold < L` (G02), `rangeObstruction` (G04).
  Helpers: `.completeNative`, `.imageErrors` (unconditional N14),
  `.composed` (old partial chain on the same output),
  `GeneratedStep123Output.weakenLateness`, `.fromGenerated`.
- **`exists_generatedStep123CompleteOutput ρ hβ hβρ σ R`** (Nonempty;
  inputs only ρ, `0<β<|Re ρ−1/2|`, σ, R; calls the producer at lateness
  `max R threshold`) and
  **`exists_eachPhase_cofinal_generatedStep123CompleteOutput`** (phases
  separately; no common aperture).
- The module docstring states honestly that the record is **38 of 40** native
  fields (N37, N38 missing) and unreviewed. Update it when complete.

### 3.8 MC strengthening — `Zeta23/RHRC/Step123OutputContractCheck.lean`
Names and declaration kinds of MC01-MC16 are unchanged (they are pinned in
`build_formal_receipt.py` `TYPED_CONTRACT_ROOTS`). The module now imports
`Zeta23.ExceptionalZero.Step123CompleteOutput`.
- MC02: `∃ out : GeneratedStep123CompleteOutput ρ β σ R, max R 4 < L ∧ max R threshold < L`.
- MC08: old eigenpair ∧ old `Nonempty PoleNeutralGroundBranch` ∧
  `DetectorRetainedSelectedGroundBranch out.retained.state` ∧ `∀ b, groundBranchFacts b`.
- MC14: returns `{c : Step123CompleteNativeOutput β σ out.sourceData.separation // c.native = out.native} × GeneratedStep123ComposedEvidencePacket ρ β σ R`.
- MC15: each phase separately cofinal for `GeneratedStep123CompleteOutput`.
- MC03 already contains unit norm and exact normalized physical realization
  (approximation is N14). MC09 compact-inverse hypotheses unchanged. MC13
  (actual Y nonrange) and MC16 (exactly three conditional cuts) unchanged.
- **Still to do**: MC07 should also consume N38, MC10 should consume N36,
  MC11 should consume N37 (§4.4).

---

## 4. Remaining work, in dependency order

### 4.1 Independent adversarial verification of N14, N21, N23, N36, N37
These were never verified; every attempt was killed by session limits. For
each module, a skeptical verifier (not the author) should check:
- that it compiles and has the three-axiom footprint;
- that every public theorem takes the actual stored packet
  (`out : Step123NativeOutput β σ a` or a generated packet) plus only real
  case splits or natural parameters (test vectors, the tie equation, the
  threshold), with no hypothesis assuming part of the conclusion;
- fidelity to the contract row and to the author's finding (§2);
- no forbidden identification (`original detector = selected ground`,
  `lambda = -eta`, `depth D = gap`, `legal = neutral carrier`, finite
  iteration = range membership, etc.).

Repair anything rejected before going on.

### 4.2 N38 — not started (no draft exists)
Requirement (contract: "legal projection, pole-normal residual, neutral part,
outer Galerkin residual separately"; producer "CanonicalPhysicalTrialRealization
+ OriginalDetectorNativeForcing"; consumer "no finite-to-global substitution"):
build, for the **original detector p** of the stored packet (carrier `Kd`, its
own phase/parity; NOT the selected ground and NOT the one-shell ground
complement), separate objects for:
the actual original-detector physical response; the legal boundary-flat
projection `Φ_legal*(1_[0,L] Response(p_phys))`; the pole-neutral projection;
the pole-normal residual (removed by neutral compression; it is not an
exterior residual); the outer Galerkin residual
`(I − Φ_legal Φ_legal*)(1_[0,L] Response(p_phys))`; the exact recombination
identity; orthogonality on the correct carrier; and the predecessor projection
with its connection to the actual `b_eta` (`out.retained.predecessorForcing`).
Mirror what `Zeta23/CCM/Step123NativeAmbientGalerkin.lean` does for the
selected ground (`selectedResponse_decomposition`,
`selectedOuterGalerkin_orthogonal`). Assert nothing vanishes, and do not
assume a globally square-integrable exterior response. Suggested file:
`Zeta23/CCM/Step123SameStateN38.lean`. Useful sources:
`CanonicalPhysicalTrialRealization.lean`, `OriginalDetectorNativeForcing.lean`
(`originalDetectorNativeForcing_physical_mixed`,
`originalDetector_projectedForcing_eq`), `Step123OriginalBoundaryEvidence.lean`.

### 4.3 Attach N37 under ONE common threshold
N37's theorem picks its own existential `L0` (plus `C_Q`, `C_W`). That
theorem already contains the three N14 bounds, so the clean fix is to
redefine the common threshold in `Step123CompleteOutput.lean` from it, so
that N14 and N37 share a single L0:
```lean
-- sketch
def step123SameStateConstants := step123NativeOutput_imageErrors_forcingError_commonThreshold
def step123SameStateThreshold : ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec step123SameStateConstants))
```
Then re-prove `four_le_step123SameStateThreshold` and
`step123ImageErrorRates_of_threshold` from that spec, and add
`n37_forcing_error : step123SameStateThreshold ≤ L → <N37 bounds with the chosen C_Q, C_W>`
to `Step123SameStateFieldRecord`, plus a generated accessor like
`.imageErrors`. Keep the finite-mode factor `√(1+(2π(K−1)/L)²)` at the
predecessor dimension `K−1` and the eta term visible; do not absorb them
into constants. Alternatively, use `max` of the two thresholds, but one
threshold is cleaner and matches "one common source-only threshold".

### 4.4 Finish G03 and MC
- Add `n38_forcing_ambient_residuals` to `Step123SameStateFieldRecord`;
  update the module docstring to say all 40 native fields are present (still
  unreviewed).
- Add a **separate complete typed consumer** module (for example
  `Zeta23/RHRC/Step123CompleteOutputConsumer.lean`) with one projection per
  contract id (N01...N40, G01...G04) from `GeneratedStep123CompleteOutput`,
  so "a typed consumer can access every field with its exact required
  content". The brief asks that this complete consumer be separate from the
  historical partial-component fixtures.
- MC07: add the N38 original-detector decomposition. MC10: add the N36
  channel identity (`n36_forcingSourceChannels`). MC11: add the N37
  composed rate (conditional on the threshold, or via a generated packet).
  Never weaken an existing MC statement. Keep every name and kind.

### 4.5 Mandatory 20-row mutation-matrix test (not started; no file exists)
Target: `research/RHRC/routes/R003_ccm_bridge/post290/test_mandatory_mutation_matrix.py`,
from `ACCEPTANCE_AND_TEST_MATRIX.md` §3. Each row builds an exact model,
checks that the correct statement passes, applies the mutation, and checks
that the observed label matches the expected one:
```
 1 J -> correlation transform with Q^2            SOURCE_MISMATCH
 2 pair at conj(w) / omit epsilon in p=w+eps      WRONG_TRANSFORM_POINT
 3 order m instead of m-1 for physical Y          WRONG_ZERO_JET_ORDER
 4 extra factorial / omit parity sign             WRONG_JET_COEFFICIENT
 5 totalized products at zeta pole                EXCEPTIONAL_POINT_MISMATCH
 6 swap the 6 and 12 inverse budgets              WRONG_SHIFT_BUDGET
 7 lambda=-eta or parityGap=D/3                   UNSUPPORTED_SPECTRAL_IDENTIFICATION
 8 drop D0 inverse in even shifted-ray residual   WRONG_CARRIER_MAP
 9 drop strict-odd minus / D0* -> D0 inverse      WRONG_ADJOINT_IDENTITY
10 even residual bound on an odd vector           INAPPLICABLE_BRANCH
11 neutral continuum defect set to zero           OMITTED_NORMAL_TERM
12 full detector complement -> one-shell ground   WRONG_SCHUR_SPACE
13 delete a reflected prime history / interior    INCOMPLETE_FORCING
14 actual pole-neutral residual -> legal residual WRONG_COMPRESSION
15 source positivity transported to finite ground UNPROVED_PROPERTY_TRANSPORT
16 finite inverse iteration -> range membership   MISSING_DOMAIN_LIMIT_THEOREM
17 unrun/unresolved/skipped geometry "complete"   INCOMPLETE_NUMERICAL_COVERAGE
18 stale tree/type hash, duplicate root, missing API, wrong kind  EVIDENCE_INTEGRITY_FAILURE
19 completion flags without review + typed contract  INCOMPLETE_PRODUCER
20 diagnostic UNRESOLVED counted as positivity    SCIENTIFIC_DISPOSITION_MISMATCH
```
Requirements: runnable as `python <file>` and `python -O <file>` (no bare
`assert`; raise explicitly); exit non-zero on any failure; print a JSON
summary (status, `claim_cap: RH_OPEN`, per-row label and one-line reason,
authority `EXACT_FINITE_CONTROL` / `VALIDATOR_CONTROL`, `Lean_authority:
false`). Rows 18-20 must exercise the **real** validators
(`build_formal_receipt.py`, `output_contract_check.py`,
`verify_semantic_review_provenance.py`, harvest checkers) on mutated
synthetic fixtures, as `test_output_mutations.py` does. Reuse the existing
exact controls (`test_pole_neutral_exact.py`,
`test_strict_odd_and_tie_exact.py`, `test_detector_schur_provenance.py`,
`test_inverse_budgets_and_gap_exact.py`,
`test_argon_continuum_and_roots_exact.py`, `test_actual_input_zero_jets.py`,
`test_forcing_history.py`) where they import without side effects. Do not
change old bytes of existing controls. Then add both invocations to the
"Replay exact geometry..." step of `.github/workflows/rhrc_post290_step123_output.yml`.

### 4.6 Registration (required before any PR-branch push)
For every new module (`Step123SameStateN14/N21/N23/N36/N37/N38`,
`Step123NativeFieldRecord`, `Step123CompleteOutput`, and the complete
consumer):
1. `Zeta23/RHRC/Step123OutputBindings.lean`: add the `import` and add every
   public declaration as a root `(``Name, "Module", "THEOREM"|"DEFINITION"|"INDUCTIVE")`.
   Prop-valued `structure`/`inductive` declarations are `INDUCTIVE`; `def`s
   are `DEFINITION`. Copy the pattern of the 6 roots added for the 16κ module.
2. `.github/workflows/rhrc_post290_step123_output.yml`, job
   `lean-components`, `targets=(...)`: add each module.
3. `research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json`
   `standalone_module_roles`: add each module not imported by `Zeta23.lean`
   (e.g. `"POST290_SUPPORTING_SOURCE_COMPONENT"`), otherwise the graph build
   fails with "standalone module disposition drift".
4. `research/RHRC/routes/R003_ccm_bridge/post290/prepare_field_review_package.py`
   `CANDIDATES`: point N14/N21/N23/N36/N37/N38/G01-G04 at the new
   declarations (e.g. N14 → `step123NativeOutput_imageErrors_commonThreshold`;
   N21 → `Step123NativeOutput.n21_retained_branch`; N23 →
   `Step123NativeOutput.n23_retained_tie`; N36 →
   `Step123NativeOutput.n36_forcingSourceChannels`; N37 → the N37 theorem;
   G03 → `exists_generatedStep123CompleteOutput`; G04 →
   `GeneratedStep123RangeObstruction.ofOffLine`), and add the field-record
   projections for the other 34.
5. Run `registered_theorem_binding_lint.py` and the binding build locally
   (commands in §6).

### 4.7 Clean up the WIP history before it reaches the PR branch
The WIP commits only exist on `claude/eloquent-brown-dm8n8s`. Squash or
reword them there into meaningful commits (that branch is not the PR branch,
so rewriting it is allowed), then **fast-forward** the PR branch to the
cleaned head. `64b0056` must stay an ancestor; never force-push the PR
branch.

### 4.8 RHKG derived state (expensive; do once, at the end)
After the final source change:
```bash
python research/RHRC/tools/materialize_derived_state.py --check   # expect stale; record drift
python research/RHRC/tools/materialize_derived_state.py --write   # ~70 min locally
python research/RHRC/tools/materialize_derived_state.py --check   # ~70 min locally, must pass
```
Then run the graph validation and the committed-state staleness tests,
commit only the five governed roots, and run `--check` in a **fresh clone**
of the final commit before any generator writes. Any later source edit
(even a docstring) makes `repository_files.jsonl` stale again, so finish all
source edits first. The fallback is the manual one-shot workflow
`rhrc_post292_one_shot_rhkg_refresh.yml` (it pushes generated state with
`GITHUB_TOKEN`, and **bot pushes do not trigger CI**, so CI then needs a
human-visible push or manual dispatch).

### 4.9 PR-branch push, CI and harvest
Fast-forward `research/post290-step123-output` to the final head, watch CI
to completion (≈2 h; 54 jobs at last count, with
`post287-full-k3` and `wp4-k3-fourth-order-alternative` skipped by design),
fix real failures with new commits, and harvest **every** job: exact
head/tree, gate type (formal / regression / research), status, scientific
result, change versus the frozen baseline. Do not call the PR green until
all required gates finish on the same tree.

### 4.10 Artifacts, audits, review request, report
- 10 output artifacts (`STEP123_FORMAL_OUTPUT.json`, `SOURCE_LINEAGE.json`,
  `CONSTRAINTS.json`, `NATIVE_OBSERVATIONS.jsonl`, `RESIDUAL_CHANNELS.jsonl`,
  `COUNTERMODEL_SURVIVAL.json`, `D2_CONTINUUM_RECEIPT.json`,
  `STEP4_CUTS.json`, `WORKFLOW_HARVEST.json`/`.md`,
  `STEP4_RESEARCH_HANDOFF.md`) via
  `research/RHRC/routes/R003_ccm_bridge/post290/materialize_step123_outputs.py`
  at the final head. Expect a **PARTIAL** bundle (D2 open, review pending),
  and say so; never turn a conditional theorem into a numerical witness.
- Re-audit all 44 fields (source-based, unapproved) and all 99 APIs in
  `API_CROSSWALK.json`: live compiler resolution, normalized types, kinds,
  origin modules, footprints. Name/kind matching alone is not a gate. Honor
  `REVIEW_DECISIONS_50.md`. Document any API whose natural proved form
  differs from the proposed one, rather than adding a fake alias.
- Build the exact-head dossier (`prepare_field_review_package.py`) and ask
  the user to arrange an external reviewer. Keep both flags false.
- Final report sections A-G as in the campaign brief: exact implementation,
  44-field matrix, 99-API audit, CI/graph evidence, release status split
  into seven lines, remaining human decisions (D2 continuation, merge), and
  post-green research findings (DERIVED vs LEADS vs EXPERIMENTAL).

---

## 5. 44-field status at the work-branch head (builder's view, NOT a review)

| Field | Current declaration(s) | Status |
|---|---|---|
| N01-N13, N15-N20, N22, N24-N35, N40 | `Step123NativeFieldRecord.fromNative` (one field each) | compiled, builder says FULL |
| N39 | `Step123NativeFieldRecord.n39_exterior_original` | compiled, PARTIAL (interior-not-zero, see §3.6) |
| N14 | `step123NativeOutput_imageErrors_commonThreshold`; `Step123SameStateFieldRecord.n14_image_errors` | compiled, unverified |
| N21 | `Step123NativeOutput.n21_retained_branch`; record field | compiled, unverified |
| N23 | `Step123NativeOutput.n23_retained_tie`; record field | compiled, unverified |
| N36 | `Step123NativeOutput.n36_forcingSourceChannels`; record field | compiled, unverified |
| N37 | `step123NativeOutput_imageErrors_forcingError_commonThreshold` | compiled, unverified, **not attached** |
| N38 | — | **not started** |
| G01 | `GeneratedStep123Output.beta_pos/beta_below/offLine` | existing |
| G02 | `GeneratedStep123CompleteOutput.thresholds_paid` + `native_aperture_bound` | compiled (N14 threshold only until §4.3) |
| G03 | `exists_generatedStep123CompleteOutput` | compiled, 38/40 native fields |
| G04 | `GeneratedStep123RangeObstruction.ofOffLine` | compiled |

---

## 6. Environment notes and gotchas

- `export PATH=$HOME/.elan/bin:$PATH`. Check a file with
  `lake env lean <file>` (reuses `.olean`s, writes nothing). A module that
  another file imports needs its own `.olean`: `lake build <Module>`.
  Building only the new module is safe; avoid `lake clean`, `lake update`
  and `lake exe cache`.
- Bindings and receipt, as in CI:
  ```bash
  export POST290_CHECKED_HEAD="$(git rev-parse HEAD)"
  export POST290_CHECKED_TREE="$(git rev-parse HEAD^{tree})"
  lake build Zeta23.RHRC.Step123OutputBindings
  lake env lean Zeta23/RHRC/Step123OutputBindings.lean > /tmp/post290-bindings.txt
  python research/RHRC/routes/R003_ccm_bridge/post290/build_formal_receipt.py \
    --log /tmp/post290-bindings.txt --out /tmp/STEP123_FORMAL_OUTPUT.json
  ```
  Without the two env vars the bindings build fails with "Missing
  POST290_CHECKED_HEAD compiler context". `build_formal_receipt.py` refuses
  a dirty tree, so commit first.
- Other local checks: `python research/RHRC/closure_batch/check_lean_proof_escapes.py --scope promoted`,
  `python research/RHRC/tools/registered_theorem_binding_lint.py`, and the
  exact-controls test list in the workflow (each run normally and with
  `-O`). Python deps: `research/RHRC/routes/R003_ccm_bridge/requirements.txt`.
- RHKG `--write`/`--check` each take about 70 minutes locally. Do not
  `pkill -f source_only_dependency_extract` from a shell whose own command
  line contains that string: it kills itself (exit 144).
- New standalone modules must be listed in `SEMANTIC_CLOSURE_CONFIG.json`.
- `build_formal_receipt.py` pins `API_CROSSWALK.json` and
  `OUTPUT_FIELD_CONTRACT.json` by blob SHA. Never edit those frozen specs.
- Lean pitfalls seen here: pass `(μ := volume)` when `IsLocallyFiniteMeasure ?m`
  gets stuck; Hölder (`integral_mul_norm_le_Lp_mul_Lq`) wants equal codomains,
  so apply it to `fun x => ‖g x‖`; `HasCompactSupport.intro` needs `(K := ...)`;
  `simp` may rewrite `Real.exp` to `cexp`, so use explicit `show` + `rw`.
- Session-limit lesson: this campaign repeatedly hit account usage limits
  after ~20 minutes of 4-5 parallel agents, which killed agents mid-task.
  Run at most one or two heavy agents at a time, checkpoint drafts into the
  repo (WIP commits on the work branch) often, and push the work branch
  (pushes to it trigger no CI; every push trigger is filtered to the PR
  branch).

---

## 7. D2 (frozen; do not touch without authorization)

- Approved run `38569316691` **failed**: 213 unresolved Q14-even pieces
  (44 islands) and 183 checker shards never executed. There is no complete
  both-parity K3 continuous-window NON-PARTIAL certificate.
- The green 18/18 frozen K3 box replay is not that certificate.
- Allowed without new authorization: inspect receipts, verify artifact
  integrity, reconcile ledgers, list unresolved/unexecuted pieces, read
  checker code, prepare a continuation spec with cost estimate
  (`research/RHRC/integration/post290/review_execution_2026-10-14/spec/D2_CONTINUATION_AND_RELEASE.md`, `research/RHRC/integration/post290/D2_CONTINUATION_PROTOCOL.json`),
  and run cheap source-equivalence/regression checks. Not allowed: any new
  D2 numerical run, retry of the 460-child campaign, budget or scope change.

---

## 8. Release status at handover

| Gate | Status |
|---|---|
| Core source-faithful producer (N01-N40, G01-G04) | IN PROGRESS: 38/40 native fields in one record on the work branch; N37 to attach; N38 missing; nothing verified |
| Three conditional Step 4 consumers | theorem-backed implications (`riemannHypothesis_of_any_step4_output_cut`); premises A-X, B-Y, C-Schur OPEN |
| 44-field source-based audit | pending at the final tree |
| Authenticated external approval | NOT OBTAINED; `independent_assumption_review_pass = false` |
| D2 NON-PARTIAL | OPEN (run 38569316691 failed) |
| Final exact-tree CI | last green at `64b0056`; the work branch has not run CI |
| Merge | not authorized; the user decides |
