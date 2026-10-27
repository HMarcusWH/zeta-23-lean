# OPICA Unified Constraint Deduction Pass

**Date:** 2026-10-27  
**Repository:** `HMarcusWH/zeta-23-lean` / PR #295  
**Head:** `07278f01fcd17fb14d465630766a02e940abb8a0`  
**Tree:** `acd548eb97ddaee68eb6c9df73f82756ee10d13f`  
**Base:** merged PR #294 `adab10a37207f75b9a8b415a0fe9eadca2e4c9aa`  
**Verdict:** **No valid Step 4 closure. RH OPEN.** This report *does* establish new conditional, source-specific and abstract deductions, narrows candidate closing inequalities, and falsifies several proposed inference patterns.

## Executive research outcome

Instead of proving 216 isolated roots again, the pass assembled one traceable constraint population across **76 original OPICA roots, 100 OPICA-follow-up roots, 40 Round 2 mandatory roots**, plus four alternative terminal targets, 13 registered research lanes, 75 scoped controls and RHKG cross-interface contacts. It then attempted to deductively compose these constraints under one hypothetical off-critical-line zeta zero, with explicit controls for source identity, domain, quantifiers, apertures, cutoff, parity, and conditional premises.

The strongest **mathematical discoveries of this pass** are:

1. **Semantic compression in retained Pair-D geometry.** Three apparent scalar inequalities are *algebraically equivalent* once two definitions are substituted, and a fourth sign follows from one of them. Under the negative source-scalar branch, the sharp radius must exceed the squared center by a strictly positive, quantified amount. This reduces rather than closes the independent-constraint search. See `proofs/01`.
2. **Observation-dimension threshold.** A homogeneous real positive-observation family separating a full `n`-dimensional amplitude space requires at least `n+1` scalar tests, and that count suffices in abstract linear algebra. Current S17's actual finite Schwartz tests do not prove that an equally strong arithmetic observation family exists, nor a margin uniform in dimension. See `proofs/02`.
3. **Pole-neutral rank-one inertia restriction.** On each *actual* parity sector, the two physical pole moments reduce to a single complex linear functional; imposing neutrality can remove at most one negative direction from the *complete canonical* Hermitian form. Existing full-form negativity at rank two would survive at the same aperture, cutoff and parity. See `proofs/03`.
4. **First-bad index separation.** Original `ApertureFreedom.lean` already gives a least unrestricted bad cutoff at every sufficiently large aperture under `¬RH`. Round 2 S15 supplies a possibly later neutral-bad cutoff. The earlier regular/resonant Schur theorem is not automatically attached to the neutral witness. See `proofs/04`.
5. **Negative-index plateau before neutral first-bad.** At all earlier cutoffs with no neutral bad vector, each actual parity sector of the full form has negative index at most one. This identifies an unproved source-specific *index-growth/alignment* target. See `proofs/07`.
6. **RHKG's 18 triple-interface contacts live in older first-bad CCM, not Round2.** The `THEOREM_VALUE_ERASED_SUPPORT` graph provides provenance, not a direct S15 or P04 interface theorem. The exact old dichotomy leaves a regular negative endpoint or resonant coupling branch; it does not rule out both. See `proofs/06`.

7. **Cofinal two-parity full-Weil negativity under one hypothetical zero.** S15 supplies the all-late-aperture negative parity COVER; Step123/N17 supplies unbounded negative sectors in EACH parity; exact complete-matrix and moving-neutral-kernel continuity make the parity-negative aperture sets open. Connectedness forces cofinally simultaneous even and odd negative directions at one L and common finite K. See `proofs/11`.
8. **Uniform intervals and first simultaneous cutoff.** The overlap is not merely isolated apertures. On arbitrarily late positive-length intervals, one fixed K and a locally uniform strictly negative two-dimensional full-form Rayleigh margin exist. At the earliest simultaneous-neutral-negative cutoff, at least one newborn parity has PSD neutral predecessor and an exact one-shell regular/resonant dichotomy. See `proofs/12` and `proofs/13`.

**No pair of verified same-object statements gave `P ∧ ¬P` from `¬RH`.** The exact rational controls in `tests/test_joint_constraints.py` exhibit scalar consistency for both source-sign branches. The missing Step 4 premises remain independent analytic/arithmetic claims, not premises hidden in Lean wrappers.

## 1. Evidence and authority

### Compiler and CI source

The source is the uploaded exact-head repository snapshot and separately retrieved GitHub PR data. The ZIP bundles indexed source files and current source research registers; the author's source file paths are preserved under `source/lean/` and `source/research/`. For the forty Round2 roots, `analysis/lean_exact_core_types.json` retains the exact exported theorem type strings from the authenticated current-head compiler receipt. For the 76 and 100 historical roots, `analysis/CONSTRAINT_ROOT_INVENTORY_216.json` retains registered root/source identities, **not a fresh recompile performed by this research pass**. Earlier verified CI and ancestry gates establish inherited compiler authority to their exact recorded scope.

The latest fetched PR snapshot in `evidence/HEAD_AND_CI.json` found 93 successful of 96 checks, one still running, two skipped, none failed. The two cold aggregates, full 76/100 comparison and forty-root scoped composition had previously passed, but the independent generated job was still running at this snapshot. **`full_core_compiler_verified=true` is not `full_core_accepted=true`.** The source manifest explicitly retains full-core/full-release acceptance false and RH/Step4 OPEN. No new Lean declaration was compiled here.

### Distinguish six separate evidence kinds

- **PROVED:** an exact, actually compiled Lean source statement, including all conditions in its type. A theorem of form `H → RH` does not prove `H`.
- **DERIVED:** an ordinary mathematical consequence of those types/definitions; the new consequences in `proofs/` are not individually Lean-compiled.
- **RESEARCH/REGRESSION:** an exact replay of fixed finite boxes, transcript, artifact, or older numerical observation; not a theorem about the continuum/global strip.
- **FALSIFIED:** a specific proposed shortcut is refuted by its validated countermodel or a direct finite algebra control.
- **LEAD:** a candidate source-specific inequality to test and attempt to falsify.
- **OPEN:** the independent terminal estimate or global no-exit property has not been established.

A cross-namespace `USES_CONSTANT` edge, RHKG support contact, or documentation mention is **not** a logical implication or proof of mathematical independence.

## 2. Source identities and the four alternative terminal interfaces

A hypothetical off-line zero is an **actual** element `rho` of the nontrivial-zeta-zero configuration with `Re(rho)≠1/2`; use the functional-equation reflection only as actually justified. This hypothetical same zero may initiate multiple consequences, but those consequences frequently inhabit *different spaces*:

- **A:** actual fixed signed arithmetic high observation, native rate `Theta`, and S10/S17 finite zero-profile tests. Older A03 uses a **two-copy detector**; it is not the one-copy Round2 probe unless a proved adapter is invoked.
- **B:** literal fixed-scale `sigma=1/4096` one-copy delayed source `jPlus`, target `v=c*jPlus`, completion `w=a*jPlus`, native finite columns `g_n=n^-1/2 D_(log n)w`, positive Gram and actual raw/fixed-filter residuals.
- **C:** original-detector exterior/full-loss functional and its own cofinal aperture, predecessor inverse, direct-complement and force terms. Its Schur matrix is **not** the B approximation Gram.
- **D:** complete prime-plus-Archimedean canonical Weil form at aperture L, integer cutoff K and physical pole-neutral even/odd boundary-flat coefficient spaces. S09 profile quadratic matrix is a *different* construction.

The four terminal routes in `analysis/TERMINAL_TARGETS_4.json` are ALTERNATIVES, not four premises one must prove simultaneously. The conditional closest inconsistency for each is tabulated in §6. The `analysis/CONSTRAINT_NORMAL_FORM_MATRIX.csv` expresses each major sourced constraint's eligibility, consequent, authority and identity firewall.

## 3. Full constraint harvesting versus semantic completeness

### What was mechanically indexed

- 216 roots across three rounds, each matched against source path SHA256 and named theorem; all 40 current Round2 roots have exported theorem types.
- Four registered terminal targets and their alternative sublanes.
- Thirteen research lanes with exact status/claim cap and twenty-five inherited mathematical controls plus 32 runtime controls and 18 typed formal controls (75 total).
- RHKG `CONTACT_QUOTIENT_VIEW`: 874 contacts, 185 cross-interface, 18 triple-interface; the latter are enumerated in `analysis/TRIPLE_CONTACT_DECLARATIONS_18.json`. No Round2 declaration among the 185 contacts.
- RHKG 290 document records, 1761 extra source-only public theorems, 5548 candidate identities, 401 auxiliary/standalone modules, 0 unknown file classes; these are existing source inventories, **not** declarations all studied mathematically in this pass.
- Forty new registered compiler-use dependency entries; twenty have no earlier registered dependency in the mapped *transitive USES_CONSTANT* view. Prior roots predominantly enter S11, S15 and S17. This observation is about compiler proof provenance, not theorem-rank or implication strength.

### What is NOT claimed

This was an exhaustive machine inventory of the specified 216 root IDs, **not** a manual semantic derivation of every combination of their often compound formulas, nor all 1761 source-only public theorems, nor all 185 graph contacts one by one. Selected high-leverage 18 triple-contact declarations were source reviewed; the seven scoped proof notes received exact algebraic tests and source verification. A full independent all-workflow/raw-log provider census, graph generation re-execution, or new Lean compilation was not performed. The distinction belongs in any future handoff.

The 75 records in `CONTROL_REGISTRY.json` contain source-level statuses such as `PROPOSED_NOT_IMPLEMENTED`; those are *design/manifest entries*. The later successful CI controls represent execution dispositions and must not be conflated with those older labels. The scoped 18-box K3 PASS, signed-ray failure and composite-parity falsification retain their historical scientific scopes.

## 4. Deduction UCDP-01: semantic rank compression and the radius obstruction

`Zeta23/CCM/RegularFirstBadCompletedSourceRealGeometry.lean`, `retainedRealCompletedSourceCorridor_of_even_of_not_oddBad`, concerns **one selected regular first-bad certificate** with even-selected and odd-not-bad successor. The same state has

\[
f=m-sc,\quad D=B-qs,\quad c\ge0,\ B,q>0,\quad (q-f)^2\le R,\quad B\le sf.\]

The list of separately displayed inequalities `B≤sf`, `B+s²c≤sm`, and `D≤s(f−q)` collapses to **one** inequality by substitution; `sm>0` follows from `B>0,c≥0`. The irredundant scalar content is `B≤s(m−sc)` and `(q−m+sc)²≤R`, plus native positivity definitions. This is an upstream theorem-inventory compression, not a claim that all associated Lean proofs are redundant.

If `s<0`, then `f≤−B/|s|`. Thus

\[
\boxed{R\ge(q+B/|s|)^2>q^2},\qquad
R-q^2\ge 2qB/|s|+B^2/s^2.
\]

A possible independent positive-source sign result could follow from a weaker **source-matched** sharp radius upper `R<(q+B/U)^2` coupled with `|s|≤U`, where these bounds are proved on the *same* selected-even regular/odd-good state. Neither exists now. Even proving `s>0` for this selected branch alone would not eliminate odd-selected/tied or resonant states.

Exact scalar models satisfy all listed constraints with either sign of `s`, so no contradiction follows from algebraic elimination. `proofs/01_PairD_Corridor_Constraint_Compression.md` contains both models and the check.

## 5. Deduction UCDP-02: observation separation has a dimension and stability cost

The compiled S17 `phase_complete_positive_test_observability` proves actual finite phase-sensitive test separations under its stated physical hypotheses, and a generic obstruction to too few homogeneous positive measurements. For any real linear `F:R^n→R^m`, the condition `F(a)≥0 ⇒ a=0` is impossible if `m≤n`. If `m=n`, either `F` has nontrivial kernel or is invertible and hits `(1,...,1)>0`; `m<n` has nontrivial kernel. `m=n+1` suffices abstractly via `F(a)=(a_1,...,a_n,−∑a_i)`.

This is the sharp *linear-algebra* number, not a theorem that such rows are realizable using the nonnegative Schwartz observation functions associated to the actual zero profiles. Furthermore, the simple family has unit directions with negative-observation margin only `1/√n`: finite separation cannot be promoted to a uniform-in-jet-count margin without an additional quantitative theorem.

The A-observation branch still requires actual arithmetic pairing nonnegativity and complete error/recovery budgets, not merely test functions that are pointwise nonnegative. See `proofs/02`.

## 6. Deduction UCDP-03,04,07: pole neutralization, negative inertia and first-bad quantifiers

`CanonicalPoleNeutralGeometry.lean` and `CanonicalPoleExponentialMoments.lean` identify simultaneous vanishing of two physical pole moments on a fixed even/odd carrier with vanishing of one appropriate parity functional. Thus `U_p=ker ℓ_p` has **complex codimension at most one** in that parity space. Let `Q_p(L,K)` be the **entire** actual Hermitian canonical form, with all native contributions. Dimension intersection gives

\[
\boxed{n_-(Q_p|U_p)\ge\max(n_-(Q_p|E_p)-1,0).}
\]

If the full sector has at least two negative directions, a negative *pole-neutral* vector exists at that same L,K,parity. A single negative direction may be erased; the exact synthetic controls `diag(-1,2,3)` and `diag(-2,-1,3)` show the threshold is sharp. These are **not** native zeta matrices. The source-parity negative *component* inertia from `SourceParityExactInertia.lean` is not automatically inertia of the full canonical Weil form.

`ExceptionalZero/ApertureFreedom.lean` had already proved that `¬RH` produces a least unrestricted globally bad cutoff `N_any(L)` for every sufficiently large aperture L. S15 `finite_pole_neutral_approximation` adds `∀L≫1, ∃K(L)≥3` and a nonzero legal fully neutral negative vector, at least one parity component negative. Define `K_neutral(L)` as the least eligible cutoff having such a witness. Then

\[
\boxed{N_{any}(L)\le K_{neutral}(L)},
\]

with no proved equality, same parity, or bounded separation. The old unrestricted-first-bad Schur hypothesis cannot be transferred automatically to `K_neutral`.

**New interval consequence:** For every eligible K with `3≤K<K_neutral(L)`, the neutral parity restrictions are PSD, hence

\[
\boxed{n_-(Q_{even}(L,K)),\ n_-(Q_{odd}(L,K))\le1.}
\]

If the first occurrence `K_2(L)` of two full-form negative directions in a parity sector exists, then `K_neutral(L)≤K_2(L)`. This is the exact **rank-one negative-mode corridor** that remains compatible with S15 under `¬RH`. It is not a proof that a rank-two negative direction ever appears. Read `proofs/03`, `proofs/04` and `proofs/07`.

A nested principal-matrix synthetic control shows **there is no generic bound on `K_neutral(L)−N_any(L)` from the codimension-one theorem alone**: keep a first negative diagonal direction annihilated by the pole functional and add the next negative eigenvector at an arbitrarily late new coordinate. All intermediate neutral restrictions remain PSD. The control is not an actual zeta matrix.

The high-leverage target is an *actual-source*, full-form bound on the negative-index growth or pole-normal alignment at the same unrestricted/neutral cutoff. A generic rank-one theorem alone is insufficient; direct F04/outgoing signatures still need native arithmetic.

## 7. Triple-interface contact graph and proof dependency

The current `CONTACT_QUOTIENT_VIEW.json` has 185 cross-interface roots; precisely 18 touch first-crossing germ, contact structure and production-source jet simultaneously. These are all **older CCM/ExceptionalZero declarations**. Their support projection is `THEOREM_VALUE_ERASED_SUPPORT`, which is not a direct theorem that a zero-profile observation, finite negative Weil witness and causal best residual are the same object.

`ExceptionalZero/GlobalFirstBadZeroShiftBranchResponse.lean` proves from an off-line zero that **some** aperture L has the first-bad predecessor/secular construction and a **disjunction**: a regular zero-shift negative endpoint with vanishing coupling, or a nonzero resonant coupling kernel. The theorem neither excludes both branches nor guarantees that the pole-neutral witness S15 produced at a different `K_neutral(L)` is its first-bad eigenvector. The `∀L≫1` theorem is instead the distinct original `ApertureFreedom` result.

`proofs/06_Triple_Interface_Contact_Audit.md` records the exact theorem and interface gap. Reclassifying those 18 contacts as a discovered RH contradiction would violate the claim firewall.

## 8. The four global terminal routes and their missing independent leaves

| Path | Formally established conditional obstruction | Last missing independent leaf | Closest invalid inference |
|:--|:--|:--|:--|
| A | `¬RH ⇒ Θ>0`; S11 exact damping rate, S10/S17 zero observation | Source-matched **complete** cofinal signed quiet upper, **or** proven nonnegative physical arithmetic observation with comparison error below actual profile margin | Nonnegative tests ⇒ positive signed prime observation; 57/25 subtrace ⇒ whole observation upper |
| B | `¬RH ⇒` positive residual zero-jet margin; P08–P10 finite Gram PD and exact nested projection | Literal native `d_N→0` or fixed-filter residual→0 from actual coefficient family | Monotonicity ⇒ zero limit; local Möbius exactness ⇒ global L² approximability; common convolution contraction ⇒ persistent relative gain |
| C | `¬RH ⇒` original-detector exterior/Schur loss lower on original cofinal family | Actual **full** loss upper, with forcing/direct-complement included and smaller exponent | Small predecessor inverse ⇒ small total loss |
| D | `¬RH ⇒ ∀L≫1 ∃K,u` pole-neutral full Weil negative; earlier firstbad and outgoing dichotomy | An independently sourced **whole-kernel** no-exit sign or contradiction for all necessary parity/regular/resonant/tied states | Fixed K3 positivity, source-part inertia, or S09 profile self-duality ⇒ complete Weil positivity |

There is no evidence that all four targets need to be proved. Each sufficient target is an independent possible route. The four *conditional contradiction cores* are captured in `analysis/CLOSURE_RELATION_GRAPH.json` and `proofs/05`.

### Why existing apparent pairs do not contradict

- The native causal finite **Gram** is positive because it is an inner-product Gram; an *independent* canonical Weil quadratic form can be negative under an off-line hypothesis. Their carriers, source operators and normalizations differ.
- S15 negative neutral witness is existential over cutoff K and parity; historic regular contact may be at a **different** firstbad K. Do not delete the quantifier.
- Finite S17 test detection does not imply an arithmetic observation of favorable sign; the actual observation includes the full signed prime/Archimedean terms.
- Source-prefix errors, positive-definiteness and finite upper certificates are compatible with a nonzero limiting residual.
- The source-specific positive-causal twin control proves equal input-energy/power data need not determine the causal range closure.
- S09 rigid quadratic profile self-duality rules out *one specified repair mechanism*; it does not collapse the genuine S15 negative-full-Weil witnesses.
- Frozen K3 18-box PASS, signed-ray FALSIFIED and composite-parity FALSIFIED are different scientific outcomes. They do not establish all-aperture K3 positivity.

## 9. Additional registered research lanes, failed routes and scopes

`analysis/RESEARCH_LANES_13.json` preserves thirteen explicit historical lanes: autocorrelation signed covariance, Suzuki orbit, corrected prime-prefix OPEN-X, forced-profile boundary sampling, full-contact critical-line representers, conductor/summation ideas, quantitative contact adapters, external reported ceilings and out-of-scope cross-framework controls. Some are source-native, some two-copy, some conditional on unverified external claims. Their statuses are reproduced **unaltered**; none supplies an unconditional closing bound.

Relevant resurfacing candidates:

- **Historical Pair A, once downranked:** reopen only if a *new actual signed invariant* appears. Native short-cofactor reduction already leaves a signed composite and a pole residue; no cancellation alone yields a complete positive law.
- **Historical Pair B / negative index versus localized sampling:** the rank-one neutral compression gives a sharp finite obstruction, but same-state arithmetic source-parenthesis control is still necessary; generic algebra cannot select a branch.
- **Earlier fixed-certificate Route B:** keep the actual one-copy dictionary and the fixed B-filter residual separate, including exponentially weighted input cost and the noncompact target tail.
- **Path C original-detector Schur:** all forcing and nonlinear cumulative terms must remain in the exact loss identity; no extra positivity implied by one inverse norm bound.

The RHKG source-only and historical dead-route inventories deserve targeted follow-up, but are not claimed exhausted. External results asserting an unconditional zeta zero strip or optimal Nyman–Beurling rate are not imported without proof, and RH-conditional optimal-rate theorems remain circular as independent Step 4 upper bounds.

## 10. Fastest falsification and next experimental/theorem campaign

**Priority 1 — D: full canonical parity inertia and pole-normal alignment at the same firstbad state.** Build a source-honest finite calculator that evaluates the *entire* canonical Hermitian form, its parity negative index, the pole functional, neutral compression and singular mode alignment for a fixed (L,K). Compare `N_any(L)`, `K_neutral(L)`, earliest rank-two cutoff K2, and regular/resonant Schur states. Verify exact-domain, predecessor PSD and all source/prime terms. Synthetic diagonal controls should be mandatory. The crucial mathematical decision: does a source-native invariant force an impossible rank-one corridor or a contradictory outgoing sign? No universal assertion is claimed.

**Priority 2 — D: radius excess versus arithmetic bound.** Trace native expressions for `Rsharp`, `B`, `q` and `s` in the already formally checked selected-even odd-good geometry. Test a *same-state* upper on `Rsharp−q²` against the negative-branch necessary gap. This is a smaller candidate than unproved `Rsharp≤q²`; still falsify first and retain resonant/other parity branches.

**Priority 3 — A: actual positive observation plus recovery norm.** For a real n-dimensional eligible finite jet basis, derive a source-specific physical observation family, not only `n+1` abstract rows. Use S10/S17 with exact phase and compare full signed arithmetic evaluation and error. Quantify conditioning and cost as n increases. Generic dimension sufficiency is not sufficient.

**Priority 4 — B: actual error innovations.** Use existing P19/P23 source enclosures and the actual Gram Schur block to certify a **positive lower bound on actual improvement** along one selected dictionary block. Then ask for a non-summable *arithmetically justified* gain, not just finite numerical successes. Preserve earlier local-to-global and high-norm counterexamples.

**Priority 5 — C: full original loss.** Compare same-interval force growth to complete Schur complementary upper without deleting direct-complement or exterior terms. Only a strict exponent gap can conflict with the existing lower.

Before promoting any result, check trivial aperture, degenerate parity/zero rank, nonphysical replacement kernel, possible hidden `RH` in an antecedent, coefficient normalization, source scale, changing cutoff, and synthetic examples where the desired no-bad-state conclusion fails. Each candidate must have independently typed Lean consumers, standard axiom audit, and a head-pinned compiler receipt.

## 11. Closing disposition

**What became formally true:** no new compiler-accepted theorem in this research pass; existing forty families on the checked head remain compiler-backed supporting source mathematics, release acceptance separate.

**Workflow harvest:** 24 latest-head workflow runs were observed, with 23 successful, one still running at snapshot; 93 of 96 instantiated checks successful, 2 skipped, 1 running. Research PASS/FALSIFIED/UNRESOLVED statuses are not theorem promotion.

**What changed in mathematical knowledge:** two redundant scalar inequalities eliminated, a sharp negative source radius gap, positive-test dimension threshold, neutral/parity rank-one inertia, strict negative-index cap before neutral firstbad, and explicit contrast of old triple-contact roots with Round2 S15.

**What is upstream:** simplify PairD proof dependency graph; reuse existing parity moments rather than count them twice; distinguish prior all-aperture firstbad from S15 neutral firstbad.

**What is downstream:** a smaller actual-source index-growth/alignment theorem could connect S15 to historical firstbad branches; a weaker native radius upper may exclude one branch; source-specific observation costs or native block progress might close another path.

**What cannot be concluded:** no incompatibility `¬RH⇒P∧¬P`, no independently proved global native residual limit, no all-aperture contact no-exit, and no RH proof. **Step 4 and RH remain OPEN.**

## 12. Resumed post-interruption research pass — cross-round parity-overlap consequence

**DERIVED, not newly Lean-compiled.** The detailed source-exact statements, proof, and falsification controls are in `proofs/08` through `proofs/13`, with the strongest topological composition in `proofs/11` and its open-interval strengthening in `proofs/12`. The relevant source blobs were checked directly against the published head and all eight blob SHAs matched; see `evidence/SOURCE_BLOB_MATCH.json`.

Fix **one actual** nontrivial zeta zero `ρ` with `Re ρ != 1/2`. Let `E_even`, `E_odd` be the aperture sets admitting a complete-canonical-form negative finite vector in the legal pole-neutral even/odd space, respectively. `eventually_finite_neutral_negative_of_off_line_zero` proves their UNION contains a tail interval. The source-specific cofinal original-detector theorem `exists_generatedStep123ComposedEvidencePacket_cofinal` and N17 field prove EACH negative set intersects arbitrarily late apertures, separately. `continuousOn_canonicalSourceMatrix_Ioi` includes the prime floor seams; moving-pole-kernel correction with the explicit legal nonzero normal proves EACH set OPEN. Two disjoint nonempty opens cannot cover a connected half-line. Thus the overlap is unbounded.

At any common L, exact neutral centered embeddings give negative vectors in both sectors at ONE finite K; reflection parity orthogonality gives a TWO-dimensional negative-definite subspace of the same complete prime+Archimedean Weil form. Strict negativity and continuous neutral-vector transport upgrade this to a nonempty aperture interval with fixed K and uniform local negative Rayleigh margin; the intervals can be selected arbitrarily far out. **The interval lengths, cutoffs and margins are not uniform over the cofinal family.**

Define `K_e(L)` and `K_o(L)` as the least per-parity neutral-negative cutoffs; `K_both=max(K_e,K_o)` is the first simultaneous cutoff. At `K_both`, each newly negative parity has a PSD neutral predecessor and a one-complex-dimensional shell, with **regular Schur<0 or resonant kernel coupling**. The OTHER parity may already have negative predecessors, so older two-predecessor-PSD first-bad theorems cannot be transferred automatically. Coincident cutoff indices need not give equal eigenvalues or a spectral tie.

**Could this close Step 4?** Only with an independently proved source-specific statement excluding two simultaneous negative parity directions, or a narrower exact sign restriction on the retained corrected cubic-plus-projected-output intertwining at the newborn state. `CanonicalPoleNeutralIntertwining.lean` leaves the projected-output residual explicit. Neither exclusion nor a no-exit statement has been proved. The synthetic controls realize two negative parities without contradiction, so the new cofinal condition is a sharpened necessary consequence of `¬RH`, NOT a contradiction. No Lean declaration was added.

The resumed tests: 18 finite/algebraic/topological tests passing under `pytest` (and the run should be repeated by the receiver). They do not verify any analytic theorem; exact source/CI authority remains the compiler.

### Highest-leverage next mathematical question

For an actual cofinally late common interval and its first simultaneous neutral cutoff, can a **whole-source** estimate from the prime+Archimedean entries and the *retained projected-output residual* exclude the regular or resonant newborn transition? That is the smallest identified new contact-to-Step4 test. It is **OPEN**, must be falsified on known countermodels before formalization, and cannot be assumed merely because it would prove RH.

### A weaker independent closing target than full Weil positivity

Under one hypothetical off-line zero, the cofinal simultaneous-negative result means it would suffice to independently establish the **no-simultaneous-pole-neutral-parity-negativity** condition:

`∃L1>0 ∀L>L1 ∀K≥3, ¬(EvenNeutralNegative(L,K) ∧ OddNeutralNegative(L,K))`,

with each negative predicate evaluated on the **same complete canonical** prime+Archimedean matrix and the actual physical pole-moment kernels. This asks only that **at least one** parity restriction be PSD at each (L,K); it does **not** require the full form to be PSD, and is weaker than bounding the total negative index by one (it allows multiple negative directions in a single parity). Combined with UCDP-11 it would contradict `¬RH`.

**Status: OPEN independent lemma, not a result proved or assumed in this pass.** Because RH would also imply the Weil-form positivity direction, this no-simultaneous assertion risks becoming another RH-equivalent restatement. Only a genuinely source-derived proof of the prime+Archimedean or corrected-intertwining sign restriction—not the mere equivalence—would be mathematical closure. Generic Hermitian controls and the retained output residual show why it cannot be inferred from existing rank-one identities alone.
