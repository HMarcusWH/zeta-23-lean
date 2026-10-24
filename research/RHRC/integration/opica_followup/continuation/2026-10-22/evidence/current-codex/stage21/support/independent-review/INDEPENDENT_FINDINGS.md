# Independent source-contract review — OPICA follow-up

Status: **UNAPPROVED FINDINGS; NO REVIEW SEAL; NO RELEASE ACCEPTANCE**.

Reviewer: a non-author model subagent assigned only read-only semantic/type/domain review. I have not implemented any theorem, edited production source, changed a registry/type table/review status/CI file, issued a PR, or pushed anything. Files written by this review are confined to `work/audit-independent-contract-review/`.

This report concerns the exact original 100 primary roots and 28 acceptance units. It does not promote RH, Step4, the independent closing inequalities, aggregate acceptance, full-release acceptance, or independent human review.

## Review authority: exact wording and its limits

The relevant production file is `research/RHRC/integration/opica_followup/build_receipt.py`.

* Lines 312–314: “No all100 semantic/type review has been accepted. This is intentionally unset; filling it requires an independent review, never copying a producer's digest.” `FULL_REVIEW_SHA256` is `None`.
* Lines 389–392: the reader consumes “a separately sealed semantic review, never infer it from a receipt.” It also says test-only seals do not establish mathematics, and names/source presence cannot establish adequacy.
* Lines 401–405 require the exact status `INDEPENDENT_EXPECTED_TYPES_AND_PHYSICAL_DOMAINS_REVIEWED`, scope `FULL_100_ORIGINAL_ROOTS`, 100 roots, 28 units, the frozen input hashes, and RH/Step4/independent closing inequalities OPEN.
* Lines 425–431 bind the complete mathematical/consumer source inventory to its exact bytes.
* Lines 432–470 require every original root in order, each frozen-contract digest, a full type digest, the independently stated expected consumer, at least one actual physical/domain consumer, and a written actual-domain review. Every consumer must have its independently reviewed full type and exact source location.
* Lines 474–487 also require every canonical required definition, its declaration kind, type, semantic origin, and separately sealed relocation amendment where applicable. A table of 100 theorem names cannot substitute for this.
* Lines 489–507 require all 28 frozen units and their complete root/consumer coverage.
* Lines 756–774 additionally require actual compiler-use paths from consumers to assigned roots. The comment at line 757 states: “Actual compiler use is necessary, but does not replace semantic review.”
* Lines 836–841 require even a full compiler receipt to retain `release_ready=false`, `full_release_accepted=false`, RH/Step4/closing inequalities OPEN and `independent_human_review=NOT_ESTABLISHED`.
* Lines 1051–1052 explicitly state: “Explicit expected-type consumers compiled; agent review is not independent human review”, followed by human review NOT_ESTABLISHED.

The frozen `BUILD_SPEC.md` reinforces the distinction. Line 35 says the parent requirement is “not human independent review by fiat: compiler authority and human review status remain separate”; a pending independent review must remain pending despite passing compiler gates. Line 745 requires an independently written intended expected type and rejects a copied inferred actual type. Lines 913 and 919 refuse auto-approval of independent human review and require expected-type review plus physical consumers alongside compiler authority.

**Authority conclusion:** the inspected full-review schema and frozen specification do not explicitly restrict semantic review to a human or an external service, and do not authenticate a reviewer identity. A genuine non-author model review is not textually excluded as review input. That absence is **not permission to declare the review accepted or set the seal**. This review supplies findings only. It does not constitute independent human approval, and does not establish that every mandatory release clause has been satisfied.

## Exact source scope and provenance

The machine-readable snapshot is `all100-semantic-review.json`. It records:

* HEAD `36b677c26b01fafeac719413753092c5988c38d3`, its committed tree, and the actual dirty working-tree status during this review.
* Exact SHA-256 for all 43 frozen module paths, including mathematical facade, Validation and audit exporter, plus every separate continuation consumer read by the inventory.
* All four frozen governing input hashes. These match the frozen constants in the full builder:
  * `BUILD_SPEC.md`: `cacab08834aeb9badd578d90828be99cff33c7a617c609e75bb878eb5fa3b29c`.
  * `BUILD_MANIFEST.json`: `c99ec7acbfe996455525b31088a7d04addd20653787e12098e4e51a4a7ce296e`.
  * `PUBLIC_ROOTS.json`: `2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41`.
  * `PAPER_CROSSWALK.json`: `9e1252631f26fb81f4a5c60ac714e483c076be5c9858e25056e3835933ce6451`.
* Every original full theorem contract, actual extracted production signature, actual path/line, specific semantic note, and discovered continuation-consumer sources.

The owner supplied the newly installed `FiniteSpanSeparation.lean` hash `8e69e7c90abb572cf45d71bd70c0446b6844372d4ae954aeb8274ea3e1f1e5ef`; this review independently matched it. `Consumers.lean` was first inspected at `132452d55d800e6889df6df5dc6c828ed99f9e5333339d269ced45188e1e5482`, then corrected by the owner to `3098cbda01dfb1e89c3b3505365c1b60f3f15b0b6d3c35a054c7ee38f16530c8` solely to restore the Fourier/Schwartz notation scope. The first aggregate build error is not a pass. The source snapshot must be refreshed after a clean final commit; a dirty working tree is not a full compiler receipt.

`ALL100_REVIEW_MATRIX.md` is the readable all-100 matrix. The extraction scripts are read-only over production; their output is review input, not a type hash approval or kernel check. In particular, the public finite-span theorem is the second same-short-name declaration in its file. The internal theorem at line 231 is narrower than the public `Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero` at line 461. The review resolves that distinction explicitly; short-name matching must not substitute for compiler-resolved full identities.

## Confirmed findings requiring action

### F1 — R2-S3 has a genuine physical-construction gap

Source pins: `SquareDefect.lean` lines 79, 274, 277, 470, 538 and 550; frozen `BUILD_SPEC.md` R2-S3 at lines 593–609 and module responsibility in `BUILD_MANIFEST.json` line 1112.

`squareGapMeasure` is currently a raw function on Schwartz tests:

`(integral |A-h|² * test) - |A|² * punctured-lattice sum`.

The square roots establish meaningful test-function identities, a test gap and test positivity, bounded density, continuous real defect, positive defect at the origin, and the gap-filling projection identity. The actual function construction is explicit, so this is not an opaque assertion of the desired Fourier conclusion.

However, the frozen group requires an actual square **measure**, exact origin/gap/sign properties, and its physical/domain consumers. At the reviewed snapshot there is no actual `LocallyFiniteSignedMeasure` square constructor with canonical Jordan parts, mutual singularity, linear total-variation growth, zero singleton origin mass, off-lattice nonnegativity, and an identification of its distribution with `squareGapMeasure`. Searches across all OPICAFollowup sources and `ExpectedSquareDefect.lean` did not find such an adapter. Test positivity is not itself the required actual Jordan-measure construction.

The owner has assigned a separate implementation lane to construct this adapter. Its outside-checkout candidate is not accepted evidence and does not resolve this finding until installed, independently checked at its exact source hash, and incorporated into the full physical review.

### F2 — R2-S3's arbitrary actual correction domain is not yet bound

`square_no_lattice_repair` quantifies `c : ℤ → ℂ` with `TemperedLatticeWeights c`, namely an explicit polynomial pointwise coefficient bound, and uses the raw `latticePairing c`. Its proof uses a legitimate periodicity/continuous-defect argument rather than assuming the no-repair conclusion.

The frozen clause says no lattice-supported tempered **order-zero measure** repairs the square. The reviewed source does not include the bridge from an arbitrary actual locally finite lattice-supported complex/signed measure with tempered order-zero distribution to polynomially bounded atomic coefficients and equality of its actual pairing with `latticePairing`, nor a complete actual-measure construction in the reverse direction. This encoding is mathematically natural, but equivalence must be demonstrated or explicitly reviewed in the agreed domain. A square-Jordan constructor by itself does not close this separate arbitrary-correction-domain clause.

This is a domain-coverage obligation, not a claim that the existing polynomial-weight theorem is false or kernel-invalid.

### F3 — Seven required canonical public definitions remain absent

Source pins: frozen `BUILD_MANIFEST.json` lines 595–600, 650–655 and 1217–1222; full builder lines 474–487. Exact-token searches confirm the following required names are absent at this snapshot:

* `finiteEulerFilter`, `inverseFiniteEulerFilter`, `rationalCausalFilter`, `truncatedInverseResidual` in `NativeFilters`.
* `optimalRecoveryCost`, `orthogonalRecovery` in `JointObservation`.
* `FollowupNativeOutput` in `Consumers`.

This is not evidence that all seven mathematical constructions are missing. The existing source already contains:

* Actual `NativeCausalState.finiteEulerAction` at line 849, `inverseFiniteEulerAction` at line 1306, `rationalAction` at line 730, `residualPowerAction` at line 1037 and its real-cutoff adapter at line 1101, with physical safe-half-plane transforms.
* Inverse Euler actions constructed through genuine primewise geometric delays, without imposing incorrect global finite variation on the infinite inverse filter.
* The recovery ratio supremum and actual range-factor/orthogonal-projection construction inside `joint_recovery_optimal_norm`, including the zero-target convention. The generic noise theorem then gives the optimal bound when composed with that construction.
* Existing `GeneratedStep123CompleteOutput` and its same-source physical view in the word/jet consumer.

The frozen exact canonical inventory nevertheless remains mandatory. A genuine named interface can expose the already proved construction, but its declared type, actual semantic origin and physical identities must be reviewed; a convenient name alias alone is not completion authority. The frozen text does not prescribe a unique elaborated Lean type for these definitions. It requires actual local causal action semantics, correct domains and exact recovery/output semantics.

Corrections made during review: `dilatedComb` is **present** as an abbreviation at `DilatedComb.lean:305`; it must not be listed missing. The newly installed public `zeroJetRealSpan` is **present** at `FiniteSpanSeparation.lean:456` and points to its actual Jordan construction.

### F4 — The production expected-type module still covers 41 expected names

At the snapshot, all 100 original primary declaration bodies are present in production source. Only 41 frozen required expected-consumer names appear in production `Validation.lean`. The remaining narrow continuation consumers live in separate namespaces and files; the new finite-span review consumers are still outside the production full-100 module.

The outside-checkout `work/audit-release/overlay/Zeta23/OPICAFollowup/Validation.lean` explicitly calls itself “UNACCEPTED explicit consumer assembly proposal” and “mechanically relocated source, not independent review, a full compiler receipt, or release authority.” `consumer-proposal-map.json` likewise says `UNACCEPTED_MECHANICAL_PROPOSAL`. These qualifications are correct and must remain. Full source-signature companions mechanically retaining root types are useful diagnostics, but do not independently establish the omitted physical clauses or reviewer approval.

The full builder requires every assigned expected/physical consumer in the canonical Validation namespace, actual compiler-use paths, full independently reviewed consumer types, exact source hashes and the separately accepted full review. Consumer existence in an external overlay is preparation evidence only.

## Newly installed finite-span roots: semantic assessment

The new code appears compatible with all three original finite-span root contracts at source level.

`JetDatum` is an explicit complex coefficient, actual zero parameter and jet order. `ValidJet` requires actual `riemannZeta rho=0`, the full nontrivial strip and order below the actual `zeroJetOrder`. `actualZeroJetSum` scales and adds genuine normalized complex jet measures. The real Jordan part then includes arbitrary real and imaginary scalar projections. Neither measure status, selfduality, growth, gap, coefficient exclusion nor negative-mass positivity is assumed as a conclusion-bearing field.

The public root at line 461 contains both finite-combination measure-zero and independent-real-basis coefficient-zero clauses. The independent-basis premise is the mathematically necessary one; it does not suppress arbitrary finite combinations from the first clause. Reflection duplicates are handled upstream through the actual kappa quotient in `ConfluentProfiles`, rather than asserting independence of equal reflected nodes.

The budget at line 935 uses one fixed actual independent real basis, `EuclideanSpace ℝ (Fin n)` coefficients, and the actual global sinc-weighted Jordan negative measure off the integer lattice. Its proof builds a genuine finite signed measure after sinc weighting, proves injectivity, and obtains a positive lower constant from finite-dimensional compactness. The zero-dimensional case is addressed in the supporting compactness lemma. No constant is asserted uniformly across colliding or increasing bases. The signed sinc balance proves the necessary evenness of negative mass, rather than assuming it.

The appended `actual_zero_measure_span_consumer` supplies actual profile regularity, actual jet identity, real-measure growth/selfduality/unit gap and separator use. It does not accept an arbitrary isMeasure/selfdual/sign packet. This assessment is not fresh compiler verification: the corrected production build and canonical explicit consumers remain necessary.

## Preserved mathematical boundaries and adversarial checks

The all-100 source-signature comparison found no confirmed added simplicity premise, positive minimum zero displacement, rightmost-zero assumption, native rate premise, globally finite substitute for locally finite measures, or desired native sign/selfduality conclusion hidden inside a packet.

Specific boundary checks matter:

* Fixed and moving source rate roots retain arbitrary multiplicity. MS1 quantifies arbitrary cofinal real horizon sequences, not only sequences positive at every index; eventual normalization remains an implementation detail.
* The actual source is the literal differential family of the parent's one-copy source; the fixed arithmetic application uses order one, Pj, not an easier different source.
* Weighted mixing retains strict exponential threshold a>1/2 and distinguishes endpoint density supremum from a<b measure integrability. It does not claim critical-tail or all-renormalized mixing impossibility.
* The actual zero-jet and determinant roots use distinct kappa nodes, with rho and 1-rho identified. Their constants are not uniform at collisions.
* The first-cell sign control also applies on the critical line; therefore sign failure is not an off-line-zero exclusion.
* Sample positivity retains the undivided identity at conjugate coincidence. Nonreal denominators are explicit, and no reality of the actual sample defect is silently assumed.
* The generic boundary-amplitude profile solves the same forced equation even when zeta(rho) is nonzero. Thus the spectral/Gram representation cannot supply a homogeneous eigenvalue contradiction or independent zero exclusion by itself.
* The conditional quiet-observation consumer visibly assumes a cofinal zero-rate upper for the complete actual signed observation. The separate physical consumer explicitly shows this upper is equivalent to Theta=0. Rephrasing it is not an independent estimate, and finite quiet prefixes do not establish the cofinal upper.
* The normalized near-gap comb limit contains nonzero delta derivatives and leaves the order-zero measure class. It cannot be fed to a measure separator after discarding divergent normalization cost.

## Post-review research state

**What became formally true:** this review creates no theorem authority. The prior 41-root source-bound subset and 56 narrow gates retain their historical/source-specific evidence. All 100 root bodies are now present in a dirty production working tree; the last three need their corrected exact-source formal gate. No full current-tree theorem inventory is accepted by this report.

**Workflow harvest:** this review has not performed the complete live GitHub job harvest. Parent/owner workflow work remains separate. An initial aggregate source build failed on missing notation scope; its error-recovery/sorryAx output is a failed diagnostic. A corrected build was still running when reported. External overlays and successful fixture tests remain preparation/regression evidence, not a full mathematical release.

**What changed:** the last three finite-span bodies are source-compatible with their full original domains. The review exposed actual-square construction and arbitrary correction-domain obligations, plus seven canonical public interface omissions. These findings do not retract narrow kernel-valid theorems; they prevent overclaiming full contract adequacy.

**Upstream implications:** the actual complex Jordan arithmetic supports a clean finite-span realification API. The sinc-weighted signed norm compresses the fixed-basis budget proof into a reusable injective finite-dimensional map estimate. Public filter/recovery names should expose the already proved physical constructions with their exact domains.

**Downstream implications:** after exact-source verification, finite-span sign exclusion and the fixed-basis budget constrain actual finite zero-jet measure constructions. The square companion can connect its currently functional Fourier obstruction to the same actual measure API.

**Resurrected routes:** controlled finite-dimensional measure constructions are now more testable; an uncontrolled normalized distributional limit remains excluded for the same reason. No broad nonlinear or infinite-dimensional route is ruled out by these finite-span/square controls.

**New RH-relevant clues — LEAD/HYPOTHESIS:** a useful future object would quantitatively map the actual complete arithmetic observation into an admissible actual measure while independently controlling sign, duality defect, gap deficit and normalization cost. The current roots give constraints on such a map; they do not construct it or bound all costs.

**Falsification checks:** first test such a map against the generic nonreal forced-resolvent controls, critical-line sign failures, colliding/growing jet bases, lattice-origin mass, and normalized delta-derivative limits. Reject a proposed cost estimate if its hidden premise simply restates the missing quiet upper or native boundary exclusion.

**Highest-leverage next moves:** close the genuine square and arbitrary-correction domain adapters; expose and check the seven exact canonical interfaces; install complete independently assessed expected/physical consumers; pin a clean exact source tree; then run the cold full compiler/type/axiom/dependency protocol and complete workflow harvest. Keep semantic acceptance, compiler validity, human review and release acceptance separate throughout.

RH **OPEN**. Step4 **OPEN**. Independent closing inequalities **OPEN**. Aggregate acceptance **OPEN**. Full release **OPEN**. Independent human review **NOT_ESTABLISHED**.
