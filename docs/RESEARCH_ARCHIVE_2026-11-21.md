# Mathematical approach and scientific status — frozen research snapshot

**Archive date:** 21 November 2026. **Project:** `HMarcusWH/zeta-23-lean`. **Author of the listed manuscripts:** Marcus Hermansson. **Sources:** the original Git history, pinned Lean theorem modules and 43 unmodified PDF manuscripts in [the paper index](../papers/README.md).

**Research baseline:** commit [7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9](https://github.com/HMarcusWH/zeta-23-lean/commit/7597acdba0c7d0a81b8c3a5f229598e3f9b74ac9), tree `9248b76d7aff60aab3bb775c4be9750dc6006003`. The guides added after that archive explain the retained source; they do not create a new mathematical checkpoint. This repository's RH attempt, independent Step 4 estimates and final closing routes remain **OPEN**.

## Read the snapshot

| Reader question | Guide |
| --- | --- |
| What did the attempt construct, and where did it stop? | [Project guide](PROJECT_GUIDE.md) and [frozen current state](CURRENT_STATE.md) |
| Which paper result corresponds to which Lean source? | [Results and formalization](RESULTS_AND_FORMALIZATION.md), covering all 43 manuscripts and later records |
| Which parts can be used outside this attempt? | [Reusable components](REUSABLE_COMPONENTS.md), with hypotheses, import maturity and attribution |
| In what order should I read the papers? | [Paper reading routes and short titles](../papers/README.md#reading-guide) |
| What does one concrete calculation look like? | [Examples](EXAMPLES.md), including Gram witnesses, singular Schur responses, finite certificates and stopping trees |
| What evidence can I reproduce or cite? | [Reproducibility](REPRODUCIBILITY.md) and [citation](REPRODUCIBILITY.md#citation) |

The four-step narrative below explains the RH route. The reusable outputs form a second route through the archive: finite linear algebra, local analytic quotients, Fourier separation, Laplace-jet Grams, quantitative approximation and evidence tooling can be read on their own. Their applicability depends on their individual assumptions, even when the surrounding RH programme is incomplete.

## Why preserve this work

The programme was a sustained, source-specific attempt to translate the Riemann hypothesis (RH) into finite, computable, and formally auditable consequences of a hypothetical nontrivial zeta zero away from the critical line. The mathematics does not become uninteresting merely because another group has announced a proposed proof. An announced RH proof, however, must not be represented as an independently accepted theorem before the relevant checks and mathematical scrutiny are complete.

The fork begins from the Anthropic `zeta-23-lean` work on a different zeta-zero theorem. The fork's contributions and the upstream proof are distinct; see [UPSTREAM_README](../UPSTREAM_README.md), [UPSTREAM_AUDIT](../UPSTREAM_AUDIT.md), [FORK_NOTES](../FORK_NOTES.md), [LICENSE](../LICENSE) and [NOTICE](../NOTICE). In particular, the seven-file `RHLinalg` development retains its upstream authorship; the reuse catalogue does not attribute it to the fork.

## Four-step research architecture

1. **Fingerprint an off-line zero.** Use Weil's zero-side quadratic form, explicit finite Gram witnesses and the complete two-translate correlation to turn a hypothetical off-critical zero into sign-sensitive data. The explicit pair witness is constructive, but pair-local negativity alone is not full-form negativity: other zero contributions can mask an isolated block.
2. **Prove the obstruction cannot hide from every finite canonical detector.** Reconcile the exact Weil–Connes–Consani–Moscovici (CCM) source normalization and the finite Guinand–Weil dictionary. Use boundary-flat centered coefficient spaces (vanishing zeroth, first and second moments), finite Fourier approximation and centered zero extension. This produces conditional finite negative directions that persist under truncation enlargement.
3. **Synchronize and transport the same source.** Study first-bad cutoff shells, reversal parity, cubic secular equations, kernel-safe Schur complements, nonunitary cross-parity maps, real-aperture prime seams, source moments and Riesz endpoint jets. Separately, establish co-Poisson/Fourier rigidity and work with a fixed native causal source, its prime-power field, multiplicity-sensitive Laplace data and Hilbert/Gram observations. Carefully retain the real arithmetic source, sign, norm, aperture, carrier and cutoff at every interface.
4. **Find an independent contradiction.** What the preceding steps do *not* give is a new arithmetic upper/sign/positivity theorem incompatible with the conditional obstruction. The required Step 4 source restriction remains OPEN in this repository. An RH-equivalent finite criterion does not prove its own nonnegativity; negative-ground classification does not exclude negative grounds.

## Selected concrete results, with their limits

- **Closed-form local negativity:** For `B = c(xx^T - yy^T)` with `c > 0`, the witness `w = ||x||^2 y - <x,y>x` satisfies `w^T B w = -c (||x||^2 ||y||^2 - <x,y>^2)^2`. This is a precise finite theorem for a transverse pair block, not an RH proof.
- **Finite dictionary scalar-defect reduction:** On the specified smooth core, the remaining zero/deterministic matrix discrepancy reduces to one rank-one channel `delta_L * 11^T`, subsequently removed by tent mollification. The `11^T` channel is distinct from an identity-matrix normalization shift.
- **Normalization reconciliation:** Comparing literal published CCM formulas with the direct source identifies a scalar identity difference `Q_can = M_print + 2 c_print(L) I` in the conventions of that manuscript. This is presented as a narrow source-specific correction, not independent proof of priority.
- **Persistent finite detection:** A hypothetical off-line zero forces an admissible boundary-flat finite vector with negative canonical Weil value; that value survives centered extension. This is a conditional existence theorem, not universal finite positivity.
- **Parity and spectral rigidity:** The first-bad successor has a one-dimensional new cubic shell. Exact Schur/secular, cross-parity and kernel/range identities constrain negative modes; prime-entry seams are controlled through the legal compression. Later work includes conditional simultaneous two-parity negativity, source-visibility and quartic-cutoff constraints. The missing source exclusion remains independent.
- **Fourier/co-Poisson results:** Signed lattice-gap hypotheses lead to negative-mass budgets and non-repair statements for the precisely specified measure/profile classes. Actual-zero profiles carry a forced arithmetic term; deleting that term to claim self-adjoint eigenvalue exclusion would be invalid.
- **Native causal source:** Source-specific transforms, residual/memory bounds, exact logarithmic-window growth rates and finite Gram certificates distinguish obstruction detection from an opposing upper bound. An exact four-column filtered certificate excludes only a small region already covered by classical zero verification; the same raw trial has a much larger error.
- **Late research:** The signed Möbius/Mellin, regular quartic Schur-inertia and prime-phase noncollision manuscripts (Papers XXV–XXVII) sharpen exact source geometry and feasible conditional packets without establishing the independent sign estimate.

These are summaries of specific results, not whole-paper verification labels. The [result crosswalk](RESULTS_AND_FORMALIZATION.md#find-a-result) links each manuscript to representative exact declarations and states which compositions or refinements remain paper-level. The [same-source packet example](EXAMPLES.md#step123-packet) explains how the late results fit together while retaining the source, parity, aperture and cutoff.

## Final-source coverage beyond the 43 PDFs

The paper archive is complete for the source folder copied on the archive date. It is not a complete index of the repository's mathematical output. Important November developments live in Lean modules and Markdown research records, including the November 19–20 finite arithmetic and stopping programme.

| Final source family | What is present | What the reader must retain |
| --- | --- | --- |
| [Arithmetic frontier](../research/RHRC/integration/opica_round4/arithmetic_frontier/README.md) | The actual source policy, cost and compression programme, finite positivity certificates, and a hierarchy of native moment-slice bounds | Initial specifications and later theorems have different dates. Read the actual [ZeroFreeFloor](../Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean) equivalences before treating a proposed weaker bound as an independent route. |
| [Source-column core](../Zeta23/OPICARound4/ArithmeticFrontier/SourceColumnCore.lean) and [finite certificate soundness](../Zeta23/OPICARound4/ArithmeticFrontier/FiniteCertificateSoundness.lean) | Generic lower-bound transfer with full complement leakage; exact real shifted-factor positivity | The core inequality, leakage estimate and native enclosure bridge are separate premises. A numerical candidate does not supply them automatically. |
| [Round 5 parity-moment bridge](../Zeta23/OPICARound5/ParityMomentBridge.lean) | The exact sequence and finite-dimensional relations between the specified even and odd moment slices | Its namespace remains `Zeta23.OPICARound4.ArithmeticFrontier`. The centered-index map is nonunitary; dimension information alone does not transfer positivity. |
| [Round 6 finite arithmetic](../research/RHRC/integration/opica_round6/README.md) and [independent consumer surface](../Zeta23/OPICARound6/PrimeFactorPaths/Verify.lean) | Finite weighted Gram identities, selector-energy stability, native cells and whole-shell transfer, opposed-sign products and stopping-tree duality | Exact finite lemmas do not certify a uniform growing-horizon estimate or the entire analytic paper route. Preserve fixed origin, complete shells and spent partners. |
| [Parity-deficit route](../research/RHRC/integration/opica_round6/evidence/step4-parity-deficit-2026-11-20/SURVIVOR_HAAR_FINGERPRINTS.md) | A source-dependent reduction to an opposed-product estimate, with the scalar coefficient four formally accounted for | `P303_OPPOSED_PRODUCT_UPPER` and `PAPER_ROUTE_VALIDATION` remain open obligations. |
| [Nested-cut route](../research/RHRC/integration/opica_round6/evidence/step4-nested-cuts-2026-11-20/LOCAL_PRIME_GRAPH_CUTS.md) | A later growing-horizon route organized through complete cuts and persistent paths | `N20_JOINT_ARITHMETIC_UPPER` and `PAPER_ROUTE_VALIDATION` remain open. The original survivor route separately retains `ACTUAL_UPPER`. |

The [later-source result map](RESULTS_AND_FORMALIZATION.md#later-source-and-research-records) identifies exact theorem names and mapping limits. The [Round 6 constraint register](../research/RHRC/integration/opica_round6/CONSTRAINTS.json) and [constraint graph](../research/RHRC/integration/opica_round6/CONSTRAINT_GRAPH.json) retain the actual route obligations. None of those obligations is discharged by giving its name to a packet or a successful wrapper run.

### Earlier boundaries and later advances

The source history includes real advances after earlier papers marked a step open. The [supersession map](RESULTS_AND_FORMALIZATION.md#scoped-supersessions) keeps the exact scopes visible. Global arithmetic derivative transport resolves the F04 issue for the canonical even boundary-flat family, including prime seams. Paper X identifies the exact native terminal-window rate, without proving that rate zero. Paper XXIII strengthens the earlier cofinal two-parity result to eventual negativity at the prescribed original quartic cutoff. Paper XXVII selects cofinal deep packets with regularity and disjoint even/odd spectra at every cutoff from 3 through the selected deep cutoff.

The last conclusion is a selection theorem with a retained rate parameter `0 < β < |Re ρ − 1/2|`. It is not a statement that every aperture has disjoint spectra, and it gives no uniform spectral gap or source-overlap magnitude. Papers XXV and XXVI combine existing formal ingredients with new manuscript arguments; their complete analytic compositions are not newly formalized by being included in this archive.

## How to interpret novelty and verification

These manuscripts contain candidate new *source-specific* theorems, decompositions, constants, normalization identities and formal proof integrations. Many ingredients (Weil positivity, Bombieri's finite negative index, Fourier convolution, Mellin methods, Nyman–Beurling approximation, Schur complements, Jordan measures and Laguerre polynomials) have extensive prior art. Mathematical originality and priority beyond the explicitly compared literature require independent expert assessment.

`PROVED` means the exact theorem and hypotheses have a claimed pinned Lean/CI verification trail, not that every claim in an accompanying PDF was independently compiled or refereed. `DERIVED` is a manuscript-level consequence; `EXPERIMENTAL` is a bounded computation; `OPEN` is an unproved obligation. No new whole-repository Lean run or specialist referee report was performed for this archival commit.

When reading those historical labels, separate the mathematical role from the evidence status. A conditional implication can be formally proved while its premise remains open. A manuscript composition can be mathematically derived while no single Lean declaration states the complete result. A source file, an expected-type consumer, an execution log and a full acceptance receipt establish different facts. The [formalization guide](RESULTS_AND_FORMALIZATION.md#how-to-read-the-evidence) and [reproduction guide](REPRODUCIBILITY.md) explain those distinctions.

The raw [43-PDF inventory](../papers/README.md#all-pdfs-in-this-snapshot) and [metadata manifest](../papers/MANIFEST_2026-11-21.json) remain unchanged. A separately named Paper XXIV PDF was absent from that source folder; its cited code ingredients and the two older PDFs retained elsewhere are identified in [missing and partially mapped material](RESULTS_AND_FORMALIZATION.md#missing-and-partially-mapped-material). The guides expose those gaps instead of inferring an absent manuscript or an unrecorded verification receipt.

## External proposed RH proof (20–21 November 2026)

The following paragraph is retained as dated archival context. It is not a current survey of external RH research or evidence for a theorem in this repository.

Levent Alpöge reported an RH/Dirichlet-GRH proof produced with Claude and released a large Lean formalization. Early independent kernel/build checks were publicly reported, but independent mathematical review and wider acceptance were still developing as of this archive date. Reference: https://www.nature.com/articles/d41586-026-03812-7 and https://apnews.com/article/4fe8b69a891f160f9e7f0c85af8c55c8 . This separate claim is not a theorem established by this fork, and no logical equivalence between the two approaches is asserted.

## Why the archive is frozen

This snapshot preserves the actual methods, negative controls, conditional reductions, independent mathematical results, original PDF versions and open obligations. The project is archived as a research record rather than rewritten retroactively to present its unresolved Step 4 as solved. Future work, if any, should start from a new branch or release and be labeled distinctly.

**Open boundary as of this snapshot:** neither RH nor the source-specific independent Step 4 contradiction has been proved by these manuscripts. A future independent proof of RH would not erase the validity of their separately stated finite, Fourier, causal, arithmetic and formal mathematical conclusions.
