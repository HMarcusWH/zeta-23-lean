# RH post-#268 audit: repository, graphs, history, workflows and proof search

**Date:** 25 September 2026  
**Repository:** `HMarcusWH/zeta-23-lean`  
**Audited commit:** `ab545e71bfb1b11c647597bee014fad6d9ac291a`  
**Audited tree:** `0fdd3151c86989f7cf7123be322b3968e89e3263`  
**Conclusion:** Existing formal infrastructure is substantial and the tested graph machinery is consistent. This audit derives a useful simplicity theorem, supplies an exact weight-sign counterexample, and isolates a precise conditional route to RH. It does **not** establish its final arithmetic estimate or prove RH.

## 1. Executive findings

The ZIP reconstructs exactly the live post-#268 source tree. A second end-of-audit SHA-256 comparison found no changes to any of its 1,207 tracked source files. Repository-wide graph census, deterministic graph checks and the main Python suite passed. The main suite contains 306 distinct unit tests; repeated runs are not counted as new tests.

The graph has 19,125 nodes and 296,976 relations. There are no duplicate node IDs, duplicate relation IDs, missing relation endpoints or import cycles. The 13 nontrivial cycles in the raw constant-reference graph are datatype/constructor relationships, not circular theorem proofs. All three OPEN registered claims remain without PROVES edges.

The important limitation is semantic, not a broken graph: historical PR/workflow provenance, dead-route revival semantics and a full multi-axis authority resolver are explicitly deferred. The graph is not yet a complete proof-search model of every historical mathematical obligation. Likewise, 680 source-only public theorem candidates are a visibility population, not 680 missing proofs or independent routes to RH.

The main new mathematical consequence found in this pass is:

> For L>0 and legal successor size, the complete boundary-flat ground eigenspace is one-dimensional exactly when the even and odd parity bottoms differ.

The rank-one parity intertwiner proves this by an elementary resolvent argument. This is DERIVED, not yet separately Lean-checked. It gives the unconditional ground atlas a substantially cleaner multiplicity split: strict branches have a unique ground line; ties require the whole ground subspace.

The main falsification is an exact real-even boundary-flat vector at K=4 whose primitive-source derivative is negative at w=1/8, while its prime-test weight still has the positive eighth-order endpoint jet. It therefore rejects the carrier-wide implication “flatness + even parity + positive leading jet -> nonnegative weight.” It is not an RH counterexample and has not been shown to be a ground eigenvector.

The most precise closing route extracted from the current stack is a cofinal spectral-certificate route. Prove exact lower bounds tending to zero along unbounded Fourier sizes, at an unbounded sequence of apertures. Existing N-antitonicity forces all finite bottoms at those apertures nonnegative; aperture freedom then excludes an off-line zero. The final uniform arithmetic bound is OPEN and RH-strength. Merely stating this criterion is not a proof.

## 2. Scope: what was and was not inspected

The audit used the supplied ZIP as its executable source, live GitHub for source/merge/workflow authority, retrievable project conversation history, the supplied historical audit and handovers, the post-#247/post-#250 programmes, and selected external primary research. It combined repository-wide mechanical inspection with close reading of the load-bearing Lean definitions, source identities, terminal seams, graph builders, registries, fixtures and workflow implementations.

It did not obtain a full account-wide chat export. Retrieved conversation records are not a substitute for every message in every historical thread. The archive contains no historical `.git` database; a local index was created only to reconstruct the tree and support the repository census. This is not an all-commits/all-PR-diffs reconstruction. Historical notes were checked against current source where they affected the proof path, rather than accepted as current authority.

There was no local Lean/lake toolchain and python-flint was unavailable; a dependency installation attempt failed. Consequently this report relies on live CI for existing formal compilation and reports the local Arb-dependent checks as blocked. A timeout and a concrete path-portability failure are separately recorded. No claim is made that every numerical workflow was independently rerun locally.

The report distinguishes:

- **PROVED:** existing exact statements backed by the inspected Lean/CI authority;
- **DERIVED:** ordinary consequences proved in the accompanying notes, not newly compiled;
- **EXPERIMENTAL SIGNAL:** finite numerical observations without theorem authority;
- **LEAD / HYPOTHESIS:** an attempted route with named remaining premises;
- **OPEN:** not established.

The generic host/governance, FFBBP, OoL and other domain architecture is used as an audit/search discipline. It is not imported as authority over analytic number theory.

## 3. Exact source and CI identity

| Object | Identity |
|---|---|
| ZIP SHA-256 | `b8cc6843ccb7788afa5e787f367df4aa96f404319234268d543b8be324ac9a54` |
| ZIP/live main commit | `ab545e71bfb1b11c647597bee014fad6d9ac291a` |
| ZIP/live main tree | `0fdd3151c86989f7cf7123be322b3968e89e3263` |
| PR #268 final materialized head | `8bb0f5f7b6c778d58bf9a30810fa9f1db29d7e5e` |
| Head associated with the 15 checks | `8c6c49cff82d4dec1b5d496089f0d644fe72ab88` |
| Ordinary CI synthetic checkout | `40024eb14f2b220e5d5f0d64a2f1920273df4dd7` |
| Shared pre-materialization/checkout tree | `5ff508904a92ee936edf10600e86f30f77ece30b` |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc2` |
| Mathlib revision | `51e6992efd06126df61a496bebf8f49482a4e129` |

PR #268 was merged on 25 September 2026 at 15:16:54 UTC. Its final bot head and merge commit have the same source tree. All 15 attached jobs, across 12 workflow runs, completed successfully. They are associated with the pre-materialization head, not fresh checks on the final merge SHA.

This distinction is resolved more precisely than in the earlier chat reply. The ordinary synthetic checkout tree equals the pre-materialization head tree. The materializer ran its steady-state gates and committed the generated state. The comparison from that head to the bot commit contains generated evidence/product updates and removal of the temporary materializer workflow, with **no Lean source changes**. Thus the tested mathematical source survives into the merged tree; the final bot/merge SHA still must not be described as having a separate 15/15 check run.

Relevant live anchors are the GitHub branch/commit endpoints, the comparison

`8c6c49cff82d4dec1b5d496089f0d644fe72ab88...8bb0f5f7b6c778d58bf9a30810fa9f1db29d7e5e`,

and materializer run `36146664275`, job `108109427730`. The local identity and final-integrity receipts are in `results/`.

The inspected root axiom outputs for the new carrier hierarchy and terminal equivalence use the standard `propext`, `Classical.choice`, and `Quot.sound` surface. This is a statement about those audited declarations and gates, not an assertion that every imported declaration in the entire upstream ecosystem has been independently audited here.

## 4. Local test results

The 21-command primary batch all passed. It includes `run_suite.py`, deterministic graph regeneration, graph validation, the graph/FFBBP/OoL/runner/control/integration unit suites, assurance/atlas checks, registered binding checks, the import/arithmetic/million-dollar firewalls, a frozen Riesz countermodel and the R002/CCM comparison.

The distinct unit-test count is:

| Suite | Tests |
|---|---:|
| Graph | 20 |
| FFBBP | 37 |
| OoL | 21 |
| Runner | 3 |
| Control v2 | 221 |
| Integration | 4 |
| **Total** | **306** |

The expanded batch attempted 44 commands: **12 PASS, 30 ENVIRONMENT_BLOCKED, 1 FAIL_OR_MISSING_INPUT and 1 TIMEOUT**. The missing-flint commands are not mathematical failures and are not passes. Their traces are retained individually.

The concrete portability defect is `R002_multi_probe/check_ccm_weil_bridge.py`: it assumes a `/home/user/zeta-23-lean/.../R004_prolate_v2` path rather than deriving the repository location. The needed module exists under the supplied checkout. It was left unmodified and is recorded as a failed portability check, not a pass.

The timeout is `R003_ccm_bridge/check_diagonal_shift.py`, stopped after the configured 80-second limit while running legacy nested quadrature. No numerical or mathematical verdict is inferred from that timeout.

The main graph pipeline and the independent structural audit are separate checks. Additional exact falsifiers were executed using SymPy/rational arithmetic. A 40-state floating-point ground-weight scout also ran, but its matrix quadrature errors were not enclosed; it therefore remains discovery only.

Full commands, return codes, timings, dispositions and output tails are in `test_results.json` and `extra_test_results.json`; complete local stdout/stderr logs are in `logs/`. Failed dependency installation is also preserved. The final source-integrity receipt reports 1,207/1,207 source files unchanged.

## 5. Graph results and defects worth fixing

### 5.1 Structural integrity

| Quantity | Audited value |
|---|---:|
| Physical source files | 1,207 |
| Lean source files | 638 |
| Python source files | 249 |
| Markdown files | 188 |
| Graph nodes | 19,125 |
| Graph relations | 296,976 |
| IMPORTS edges | 2,256 |
| USES_CONSTANT edges | 280,507 |
| Compiled declaration nodes in the registered closure | 7,694 |
| Source-discovered declarations | 8,335 |
| Registered claims | 81 |
| Registered PROVED_UNCONDITIONAL claims | 78 |
| Registered OPEN claims | 3 |
| Missing endpoints / duplicate IDs | 0 / 0 |
| Import cycles | 0 |

The 13 raw constant-reference SCCs pair structures/inductives with their constructors: examples include `ReversalParity` with `even/odd`, and `GlobalBottomResidualState` with `.mk`. None is a cycle of theorem proofs establishing one another. The full SCC list is recorded in the independent audit.

The three open registered claims are `C_RH`, `R001_PRIME_UPPER`, and `R002_WINDOWED_VISIBILITY`. None receives a PROVES edge. This is an important successful claim-boundary check.

### 5.2 Source-candidate identities

The candidate population is 2,362:

| Visibility | Count |
|---|---:|
| Already in registered dependency closure | 1,380 |
| Already registered root in this candidate scope | 75 |
| Private/internal source object | 217 |
| Source-only public theorem | 680 |
| Unresolved source identity | 10 |

Resolution status is 2,135 uniquely resolved, 217 private/internal and 10 without a compiler match. “Source-only” means absent from the registered closure under the current projection; it does not mean unproved, independent, novel, or automatically RH-relevant.

The ten unresolved declarations consist of one `DictionaryArchDiagonal` helper, six `GlobalParityBottomArithmeticEquivalenceAudit` declarations, one conditional-RH wrapper and two `GlobalParityBottomObstruction` declarations. One of them—`globalBottomResidualExclusion_iff_riemannHypothesis`—is separately registered and audited in the all-registered-theorem binding authority. Its unresolved candidate receipt is therefore an **export-scope inconsistency**, not evidence that its proof is absent.

The candidate exactifier imports `Zeta23.CCM` and `Zeta23.ExceptionalZero`. Standalone audit modules outside those aggregate imports need a separately declared export environment. The fix must not import RH-terminal audit modules into unconditional CCM code. Record module scope in the receipt, resolve the missing declarations in isolated audit exports, and retain the anti-circularity firewall.

### 5.3 Semantic incompleteness is explicitly acknowledged by the graph

`UNRESOLVED_GRAPH_ITEMS.json` defers:

- compiler-wide declaration census beyond the source-navigation/registered closure;
- multi-axis authority/current-state resolution;
- Git/PR/workflow provenance semantics;
- dead-route/obstruction/revival semantics beyond file nodes;
- operational concept preflight.

Thus a zero unindexed-file count is not the same as “every historical proof route is semantically represented.” A shortest path through USES_CONSTANT or MENTIONS is not a proof chain whose hypotheses have been discharged.

The FFBBP reduction correctly distinguishes module-only cohorting from module-plus-visibility cohorting. The former loses information when one module contains mixed visibility classes. The supported reduction is navigation-scoped, not a proof of exact mathematical equivalence or empirical qualification.

The OoL atlas has 680 candidates, with 495 theorem-value-erased frontier contacts and 185 without active-interface contact. Its selected cross-region probe exposes 28 eligible declarations and 21 edges. These are search contacts, not 495 partial RH proofs. In particular, a theorem's proof body mentioning another theorem is not an extra independent hypothesis in its statement. The value-erased separation is useful precisely because it prevents that confusion.

### 5.4 Documentation drift

The front-page “merged theorem authority = #247” block lags the later theorem-bearing work; the carrier bridge still appearing as an active lead is stale after #268. The graph README's older Phase-2 closure counts also lag the generated products. Historical labels should remain as dated provenance, but current summaries must stop presenting them as current global state.

These are auditability defects. They do not invalidate the unchanged, compiler-checked Lean declarations.

## 6. Workflow harvest: what the green checks actually preserve

All 15 live conclusions were success. Classification matters: a research check can pass because it faithfully reproduces a **negative** result. For the research jobs, this audit compared the logged dispositions with their frozen interpretation. It did not independently download and byte-compare every artifact from every prior historical run.

The following table is generated from the extracted live observations. Complete run/job identifiers and claim limits are in `results/workflow_harvest.json`.

| Job | Classification | Exact disposition / limit |
|---|---|---|
| `lean` | FORMAL VALIDITY GATE | CCM/ExceptionalZero and declared audit builds, placeholder rejection and axiom gates succeeded. Existing theorem authority preserved; no RH theorem proved. |
| `python-rhrc` | REGRESSION GATE | RHRC registries, integration, graph, control and Python test suite succeeded. Software/control consistency, not arithmetic positivity. |
| `r003-normalization-audit` | REGRESSION GATE | Frozen normalization, source/energy identities, threshold and research-scope checks succeeded. A normalization/research replay does not promote bounded signals to universal statements. |
| `rhkg-compiler-receipt` | FORMAL VALIDITY GATE | Compiler dependency receipt/export comparison succeeded. Certifies its declared import/root scope, not all source declarations in all audit modules. |
| `materialize` | FORMAL VALIDITY GATE + RESEARCH-PRODUCING CHECK | Regenerated compiler/graph/candidate/FFBBP/OoL products; steady-state gate passed; committed 8bb0f5f7b6c778d58bf9a30810fa9f1db29d7e5e. New candidate visibility is metadata, not new mathematical proof. Final commit has no separate attached check runs. |
| `lean-permansson` | FORMAL VALIDITY GATE | Separate Permansson formalization job succeeded. Separate domain/theorem scope; not RH and not every claim in the Permansson paper. |
| `post190-canonical-realizability` | REGRESSION GATE | REALIZABILITY_TARGET_IDENTIFIED; BASE_UNKNOWN; BLOCKED_TIGHTENED; QUOTIENT_SPACE_SCAN_DEFERRED_BASE_UNKNOWN. Frozen pressure result; quotient scan was not executed. |
| `post192-parity-trajectory-rigidity` | REGRESSION GATE | LOCAL_TAYLOR_FAILURE_ACCEPTED; REFUTED_TIGHTENED_PACKAGE; MULTIMODE_LOCAL_TAYLOR_DISMISSAL_ALL_MODES. Preserves failure of the tested local Taylor closure, not a positivity theorem. |
| `post194-parity-trajectory-sharp-enclosure` | REGRESSION GATE | PARTIAL_TRAJECTORY_ORIENTATION; 49 leaves with 48 certified and 1 unresolved span. Partial frozen coverage only. |
| `post196-q14-residual-cell-replay` | REGRESSION GATE | GLOBAL_MONOTONE_ORIENTATION / J_POSITIVE; remaining frozen span resolved. GLOBAL is the frozen Q14 hull, not all apertures or Loewner monotonicity. |
| `post198-q14-source-mechanism` | REGRESSION GATE | SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED; NO_UNIQUE_COLLAPSED_UNIFORM_LOCK; chosen lock null. No uniform source mechanism selected. |
| `post200-q14-discrepancy-mechanism` | REGRESSION GATE | DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED; NO_UNIQUE_PRIMARY_LOCK; paired enclosure 0/49 positive leaves. Identity compatibility did not yield required sign. |
| `post202-q14-composite-parity-gap` | REGRESSION GATE | COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED; PATTERN_FALSIFIED_BEFORE_FULL_COVER. Full cover was not executed after the central falsifier. |
| `post214-kernel-dual-geometry` | REGRESSION GATE | FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED; FULL_SPACE_SIGN_INDEFINITE_CERTIFIED; Q13/Q15 controls preserved. FULL_SPACE is the tested dual/kernel geometry, not the unrestricted canonical carrier of PR268. |
| `post222-biregular-zero-shift-scalar` | REGRESSION GATE | NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED; qualified cell-minimal states 0. Pointwise bi-regular scalar identities do not certify the retained whole-cell state and do not exclude it. |

## 7. Historical reconciliation

The oldest CCM material organized the problem around a finite restricted-Weil matrix, an even-simple full-space ground vector, a perturbed scaling operator, and a surrogate determinant/transform. Those are legitimate finite objects, but source hypotheses and finite-to-infinite obligations were explicit. The current route has changed: a hypothetical off-line zero itself supplies a finite negative canonical witness. It is no longer correct to describe the immediate CCM obstruction construction as waiting for a speculative determinant-convergence theorem.

The current history is better understood by separating consumed constructions from genuinely distinct unresolved mechanisms:

| Historical route or stage | Reconciled state after #268 |
|---|---|
| R001 scalar subexponential prime target | Exact RH-equivalent criterion; not an independent weaker shortcut. |
| R002 exceptional pair block | Genuine negative-direction theorem remains; survival against the complete positive on-line bulk is still open. |
| Generic R002 = CCM identification | Not available. Existing bridge is specialization-only, with a nonzero representation discrepancy in general. |
| Raw kernel / legacy finite matrix | Normalization/scalar-correction repair must be retained; names are not interchangeable. |
| Zero-shift, cubic correction, Riesz and source coupling | Substantially consumed by the present retained-state stack; not untouched fallback programmes. |
| Off-line zero -> finite witness | Already formalized. |
| Aperture freedom | A negative witness occurs at every sufficiently large aperture under an off-line zero. |
| Literal Mathlib RH terminal seam | Already formalized in the audited terminal layer. |
| #245/#246 closure gates and arithmetic criteria | RH-equivalent; their labels do not supply missing positivity. |
| #247 global-ground package | Aligns source, transfer, parity and arithmetic data on the same actual ground witness. |
| #249/#250 ratio scout | Finite sharp cancellation/control evidence, with no proved asymptotic rate or global first-detection threshold. |
| #262 endpoint jets | Exact same-ground local endpoint shape, not global weight sign. |
| #267 N-flow | Exact antitonicity in Fourier size; this is not aperture monotonicity. |
| #268 carrier hierarchy | Exact full-bottom <= boundary-flat-bottom = min parity bottoms. |
| R004 prolate/full-space comparison | Structural comparison remains worth testing, but approximate commutation alone does not control ground spaces without a usable gap/angle estimate. |

Earlier history reported extremely small relevant spectral gaps compared with commutator residuals in the prolate comparison. The appropriate revival condition is an actual quantitative invariant-subspace/angle estimate or another exact bridge—not “the commutator is small.” The derived constrained simplicity result below does not prove the original full-space even-simple hypothesis.

The CSM research-state packet supplied additional pipeline/globalizer ideas but not a compiled closing theorem. Its broader lossless-globalization/packet-bound obligations cannot be declared solved merely because the canonical CCM aperture argument now exists. Specialization and object identity must be established explicitly.

## 8. What became formally true, and what is newly derived

**PROVED in the existing source:** for L>0 where required, legal successor sizes have attained parity bottoms, exact source/intertwining identities, exact weighted-von-Mangoldt remainder energy, N-antitonicity, the full/boundary-flat/parity bottom hierarchy, and the stated terminal equivalences. The graph's current registered roots do not include a proof of `RiemannHypothesis`.

**DERIVED in this audit:** strict parity separation forces a simple boundary-flat ground state; conversely a parity tie gives at least two ground directions. The proof uses `(B-aI)Dv=S(v)g`, invertibility of the opposite shifted operator, and invertibility—not unitarity—of D. Details and assumptions are in `PROOF_NOTES.md`, Section 1.

**DERIVED with executed exact checks:** the real-even vector `(-1,3,1,-15,24,-15,1,3,-1)` at K=4 has moments M0=M1=M2=M3=0 and M4=-24, but

\[
 g'(1/8)=25432/21-(15962/35)\sqrt2-126\sqrt2\pi-2\pi<0.
\]

Its prime-test weight has zero endpoint derivatives through order seven and a strictly positive eighth derivative. Exact rational bounds on sqrt(2) and pi certify the negative sign. This is a counterexample to a proposed general implication about carrier vectors, not to a theorem restricting actual ground eigenvectors, and not to RH.

**EXPERIMENTAL SIGNAL:** a 40-state ground-weight scout at K=2,3,4,6 and L=0.5,1,2,3,4, both parities, sampled 999 source-coordinate values per state. It did not certify a ground-weight counterexample. Near floating-point spectral resolution limits the ground vector is not reliable; these states are not negative or positive theorem evidence. Matrix quadrature and eigenspace errors remain unenclosed.

## 9. A correction to the preceding proposed next step

The previous chat recommended defining the prime/source weight unconditionally rather than only through `GlobalBottomResidualState`. That recommendation was too broad.

`CanonicalPrimeRemainder.lean` already defines `canonicalPrimeRemainderEnergy L N u` for arbitrary coefficient vectors via the exact source-atom derivative integral. The residual-state prime weight is a named specialization; its integral identity is `rfl`. A generic wrapper could improve interface ergonomics, but it is not the missing mathematics.

The useful target is a **ground-specific restriction or arithmetic bound**, not another name for an existing derivative. The strict-parity simplicity result helps select and compare that ground line. The explicit counterexample prevents weakening “ground vector” to “arbitrary even boundary-flat vector” without justification.

## 10. The exact proof path now worth attempting

Let `lambda_N(L)=globalParitySuccessorBottom L N` for N>=1. Existing N-flow says it is nonincreasing in N.

Consider an unbounded sequence of positive apertures L_j. At each aperture, seek a certified unbounded size sequence N_{j,m} and explicit errors epsilon_{j,m}>=0 tending to zero, with

\[
\lambda_{N_{j,m}}(L_j)\ge-\epsilon_{j,m}.
\]

If any fixed finite bottom at L_j were negative, monotonicity would preserve that negative upper bound at every larger size, contradicting the vanishing lower error. All finite bottoms at L_j would therefore be nonnegative. An off-line zero, however, gives a negative finite witness at every sufficiently large L, including a sufficiently large member of this sequence. Contradiction.

This conditional implication is proved in full in the proof notes. Its arithmetic target is the uniform quadratic estimate

\[
B_{\rm free}(L_j,N_{j,m}+1,u)+E_R(L_j,N_{j,m}+1,u)
\le\epsilon_{j,m}\|u\|^2
\]

on the exact complete boundary-flat carrier. The current energy identity then yields the spectral lower bound.

**That estimate is OPEN.** It is RH-strength under the existing equivalence, not a newly solved or weaker premise. This route is useful because it sharply identifies what an analytic estimate must control and avoids unnecessary claims: no monotonicity in L, no all-aperture argument, and no positive lower gap uniform in N are required.

A viable attempt could exploit source/ground resolvent structure and a certified low/high block estimate. But positivity of a high block, control of its inverse, coupling norms and remaining tails would themselves need proof. None follows automatically from the graph, the rank-one identity, or an observed finite grid.

The first-contact programme remains a parallel alternative. The derived simplicity theorem makes strict branches easier to analyze; ties remain an explicit subspace problem. A mere derivative inequality at contact is inadequate, because `-t^3` crosses down with derivative zero. A valid barrier must control the first nonzero contact order or a genuinely stronger local invariant.

## 11. Falsification and why tempting shortcuts fail

A scalar shift preserves commutator/rank-one intertwining identities, reversal symmetry and compatible nesting, while changing every Rayleigh bottom. Therefore those identities alone cannot choose zero as a positivity boundary. The canonical arithmetic normalization must enter essentially.

The full-space hierarchy has a fixed direction. A seven-dimensional diagonal matrix with negative first entries and a positive codimension-three coordinate compression gives an exact elementary counterexample to reversing it. Full-space negativity is not boundary-flat negativity.

An ordinary Hilbert-space Gram matrix is positive semidefinite by construction. To use it against a hypothetical RH obstruction one needs an independently established identification of the same state's entries with expressions forcing a contradiction. Writing more compatible coordinate views does not itself add a sign inequality.

The generic polynomial weight `(1-t)^8(20t-19)` has all required zero endpoint jets, positive eighth derivative, but integral -17/9. The stronger source-matrix example in Section 8 shows that a comparable failure occurs inside the actual even boundary-flat carrier, not only in arbitrary smooth functions.

The frozen research workflows already reject the composite-parity-gap monotonicity pattern and retain unresolved source/discrepancy correlation losses. Those results should remain active constraints on new proofs. Renaming a source decomposition does not remove the loss of correlation in a signed interval enclosure.

## 12. External research check

Two primary sources were compared with the current route rather than used to overwrite the supplied project evidence.

Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755, supplies a full-space construction with an even-simple hypothesis and boundary normalization. The new constrained-ground simplicity result does not automatically discharge those differently scoped premises.

Groskin, *A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form*, arXiv:2607.02828v1, gives finite dictionary and tail-certification results. Its post-band archimedean correction has a controlled positive order and a budget asymptotic of the form `(2N+1) rho log(T)/(pi^2 T)`. This is relevant to rigorous finite matrix evaluation. It is not a bound uniform in the Fourier-size limit and does not establish full Weil positivity. In particular **T -> infinity at fixed N is not N -> infinity**. The paper explicitly excludes an RH proof.

This audit did not independently rerun those authors' released numerical packages. Public claimed-proof leads without an inspected and verified closing argument were not admitted as mathematical authority. The public Clay problem page remains an external status reference; the project's decisive criterion is still its exact proof and claim-validation gates.

Primary references:

- `https://arxiv.org/html/2511.22755v1`
- `https://arxiv.org/html/2607.02828v1`
- `https://www.claymath.org/millennium/riemann-hypothesis/`

The specific usefulness of external tail order is certification hygiene: it prevents false finite negatives from being confused with the canonical cutoff-free form. It does not supply the missing arithmetic estimate in Section 10.

## 13. Upstream implications, downstream implications and revived routes

**Upstream.** Extract a generic rank-one intertwining eigenspace lemma instead of duplicating parity-specific simplicity arguments. Keep the metric distinction explicit. Reuse the already generic prime-remainder energy rather than rebuilding it. Separate declaration identity export from mathematical authority and repair the ten missing candidate identities without crossing the terminal import firewall.

**Downstream.** The ground atlas can treat strict-even and strict-odd branches using one-dimensional ground lines, with explicit tie-subspace handling. Source-moment and weight diagnostics can use normalized charts only where the relevant source functional is nonzero. A later differentiability theorem should state matrix regularity and spectral gap assumptions explicitly. The N-flow theorem can support the cofinal lower-certificate closure lemma immediately as a conditional mathematical result.

**Revived routes.** R004 is worth a precise full/flat comparison with actual gap and angle bounds, not a revival of the failed near-commutation inference. R002 remains independent where the masking/window theorem is genuinely distinct; the generic R002/CCM identification is still unavailable. The globalizer vocabulary is useful only after matching its state, norm and output to the existing canonical witness. Old cross-parity/Riesz/zero-shift programmes already consumed by the current stack should not be billed as new alternatives.

**New RH-relevant clues.** A unique strict-branch ground line may obey a restriction that generic even-flat vectors do not. That is a specific, falsifiable hypothesis. Source-weight positivity on all carrier vectors is already false. A cofinal exact lower-certificate sequence would suffice for closure, but no such sequence has been established. The new results direct where to search; they do not constitute the required arithmetic control.

## 14. Highest-leverage next moves

The next theorem-bearing unit should formalize strict-parity ground simplicity and its tie characterization, with the exact source-weight counterexample beside it. This pair improves the atlas and prevents an invalid generalization. It has a concrete mathematical proof and a concrete falsifier, unlike a speculative universal positivity claim.

In parallel, repair the candidate export scope and update the current authority summaries. Extend the graph's deferred history/workflow/dead-route semantics before treating it as a complete historical reasoning engine. These repairs are audit infrastructure, not progress in the final RH inequality by themselves.

The next research-producing experiment should test **actual ground** weights/resolvent shapes with cutoff-free interval assembly, both parities, whole ground subspaces at ties, and planted on-line/off-line controls. Every negative or positive event must include operator-norm and eigenspace uncertainty. The exact K=4 carrier counterexample belongs in its negative-control suite.

Finally, attempt the uniform lower-certificate bound in Section 10. A successful proof must identify where arithmetic enters, bound every error on the cofinal size family, and survive scalar-shift and normalization controls. Failure to establish a required high-block, sampling or remainder estimate should become a named mathematical obstruction rather than an implicit assumption.

## 15. Final verified state

The current source tree passed the executed graph/software checks and carries genuine existing Lean theorem authority. The audit adds ordinary proofs and exact falsification evidence but no newly compiled theorem. Some local tests remain blocked, one portability check failed, and one timed out. Historical semantic coverage is incomplete despite complete physical-file coverage.

**RH remains OPEN.** There is now a clearer and testable research route: exploit ground-specific structure on strict branches, handle ties explicitly, and seek an exact cofinal arithmetic lower certificate. The unresolved part is stated as an inequality with complete quantifiers rather than hidden behind a graph path, a green workflow or an equivalent formulation.

## Reproducibility files

`PROOF_NOTES.md` contains complete ordinary proofs and the exact negative-weight certificate. `results/source_anchor_index.json` supplies pinned source paths, declaration locations and hashes. `results/workflow_harvest.json` contains extracted live CI observations; it is not a raw remote-log archive. The complete local test logs, scripts, environment receipt, original file manifest and final integrity receipt accompany this report.
