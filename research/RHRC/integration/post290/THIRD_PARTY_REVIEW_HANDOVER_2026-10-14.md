# PR 292 — complete iteration handover for third-party review

Date: 2026-10-14. Repository: HMarcusWH/zeta-23-lean. Branch: `research/post290-step123-output`. Pull request: <https://github.com/HMarcusWH/zeta-23-lean/pull/292>.

**Disposition: this research iteration is frozen for review. The complete specified build is not finished. RH remains OPEN.** The user requested that all current work be rounded up, committed and pushed, followed by an extensive account of everything built, learned and still questioned, and then a wait for a third-party review supplied by the user. This document implements that handover. It does not authorize more experiments, a merge, or promotion of supporting lemmas into an RH theorem.

The complete machine-readable local module inventory is [LOCAL_PROOF_FRONTIER_2026-10-14.json](LOCAL_PROOF_FRONTIER_2026-10-14.json). Detailed component receipts, compiler logs and three domain handovers are preserved in [review_2026-10-14](review_2026-10-14/). The final push and workflow snapshot are recorded separately in `REVIEW_FREEZE_STATUS_2026-10-14.md`, so a document cannot purport to contain its own final commit hash.

## 1. Request, reference instructions and authority

The original request was to finish the build continuing from an old chat and PR 292. Reference material included RH_Argon_Audit_Iteration_2026-10-13.zip, NEXT_PR_AMENDMENT.md, BUILD_MANIFEST (2).json, BUILD_SPEC (2).md, and RH_Next_PR_Step123_Output_Spec_2026-10-13.zip. Their intake, provenance and adopted scope are preserved in SOURCE_INTAKE_RECEIPT.json, SOURCE_REGISTER.json, BUILD_CONTRACT.md, the `spec/` snapshot and amendment register. Instructions within attachments were treated as proposed build requirements and research context; they were not human authorization to incur unbounded resources or assert mathematical success.

The live user authorized the D2 continuation separately: **“Approve the 460-child continuation and its stated resource limit.”** The later instruction to round up and wait supersedes continued pursuit of new proof obligations. The original mandatory W00–W10 and M01–M25 scope has not been silently reduced. A review freeze is not acceptance of an incomplete producer. Synced `sources/` material remains read-only. No merge is requested or performed.

Evidence precedence is live source/compiler/CI, current execution and handover documents, detailed adopted specifications, then older history. Local source-byte checks and remote whole-commit checks are distinguished throughout.

Labels used below:

- **PROVED:** the exact stated component is accepted by the pinned Lean compiler, with the scope and assumptions in its source. Local evidence does not itself establish that the final remote commit passed CI.
- **DERIVED:** a straightforward mathematical consequence of proved components whose final composition or requested export has not been separately formalized.
- **LEAD / HYPOTHESIS:** a route to investigate after review.
- **EXPERIMENTAL SIGNAL:** numerical or discovery evidence, even when a finite checker certifies its finite scope.
- **OPEN:** the exact obligation is not established.

## 2. Exact verification state and reproducibility limits

The toolchain is `leanprover/lean4:v4.33.0-rc2`; Mathlib is pinned at `51e6992efd06126df61a496bebf8f49482a4e129`. Local checks used a single compiler job, `maxHeartbeats=800000`, `relaxedAutoImplicit=false`, and the stated Unicode pretty-printer flag. They used the separate checkout and a shared pinned baseline import cache. The receipts bind the actual checked source and log bytes; some additionally bind olean bytes. They do not claim that a clean, monolithic final-tree build ran locally.

The permitted printed axiom footprint is a subset of `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, new project axiom or proof escape is admitted by the component audit. The full workflow also checks proof escapes. Compiler success determines formal validity of the exact proposition; it does not show that the proposition is the intended specification or that its hypotheses are independently available.

The frozen component batches include:

| Evidence batch | Scope |
| --- | --- |
| Fourier receipt | Unpadded support chain and canonical phase facade; exact modules, roots and hashes in receipt |
| Padded receipt | Literal positive-padding construction, transport, normalization, quantitative errors and phase symmetry |
| Native consumer receipt | 22 modules, 87 printed roots: native selection, inverse budgets, Schur consumers, actual complex transforms |
| M18/M20 final receipt | 14 modules, 62 printed roots: causal witnesses, analytic zero jets, actual kernel annihilation and A-X to B-Y bridge |
| Root compact inverse checks | General L2 regularity, energy, concrete weak-H2 solution, uniqueness and canonical facade; all nine final refreshes exit zero |
| Compact convolution check | Four printed roots for actual P integration by parts, reflection and convolution transfer |

These batches overlap; do not add their counts to obtain independent modules or theorems. The aggregate JSON lists distinct source modules. A printed-root count also need not equal all public theorem declarations. Definitions and structures are recorded as definitions/inductives, not promoted into theorem authority.

Published checkpoints during this resumption were:

| Commit | Meaning |
| --- | --- |
| `72bc63fe8b4abe27423b09ea30f1a4fa5a1b4501` | Previously pushed source frontier and historical whole-workflow harvest target |
| `6f5a541b70d39dd6e1a8e7d32c85e9e5c2a44ba1` | Explicitly approved bounded D2 continuation protocol |
| `a55fbeeed6500bffe2ccac3960258ca5c590c7ee` | Narrow production-workflow bootstrap; actual D2 run source |
| `fd250bd897d4d723a45e107c49c0b35831396b53` | Large completed proof/support batch and preserved workflow harvests |
| `c1751f06` and `d5b867ef467b4eb5d5e38e500577fda2b2a5f91b` | Exact declaration-kind corrections for audit roots, including multiline entries |

The final batch additionally repairs the Python receipt consumer to parse explicit theorem/definition/inductive triples. The earlier fd250bd8 component job successfully built its implemented sources and printed its allowed axiom roots, then failed during receipt export because two constructors had been queried as THEOREM. That run is not reported as a successful completed receipt. The fix keeps exact kind equality and separates `PROVED` theorem entries from `DEFINED_DATA_NOT_A_THEOREM` entries. Mutation tests cover malformed, duplicate and incorrect-kind scopes.

## 3. Original source, visibility and phase depth

The source remains the original infinite uniform-convolution sinc product at the fixed rational scale `s0=1/4096`. With `P=∂²−1/4`, the project uses `k=Pq` and `j=P²q`. The finite detector is an approximation of this actual source, not a replacement source chosen to fit a desired conclusion.

PROVED support includes original source smoothness and Fourier estimates, literal transform identities, off-line visibility, signed tail excursions and normalized per-phase cofinal aperture depth. The quantifiers matter: for each actual off-line nontrivial zero rho, each `0<beta<abs(Re rho−1/2)`, each requested phase, and each requested lateness R, a sufficiently late aperture is produced. There is no uniform detection time, common deep aperture for both phases, or all-large-L depth assertion.

The actual source Laplace factor J contains **one Q factor**: the pole-killing polynomial times the original Q. The detector autocorrelation can contain Q squared; it cannot replace J. Positivity of q does not imply positivity of j. The unchanged j has ordinary mass 1/16, exponential pole cancellation, and changes sign. Absolute mass must not be confused with signed mass.

Several requested export spellings in M02/M03 are not yet packaged even though substantial source/visibility mathematics exists. The final acceptance audit identifies exact-name gaps separately from mathematical gaps.

## 4. Actual finite source construction and positive padding

The finite construction fixes `Kd=ceil(L^4)` and raw cutoff `N=Kd−4`; the endpoint multiplier is exactly sin^8. No larger cutoff is introduced to evade the prescribed estimates. All Fourier coefficients, sqrt(L) normalization and the nine coefficients of the endpoint multiplier are explicit.

The original unpadded chain proved finite reconstruction, endpoint flatness, moment cancellation, norm transport, Weil continuity and native depth. Review revealed that this did not by itself fulfill the mandatory nonnegative-primitive construction. The final padded chain adds the rigorous raw r=0 tail budget as a literal positive DC coefficient before applying the endpoint multiplier. Fourier conjugacy proves the truncation real, and the tail domination proves the primitive nonnegative on the physical interval.

PROVED properties of the actual padded image include eight zero endpoint jets for q, the actual P image, the required hard-extension C4 regularity, exact elementary pole neutrality, six vanished trial moments, true Euclidean/physical L2 norm identification, and actual native quadratic-form transport. Both phase vectors are nonzero and truly normalized after one source-derived threshold. Every requested phase separately has cofinally deep actual unit trials with energy at most `−exp(beta L)`.

The full four-term Gram and native-energy expressions are retained before minimization. Actual padded matrices are circulant. Canonical M05 and M06 facade exports now exist and compile locally. The generalized Rayleigh identity uses the complete Gram denominator and energy numerator. The separately simplified scalar phase quotient `(d+sigma*c)/(nu+sigma*omega)`, real-entry presentation and an explicit positive scalar denominator export remain packaging/composition work.

The positive DC padding cancels exactly in the **odd primitive**. Equality of the resulting odd normalized native detectors is DERIVED from that cancellation, linearity/reflection of P and finite coordinate uniqueness; its final separate export has not been supplied. This is a useful simplification clue, not permission to discard padding from the even construction.

Quantitative estimates retain part of the stretched-exponential decay to pay polynomial, normalization and aperture losses. The concrete normalized physical H1 rate has source-only constants and threshold and the requested `L^(17/2)` scale. The normalized native-form error has an actual proved budget with a stronger weighted stretched-exponential asymptotic. The final theorem displaying exactly `(1+L)L^(17/2) exp(L/2−c sqrt(N/L))` was not appended before the freeze. That display is DERIVED/unfinished packaging, not an already exported theorem.

## 5. Corrected pole-neutral geometry, moments and singular branches

The corrected source and index identities, cubic witness and actual fourth-moment/index rigidity are supported by compiled components. Even and odd shifted secular reconstruction use their correct adjoint conventions, including the corrected odd minus sign. Singular-safe simple-even and tied branches are treated separately.

PROVED: a selected simple even ground has nonzero fourth moment, including at a parity tie. Corrected-source nonvanishing is only asserted under the strict-below-odd-bottom hypothesis. No S0 nonzero theorem is asserted at a tie. Both parity eigenspaces may be simple while their eigenvalues tie; simplicity within a parity does not eliminate a tie across parities.

The actual R3 intertwining yields a residual bound and, with a positive odd gap, a quantitative lower bound for a trial with M4=0. At zero gap this lower bound is vacuous. The source trial has M4=0; the selected even ground has M4 nonzero. They must remain distinct objects. A deep trial need not be an eigenvector, and replacing it by a selected ground does not preserve its phase, positivity, source representation or higher moments.

M10/M11 have substantial proved mathematics under current names but not all proposed facade spellings. Their status must not be inferred solely from earlier “complete local” notes. The acceptance audit is the current precise account.

## 6. Native threshold selection and two Schur records

The bottom-only finite avoidance lemma constructs `eta` with `D/3<eta<D/2`, `D=exp(beta L)`, and gap `g=D/[12(Kd−1)]`. It uses only the actual native bottoms at cutoffs 3 through Kd. Repeated forbidden values and the empty case are handled. The least crossing constructs an actual cutoff `3≤K≤Kd`, an actual spectral value and a unit actual parity ground. At K=3 the predecessor K=2 is genuinely empty; no invented bottom of an empty spectrum is used.

The predecessor is coercive by 2g at the actual ground shift and by g at the detector shift −eta. Four actual inverses are constructed, with bounds `6(Kd−1)/D` and `12(Kd−1)/D` respectively. Their norms are zero at the first empty predecessor. These are conclusions, not caller-supplied inverse assumptions.

The selected-ground Schur record concerns one new native shell at K and actual shift lam. The original detector Schur record concerns the entire complement of the embedded K−1 predecessor inside Kd and shift −eta. Its dimension is `Kd−K+1`. The detector completed-square identity retains a nonzero complementary coordinate and signed Schur energy at most `−(D−eta)<−D/2`. These two records cannot be collapsed into one.

The canonical M12 facade now exports all four required names. Its gap core was moved unchanged into CanonicalDeepThresholdGap to avoid an import cycle; source-origin audit entries were updated accordingly.

The actual rho-free Admissible selector requires both literal padded phases to be nonzero and unit, the exact cutoff/gap/threshold data and actual earlier-bottom conditions. It does not contain rho or assume the desired C-Schur upper bound. Every requested actual padded phase produces a retained state cofinally with detector literally equal to that phase's source unit. Normalization for both phases is paid at the chosen aperture without claiming simultaneous depth.

## 7. General compact L2 inverse and convolution transfer

The compact inverse was extended from smooth input to a general compactly supported pole-neutral `MemLp 2` source. Explicit finite primitives produce continuous u and first-jet representatives, actual a.e. equations, compact support, clamped traces, absolute continuity and all three L2 jets. Complex FTC and a complex energy identity yield the actual norm bound `||u||≤4||f||`.

NativeCompactPoleH2 is a concrete one-dimensional weak-H2 interface. Its constructor does not take inverse existence, uniqueness, energy or a norm bound as fields to assume. Global integral identities against compact C1 tests establish both weak derivatives. Two exponential integrating factors prove uniqueness with only the stated general-source regularity. The canonical M16 facade now supplies existence/uniqueness, support and norm-bound exports.

This is a genuine constructed weak-H2 solution. It is not a claim that a separately named Mathlib distributional Sobolev predicate has been populated. A reviewer should decide whether the specification accepts this equivalent concrete interface or wants a further bridge to a particular library predicate.

CompactPoleConvolution proves self-adjoint P integration by parts when the first factor is compact and the second is C2, commutation with literal reflection, convolution transfer and actual `(Pq)*(Pq)=q*(P²q)`. No unnecessary global support or integrability premise is imposed on the second factor. These are M17 prerequisites. The full native prime-field forcing/projected forcing/exterior-history package remains OPEN.

## 8. Actual stable input, bounded operator and arithmetic transforms

The actual correction c is signed. Its signed mass −2/3 must not be confused with the positive completed kernel's absolute contraction estimate. The actual damped completion operator on causal L2 has norm at most `605/621<1`. Fixed-time integrability, local product Fubini and representative arguments identify the Bochner operator with the literal x−s convolution almost everywhere for arbitrary L2 input.

The original integer drive U has the required stable integrability. Actual Y=c*U is causal L2. The pointwise identity a*X=Y is established before assuming global X L2. A-X→B-Y is now a proved implication: **if the literal damped original X is MemLp2**, its actual causal class maps to actual Y, hence Y belongs to the actual operator range and range closure. This implication does not prove A-X.

The actual complex transform identities now have paid integrability and sum/integral exchanges. Write `R(w)=(w−1/2)/[(w+1/2)(w+3/2)]` and J for the actual source transform:

- `Laplace(c)(w)=R(w)` on Re w>−1/2.
- `Laplace(a)(w)=R(w) zeta(w+1/2)` on Re w>0 except w=1/2, first proved in the absolutely convergent half-plane and then analytically continued.
- `Laplace(U)(w)=−zeta'(w+1/2) J(w)` on Re w>0 except w=1/2.
- `Laplace(Y)(w)=R(w)[−zeta'(w+1/2)]J(w)` on that punctured half-plane.
- The actual J is entire, with its unchanged one-Q physical formula.

The exceptional values are proved separately: `Laplace(a)(1/2)=1/2`, using the true zeta residue, while `Laplace(Y)(1/2)=0`, using the actual c*U product. Totalized zeta or derivative values at their pole cannot be substituted into a punctured formula. The zero of c at 1/2 does not make a into an annihilator there.

## 9. Causal zero jets, actual annihilation and the remaining obstruction

The concrete causal exponential-polynomial `t^k exp(−conj(w)t)` is L2 and nonzero for Re w>0. Its Hilbert pairing is the literal polynomial Laplace moment, with damping shifts and conjugation fixed. Actual adjoint pairings expand into binomial kernel moments. Analytic differentiation establishes the exact derivative/moment relation with factor `(-1)^k`.

The actual a/zeta transform now proves actual kernel zero jets. For an off-line zero, the right-side representative is chosen as rho or 1−rho with multiplicity preserved, and positive damping is constructed. All degrees below the actual multiplicity annihilate the real operator range; the concrete witness lies in the actual adjoint kernel. This is stronger than an abstract conditional moment lemma.

For an actual zero of order m, zeta' has order m−1. The rational factor and actual J are nonzero at the off-line point. The analytic factor modules prove the expected first nonzero expression jet, with the exact sign and degree m−1; no simple-zero assumption is used.

**Still OPEN as a final physical composition:** identify the appropriate derivative of the actual Y transform with that nonzero expression jet, export the actual nonzero input pairing, and compose it with the actual annihilator to obtain the proposed `nativeCompletedInput_zeroJet_ne_zero` and `nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero`. The final U/Y transforms and actual kernel annihilation now exist separately, but the final theorem is not silently inferred as a completed canonical M20 export. This is the highest-value narrowly scoped post-review composition candidate.

## 10. Residual iteration and the Step4 boundary

The actual adjoint residual iteration proves finite norm-loss identities, a quantitative decrement using `2−(605/621)^2`, monotonicity and invariance of the projection to ker A*. Kappa is kept as its own ratio and may vanish. Contraction of A does not imply an inverse, dense range, vanishing limiting residual, zero adjoint-kernel projection or membership of the original X in L2.

The three intended closing cuts remain OPEN: A-X (the actual damped X domain assertion), B-Y (the required actual range/range-closure assertion in the appropriate quantified setting), and C-Schur (the separately required signed Schur bound). The proved A-X→B-Y implication compresses dependency, but it is not a proof of either antecedent or unconditional conclusion.

M21 original native exterior record/history and associated residual package, M22 native output/route views, M23 filled GeneratedStep123Output producer, M24 conditional RH sufficiency wrappers and complete M25 acceptance remain unfinished. No theorem here is claimed as RH or an RH-equivalent closing theorem.

## 11. Workflow harvest and numerical state

Historical workflow harvests for 6ae99364, 75a3bd63, 8ede0589, b716fad7, d88d1009 and 72bc63fe are preserved beside this document. A workflow success is classified by what it does:

- FORMAL VALIDITY GATE: compiler, exact type/axiom resolution, no-placeholder checks.
- REGRESSION GATE: replay of frozen historical theorems, certificates or countermodels.
- RESEARCH-PRODUCING CHECK: new search, discrepancy observations, independent finite certification.

The 72bc63fe harvest covered 20 runs / 54 jobs: 49 successes, three failures, two skips, with 52 logs and 27 artifact ZIP digests. The old component proof-root failures were subsequently repaired. The strict RHKG gate also identified missing standalone-role dispositions and stale generated products. Source roles are descriptive inventory, not new theorem authority. The generated graph/compiler/integration/FFBBP/OOL stack must be fully materialized and strictly rechecked; weakening its gate is not an acceptable repair.

The fd250bd8 push component build compiled the implemented batch and passed its proof-escape check over 564 files. Its receipt-export kind error is documented above. Other jobs had mixed completed, cancelled, queued and running states; they are not summarized as “all green.” The review-freeze snapshot records the exact later dispositions. Cancelled or running jobs establish no pass.

Research results preserved by green replay include native observation rows unchanged at the compared frontier, the historical Q14 composite parity-gap falsification, unresolved source/discrepancy mechanisms, scoped K2 interval certificates and 18 frozen K3 boxes. Full-space dual-independence/sign-indefiniteness certificates retain their exact historical scopes. Replaying them does not make a new global theorem or erase a counterexample.

### Approved D2 continuation

Original run 38461259594 was cancelled after the selected SECOND search waves and candidate assembly completed, while independent checking/release did not finish. It retained 66395 accepted leaves and exactly 460 unrun frozen children. The frozen partition has 716 children and original selection cap 256. The remaining even-layer counts are Q13:8, Q14:244, Q15:208.

The user authorized exactly those 460 children, the same SECOND algorithm, 512-bit search, depth 48, node limit 8192, 1800 seconds per child, globally at most eight workers, sequential waves of 256 and 204, and at most 230 additional search runner-hours. Fresh independent 768-bit checking of all 30 cells is required afterward. No implicit retries, timeout resets, FOURTH layer, new representation or removal of unresolved geometry is authorized.

Actual continuation: <https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38569316691>, source a55fbeeed6500bffe2ccac3960258ca5c590c7ee, tree 7ffdf5095db2d54ef97897c19797886d145b65d2. The freeze/preflight passed, including archive integrity and real artifact upload/download. Frozen plan SHA256 is `433107bbfe412625223fe1f08da36ca7d837bd82e7a536fc50a2d447886cf6ef`. Original archive SHA256 is `0077e514187a0cb326170b7b13e9e699d898a2ba10d8b4b20fa75a5cd6072b92`.

The first independently inspected completed child Q13_even_C00_P07_R00001_P0 produced 16 accepted leaves from 31 tested nodes, zero unresolved and no negative result in 192.74 seconds of supervisor wall time. This is a search result awaiting the required fresh check. The final snapshot, not this first example, gives current job counts. Search-job success alone is not an all-cell certificate. Even a completed finite certificate would not supply Lean hWindows or prove RH.

The user requested review freeze while this already authorized external run was active. It is left within its approved protocol. No new monitor automation, rerun or resource extension is created by this handover.

## 12. Post-green research pass

### What became formally true

The actual padded source now reaches literal normalized cofinally deep native trials and actual retained selection. General compact L2 pole-neutral input has an explicit unique clamped weak-H2 inverse with norm bound four. Actual causal completion is connected to literal convolution and arithmetic transforms. Actual zero jets annihilate the actual operator range. The exact hypotheses and boundaries above remain part of these statements.

### Workflow harvest

Historical and current snapshots preserve each job's disposition. Formal components, regressions and research production are separated. Final whole-head CI, complete graph freshness, final D2 independent certification and full producer acceptance cannot be inferred from local green components.

### What changed

The unpadded positivity gap was repaired with actual DC padding. Smooth-only inversion became general L2 inversion. Conditional kernel-moment reasoning became actual kernel annihilation. U/Y arithmetic identities moved from intended formulas to actual physical transforms. Several native output consumers gained canonical facades, while other interfaces and the final producer remain unfinished.

### Upstream implications

The complex AC/FTC and compact-test P identity can serve as common infrastructure. Padded and unpadded chains may be compressed through a generic perturbation abstraction after review. Gap/core extraction avoids an artificial import cycle. Actual arithmetic transforms and actual adjoint witnesses should share one damping/translation convention rather than duplicate it.

### Downstream implications

The final physical Y zero-jet composition is now a smaller, concrete obligation. M17 can use the compact-first-factor convolution identity without demanding global prime-field L2 before it is available. The A-X→B-Y theorem may remove duplicate downstream assumptions. Actual retained selection can feed a future output record without equating the source detector and ground.

### Resurrected routes

The general-source compact inverse route is no longer blocked by a smooth-source restriction. The actual causal annihilator route is no longer blocked by merely abstract transform/moment premises. The physical range-obstruction route is reduced to composing actual Y derivative jets with proved local analytic factors. The source-versus-ground shortcut remains invalid; the parity-gap tie remains a real boundary; the numerical D2 route remains independently finite and incomplete until checked.

### New RH-relevant clues

LEAD: actual kernel order m against actual input order m−1 could produce a precise causal range obstruction at every off-line zero. LEAD: odd padding cancellation may simplify exterior/history estimates. LEAD: M4-zero source trials and nonzero-M4 selected even grounds could quantify the amount of residual/Schur correction required by a positive parity gap. These are possible compositions or obstructions, not claims of RH.

### Falsification checks

Attack the final obstruction at multiple zeros, reflected left-side zeros, damping endpoints and the exceptional w=1/2. Verify every conjugation, (-1)^k sign and epsilon shift. Try parity ties before interpreting an M4 residual bound as positive. Test K=3 empty predecessors and K=Kd complementary dimension one. Track true normalization and all four phase cross terms. Check that a finite approximation has not inherited the original Q zero divisor without proof. A contraction example with nonzero adjoint-kernel projection is the fastest falsifier of an unjustified range inference.

### Highest-leverage next moves after review

1. Review mathematical meanings of the new actual transform, H2 and annihilation statements before adding more code.
2. Compose the actual Y nonzero jet and actual range annihilator with exact multiplicity/damping conventions.
3. Decide the accepted M16 Sobolev interface and finish precise M05/M06 rate/scalar exports.
4. Build the actual M17 forcing and M21 exterior/history packet, keeping the two Schur records distinct.
5. Close the complete output producer and audit its hypotheses before any RH sufficiency wrapper.
6. Complete exact-head compiler receipt, full derived-state materialization and full workflow harvest; separately finish D2 fresh verification under the approved budget.

No item is started automatically during the review wait.

## 13. Outstanding questions for the third-party reviewer

The following list deliberately includes both mathematical and engineering questions. An affirmative answer in prose must not substitute for a missing Lean theorem.

1. Does the literal positive DC coefficient exactly match the adopted construction, including the cutoff and all normalization constants?
2. Are source-only constants defined through thresholds acceptable, or must the specification expose numerical constants?
3. Is the final displayed native-form rate best exported as a short corollary of the stronger weighted budget?
4. Should the simplified real phase quotient and denominator positivity become mandatory explicit exports before packet assembly?
5. Can odd primitive cancellation eliminate duplicate later odd-phase estimates without changing the literal producer?
6. Are every hard-extension endpoint and the distinction between eight primitive jets and six P-image jets correctly stated?
7. Does every use of the finite source retain both elementary pole functionals and the actual norm identification?
8. Are any upstream source Gevrey/visibility obligations merely missing aliases, or is a stronger specified quantifier still absent?
9. Are the corrected odd adjoint sign and strict/tied secular branches mathematically the intended ones?
10. Is the singular tied package complete enough for every intended consumer without an illicit nonzero S0 premise?
11. Can the M4 residual lower bound yield a useful quantitative Schur constraint, or does it only restate trial/ground separation?
12. What remains at a parity tie where the positive-gap residual lower bound disappears?
13. Does the bottom-only avoidance lemma use the smallest necessary forbidden-value set?
14. Are the separate 6 and 12 inverse budgets used at exactly their intended shifts?
15. Is K=3 genuinely handled everywhere by zero-dimensional predecessors?
16. Do all detector Schur consumers retain the full Kd−K+1 complement rather than the selected one-shell model?
17. Does the rho-free Admissible predicate contain only the intended inputs to C-Schur, with no hidden desired conclusion?
18. Are any original trial phase, positivity or moment facts accidentally transferred to selected u downstream?
19. Does the concrete weak-H2 record meet M16, or is a library Sobolev/distribution bridge required?
20. Does representative-level uniqueness prove precisely the intended solution uniqueness for arbitrary L2 equivalence classes?
21. Can compact P transfer be applied to the actual native prime field with only locally proved C2 regularity?
22. Which exact additional convergence estimates are needed for the full projected forcing identity?
23. Is actual a*X=Y stated before X L2 everywhere that later A-X→B-Y uses it?
24. Are causal embeddings, x−s conventions and almost-everywhere representatives consistent across the operator and transform modules?
25. Do all sum/integral exchanges pay absolute integrability before rewriting the arithmetic series?
26. Does the analytic continuation use the correct connected punctured domain and never the zeta pole itself?
27. Are the separately computed exceptional values a(1/2)=1/2 and Y(1/2)=0 used without totalization artifacts?
28. Does J retain one Q factor at every source-visibility and input-jet use?
29. Are the actual zero order, reflected-zero choice and positive epsilon compatible in one final theorem?
30. Is degree m−1 correct for every multiple zero, with the exact (-1)^m leading coefficient?
31. What is the shortest exact bridge from actual Y Laplace derivatives to the already proved analytic expression jet?
32. Does the final witness pairing prove non-membership of range closure in exactly the intended Hilbert space?
33. Could an unnoticed conjugation or damping shift make the putative nonzero pairing evaluate at a different point?
34. Is B-Y intended as range, closure of range, or a quantified approximation assertion at each stage?
35. Given A-X→B-Y, can any consumer hypothesis be removed without circularity?
36. Which concrete exterior/history estimate would actually prove A-X, and does it conceal an RH-equivalent premise?
37. Is the C-Schur cut logically independent of the missing X domain/range cuts in the proposed wrappers?
38. Can the invariant ker A* projection furnish a useful obstruction while the residual norm still decreases?
39. Do existing finite countermodels falsify any newly proposed composition, rather than just the historical stronger conjecture?
40. Does the unchanged native observation table now have a different implication under the proved selection constraints?
41. Are the D2 460-child plan and no-retry accounting fully faithful to the user-approved continuation?
42. Does fresh 768-bit checking cover every accepted leaf and all 30 cells, including seam obligations and unresolved geometry?
43. Which numerical conclusions, if any, could later be imported into Lean, and through what explicit certificate interface?
44. Have all mandatory proposed API names been implemented or transparently classified as absent/equivalent support?
45. Are actual definitions/structures correctly separated from theorems in audit receipts and downstream claim consumers?
46. Do moved root origins and aliases resolve to the actual current source module without ambiguity?
47. Is the full derived-state stack reproducible from the final source census without stale generated products?
48. Which exact final CI failures are source defects, metadata defects, stale products or intentionally unresolved research dispositions?
49. Does any prose still overstate component validity as full producer or RH authority?
50. What single post-review theorem or falsification experiment would now yield the greatest mathematical information gain?

## 14. Reviewer navigation and restart conditions

Start with BUILD_CONTRACT.md, BUILD_MANIFEST.json and the exact M01–M25 acceptance audit. Then read the frozen source/log receipts, the three detailed domain handovers, and the proofs around their definitions. Use POST_GREEN_RESEARCH.md and historical WORKFLOW_HARVEST documents for earlier failures and changes in interpretation. Use the final workflow snapshot for what actually ran on the final source head.

The two unexecuted workflow designs are preserved as `.yml.txt` under `review_2026-10-14/unexecuted_workflow_candidates/`. They are not active workflows and have no execution evidence. The old diagnostic shard design must not be run alongside the approved D2 continuation in a way that exceeds its global eight-worker budget. The materialization design is an unexecuted proposal, not evidence that the strict generated-state gate passed.

No caches, compiled objects, temporary credentials or downloaded artifact archives are committed as source evidence. Portable source/log hash receipts and selected decoded logs are committed. Raw receipts may retain local absolute provenance paths; the copied portable log tree and evidence index allow review without those original machine paths.

At handover, local mathematical runners are stopped. Already authorized D2 work remains external and bounded. The next active step is the third-party review supplied by the user. Any resumed work should begin by checking the exact live head and outstanding CI/D2 state, then responding to that review. The remaining research program is recorded here so it need not be reconstructed from a lost chat.




## Appendix: distinct locally checked source modules

This inventory contains 132 distinct source modules. Counts are printed axiom roots, not independent theorems or whole-tree checks. The JSON frontier supplies exact byte and LF-normalized hashes plus Git blob identities.

| Source module | Printed roots |
| --- | ---: |
| [Zeta23.CCM.CanonicalDeepThresholdGap](../../../../Zeta23/CCM/CanonicalDeepThresholdGap.lean) | 4 |
| [Zeta23.CCM.CanonicalDeepThresholdSelection](../../../../Zeta23/CCM/CanonicalDeepThresholdSelection.lean) | 4 |
| [Zeta23.CCM.CanonicalPoleNeutralBottomNFlow](../../../../Zeta23/CCM/CanonicalPoleNeutralBottomNFlow.lean) | 7 |
| [Zeta23.CCM.CanonicalPoleNeutralCubicWitness](../../../../Zeta23/CCM/CanonicalPoleNeutralCubicWitness.lean) | 5 |
| [Zeta23.CCM.CanonicalPoleNeutralGroundConstraints](../../../../Zeta23/CCM/CanonicalPoleNeutralGroundConstraints.lean) | 3 |
| [Zeta23.CCM.CanonicalPoleNeutralIndexRigidity](../../../../Zeta23/CCM/CanonicalPoleNeutralIndexRigidity.lean) | 5 |
| [Zeta23.CCM.CanonicalPoleNeutralShiftedSecular](../../../../Zeta23/CCM/CanonicalPoleNeutralShiftedSecular.lean) | 16 |
| [Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie](../../../../Zeta23/CCM/CanonicalPoleNeutralSimpleEvenTie.lean) | 10 |
| [Zeta23.CCM.CanonicalPoleNeutralSourceMoment](../../../../Zeta23/CCM/CanonicalPoleNeutralSourceMoment.lean) | 8 |
| [Zeta23.CCM.CanonicalPoleNeutralTiePackage](../../../../Zeta23/CCM/CanonicalPoleNeutralTiePackage.lean) | 7 |
| [Zeta23.CCM.CanonicalPoleNeutralTrialResidualBounds](../../../../Zeta23/CCM/CanonicalPoleNeutralTrialResidualBounds.lean) | 4 |
| [Zeta23.CCM.CanonicalTrialResidualChannels](../../../../Zeta23/CCM/CanonicalTrialResidualChannels.lean) | 11 |
| [Zeta23.CCM.CompactComplexIntegralFTC](../../../../Zeta23/CCM/CompactComplexIntegralFTC.lean) | 2 |
| [Zeta23.CCM.CompactPoleConvolution](../../../../Zeta23/CCM/CompactPoleConvolution.lean) | 4 |
| [Zeta23.CCM.DetectorRetainedSchurState](../../../../Zeta23/CCM/DetectorRetainedSchurState.lean) | 6 |
| [Zeta23.CCM.FiniteBottomGapSelector](../../../../Zeta23/CCM/FiniteBottomGapSelector.lean) | 1 |
| [Zeta23.CCM.NativeAdjointResidual](../../../../Zeta23/CCM/NativeAdjointResidual.lean) | 4 |
| [Zeta23.CCM.NativeCausalAdjointZeroJets](../../../../Zeta23/CCM/NativeCausalAdjointZeroJets.lean) | 5 |
| [Zeta23.CCM.NativeCausalAnalyticObstruction](../../../../Zeta23/CCM/NativeCausalAnalyticObstruction.lean) | 2 |
| [Zeta23.CCM.NativeCausalExponentialWitness](../../../../Zeta23/CCM/NativeCausalExponentialWitness.lean) | 5 |
| [Zeta23.CCM.NativeCausalKernelLaplaceDerivatives](../../../../Zeta23/CCM/NativeCausalKernelLaplaceDerivatives.lean) | 6 |
| [Zeta23.CCM.NativeCausalLaplaceDerivatives](../../../../Zeta23/CCM/NativeCausalLaplaceDerivatives.lean) | 5 |
| [Zeta23.CCM.NativeCausalLaplaceMoments](../../../../Zeta23/CCM/NativeCausalLaplaceMoments.lean) | 3 |
| [Zeta23.CCM.NativeCausalRangeObstruction](../../../../Zeta23/CCM/NativeCausalRangeObstruction.lean) | 3 |
| [Zeta23.CCM.NativeCompletedInput](../../../../Zeta23/CCM/NativeCompletedInput.lean) | 5 |
| [Zeta23.CCM.NativeCompletedInputComplexLaplace](../../../../Zeta23/CCM/NativeCompletedInputComplexLaplace.lean) | 3 |
| [Zeta23.CCM.NativeCompletedInputRangeOfPrimeLp](../../../../Zeta23/CCM/NativeCompletedInputRangeOfPrimeLp.lean) | 5 |
| [Zeta23.CCM.NativeCompletedInputZetaLaplace](../../../../Zeta23/CCM/NativeCompletedInputZetaLaplace.lean) | 5 |
| [Zeta23.CCM.NativeCompletionComplexLaplace](../../../../Zeta23/CCM/NativeCompletionComplexLaplace.lean) | 3 |
| [Zeta23.CCM.NativeCompletionEquation](../../../../Zeta23/CCM/NativeCompletionEquation.lean) | 4 |
| [Zeta23.CCM.NativeCompletionIntegerKernel](../../../../Zeta23/CCM/NativeCompletionIntegerKernel.lean) | 4 |
| [Zeta23.CCM.NativeDampedCompletionOperator](../../../../Zeta23/CCM/NativeDampedCompletionOperator.lean) | 9 |
| [Zeta23.CCM.NativeDampedCompletionPointwiseBridge](../../../../Zeta23/CCM/NativeDampedCompletionPointwiseBridge.lean) | 5 |
| [Zeta23.CCM.NativeDampedCompletionResidual](../../../../Zeta23/CCM/NativeDampedCompletionResidual.lean) | 6 |
| [Zeta23.CCM.NativeDeepThresholdEvenMoment](../../../../Zeta23/CCM/NativeDeepThresholdEvenMoment.lean) | 2 |
| [Zeta23.CCM.NativeDeepThresholdGround](../../../../Zeta23/CCM/NativeDeepThresholdGround.lean) | 1 |
| [Zeta23.CCM.NativeDeepThresholdInverseBudgets](../../../../Zeta23/CCM/NativeDeepThresholdInverseBudgets.lean) | 7 |
| [Zeta23.CCM.NativeDeepThresholdSimplicity](../../../../Zeta23/CCM/NativeDeepThresholdSimplicity.lean) | 5 |
| [Zeta23.CCM.NativeDetectorSchur](../../../../Zeta23/CCM/NativeDetectorSchur.lean) | 7 |
| [Zeta23.CCM.NativeIntegerDriveComplexLaplace](../../../../Zeta23/CCM/NativeIntegerDriveComplexLaplace.lean) | 5 |
| [Zeta23.CCM.NativeIntegerKernelComplexLaplace](../../../../Zeta23/CCM/NativeIntegerKernelComplexLaplace.lean) | 4 |
| [Zeta23.CCM.NativeLaplaceHalfPlaneContinuation](../../../../Zeta23/CCM/NativeLaplaceHalfPlaneContinuation.lean) | 2 |
| [Zeta23.CCM.NativePoleNeutralTrialDepth](../../../../Zeta23/CCM/NativePoleNeutralTrialDepth.lean) | 3 |
| [Zeta23.CCM.NativePositiveCompletionComplexLaplace](../../../../Zeta23/CCM/NativePositiveCompletionComplexLaplace.lean) | 3 |
| [Zeta23.CCM.NativeSelectedGroundSchur](../../../../Zeta23/CCM/NativeSelectedGroundSchur.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorAdmissibleSelector](../../../../Zeta23/CCM/OriginalDetectorAdmissibleSelector.lean) | 1 |
| [Zeta23.CCM.OriginalDetectorDividedLobeBounds](../../../../Zeta23/CCM/OriginalDetectorDividedLobeBounds.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseApproximation](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseApproximation.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseCarrier](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseCarrier.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseDepth](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseDepth.lean) | 1 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseL1Errors](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseL1Errors.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseMass](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseMass.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseNativeProducer](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseNativeProducer.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseNativeTransport](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseNativeTransport.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseNormControl](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseNormControl.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseNormalization](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseNormalization.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorFinitePhasePlane](../../../../Zeta23/CCM/OriginalDetectorFinitePhasePlane.lean) | 7 |
| [Zeta23.CCM.OriginalDetectorFinitePhaseWeilPadding](../../../../Zeta23/CCM/OriginalDetectorFinitePhaseWeilPadding.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorFinitePhysicalNorm](../../../../Zeta23/CCM/OriginalDetectorFinitePhysicalNorm.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorFinitePoleImage](../../../../Zeta23/CCM/OriginalDetectorFinitePoleImage.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorFinitePoleImageAsymptotics](../../../../Zeta23/CCM/OriginalDetectorFinitePoleImageAsymptotics.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorFinitePoleImageNonzero](../../../../Zeta23/CCM/OriginalDetectorFinitePoleImageNonzero.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorFinitePoleImageTransport](../../../../Zeta23/CCM/OriginalDetectorFinitePoleImageTransport.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorFiniteTransport](../../../../Zeta23/CCM/OriginalDetectorFiniteTransport.lean) | 8 |
| [Zeta23.CCM.OriginalDetectorFiniteWindowBoundaryFlat](../../../../Zeta23/CCM/OriginalDetectorFiniteWindowBoundaryFlat.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorFiniteWindowHigherFlat](../../../../Zeta23/CCM/OriginalDetectorFiniteWindowHigherFlat.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorFiniteWindowImage](../../../../Zeta23/CCM/OriginalDetectorFiniteWindowImage.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorFiniteWindowImageAsymptotics](../../../../Zeta23/CCM/OriginalDetectorFiniteWindowImageAsymptotics.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorFiniteWindowImageJets](../../../../Zeta23/CCM/OriginalDetectorFiniteWindowImageJets.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorFourierCoefficientBounds](../../../../Zeta23/CCM/OriginalDetectorFourierCoefficientBounds.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorFourierScalarTailBounds](../../../../Zeta23/CCM/OriginalDetectorFourierScalarTailBounds.lean) | 9 |
| [Zeta23.CCM.OriginalDetectorFourierTailAsymptotics](../../../../Zeta23/CCM/OriginalDetectorFourierTailAsymptotics.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorFourierTailBounds](../../../../Zeta23/CCM/OriginalDetectorFourierTailBounds.lean) | 11 |
| [Zeta23.CCM.OriginalDetectorNativeRetainedSelection](../../../../Zeta23/CCM/OriginalDetectorNativeRetainedSelection.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorOriginalPhaseL1Bounds](../../../../Zeta23/CCM/OriginalDetectorOriginalPhaseL1Bounds.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteH1Rate](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteH1Rate.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteNativeFormRate](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteNativeFormRate.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteNormalizedErrors](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteNormalizedErrors.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseApproximation](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseApproximation.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseCarrier](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseCarrier.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseDepth](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseDepth.lean) | 1 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseL1Errors](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseL1Errors.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseMass](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseMass.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeProducer](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseNativeProducer.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeTransport](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseNativeTransport.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormControl](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseNormControl.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormalization](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseNormalization.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhasePlane](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhasePlane.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseSymmetry](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseSymmetry.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePhaseWeilPadding](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePhaseWeilPadding.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePoleImage](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePoleImage.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageAsymptotics](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePoleImageAsymptotics.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageC4](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePoleImageC4.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageNonzero](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePoleImageNonzero.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageTransport](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePoleImageTransport.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorPaddedFinitePositivity](../../../../Zeta23/CCM/OriginalDetectorPaddedFinitePositivity.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteWindowBoundaryFlat](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteWindowBoundaryFlat.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteWindowHigherFlat](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteWindowHigherFlat.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteWindowImage](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteWindowImage.lean) | 6 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteWindowImageAsymptotics](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteWindowImageAsymptotics.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPaddedFiniteWindowImageJets](../../../../Zeta23/CCM/OriginalDetectorPaddedFiniteWindowImageJets.lean) | 4 |
| [Zeta23.CCM.OriginalDetectorPaddedFourierQuantitativeRates](../../../../Zeta23/CCM/OriginalDetectorPaddedFourierQuantitativeRates.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedPhaseQuantitativeRates](../../../../Zeta23/CCM/OriginalDetectorPaddedPhaseQuantitativeRates.lean) | 3 |
| [Zeta23.CCM.OriginalDetectorPaddedRetainedSelection](../../../../Zeta23/CCM/OriginalDetectorPaddedRetainedSelection.lean) | 2 |
| [Zeta23.CCM.OriginalDetectorPositiveFourierPadding](../../../../Zeta23/CCM/OriginalDetectorPositiveFourierPadding.lean) | 5 |
| [Zeta23.CCM.OriginalDetectorPositiveFourierPaddingReal](../../../../Zeta23/CCM/OriginalDetectorPositiveFourierPaddingReal.lean) | 4 |
| [Zeta23.CCM.OriginalSincCompactPotential](../../../../Zeta23/CCM/OriginalSincCompactPotential.lean) | 7 |
| [Zeta23.CCM.OriginalSincDriveCancellation](../../../../Zeta23/CCM/OriginalSincDriveCancellation.lean) | 4 |
| [Zeta23.CCM.OriginalSincDriveDecay](../../../../Zeta23/CCM/OriginalSincDriveDecay.lean) | 6 |
| [Zeta23.CCM.OriginalSincDriveDerivative](../../../../Zeta23/CCM/OriginalSincDriveDerivative.lean) | 3 |
| [Zeta23.CCM.OriginalSincDriveLp](../../../../Zeta23/CCM/OriginalSincDriveLp.lean) | 5 |
| [Zeta23.CCM.OriginalSincSourceSign](../../../../Zeta23/CCM/OriginalSincSourceSign.lean) | 5 |
| [Zeta23.CCM.OriginalSincWeightedPoleMoments](../../../../Zeta23/CCM/OriginalSincWeightedPoleMoments.lean) | 6 |
| [Zeta23.CCM.PoleNeutralCompactH2](../../../../Zeta23/CCM/PoleNeutralCompactH2.lean) | 4 |
| [Zeta23.CCM.PoleNeutralCompactH2Uniqueness](../../../../Zeta23/CCM/PoleNeutralCompactH2Uniqueness.lean) | 2 |
| [Zeta23.CCM.PoleNeutralCompactInverse](../../../../Zeta23/CCM/PoleNeutralCompactInverse.lean) | 3 |
| [Zeta23.CCM.PoleNeutralCompactInverseCore](../../../../Zeta23/CCM/PoleNeutralCompactInverseCore.lean) | 8 |
| [Zeta23.CCM.PoleNeutralCompactInverseL2Bound](../../../../Zeta23/CCM/PoleNeutralCompactInverseL2Bound.lean) | 6 |
| [Zeta23.CCM.PoleNeutralCompactL2Energy](../../../../Zeta23/CCM/PoleNeutralCompactL2Energy.lean) | 3 |
| [Zeta23.CCM.PoleNeutralCompactL2Regularity](../../../../Zeta23/CCM/PoleNeutralCompactL2Regularity.lean) | 8 |
| [Zeta23.CCM.PoleNeutralUniqueness](../../../../Zeta23/CCM/PoleNeutralUniqueness.lean) | 3 |
| [Zeta23.CCM.Step123PrimeSeam](../../../../Zeta23/CCM/Step123PrimeSeam.lean) | 2 |
| [Zeta23.ExceptionalZero.NativeActualKernelZeroJets](../../../../Zeta23/ExceptionalZero/NativeActualKernelZeroJets.lean) | 5 |
| [Zeta23.ExceptionalZero.NativeOriginalSourceLaplaceVisibility](../../../../Zeta23/ExceptionalZero/NativeOriginalSourceLaplaceVisibility.lean) | 3 |
| [Zeta23.ExceptionalZero.NativeRangeZeroJetObstruction](../../../../Zeta23/ExceptionalZero/NativeRangeZeroJetObstruction.lean) | 5 |
| [Zeta23.ExceptionalZero.NativeZeroJetAnalyticFactors](../../../../Zeta23/ExceptionalZero/NativeZeroJetAnalyticFactors.lean) | 8 |
| [Zeta23.ExceptionalZero.OriginalDetectorPhaseDepth](../../../../Zeta23/ExceptionalZero/OriginalDetectorPhaseDepth.lean) | 3 |
| [Zeta23.ExceptionalZero.UniversalSincInitialLaplace](../../../../Zeta23/ExceptionalZero/UniversalSincInitialLaplace.lean) | 4 |
| [Zeta23.ExceptionalZero.UniversalSincOriginalPhaseDepth](../../../../Zeta23/ExceptionalZero/UniversalSincOriginalPhaseDepth.lean) | 8 |
| [Zeta23.ExceptionalZero.UniversalSincSignedExcursions](../../../../Zeta23/ExceptionalZero/UniversalSincSignedExcursions.lean) | 4 |
| [Zeta23.ExceptionalZero.UniversalSincSignedPoleBound](../../../../Zeta23/ExceptionalZero/UniversalSincSignedPoleBound.lean) | 8 |
| [Zeta23.ExceptionalZero.UniversalSincSignedTailTransform](../../../../Zeta23/ExceptionalZero/UniversalSincSignedTailTransform.lean) | 3 |
