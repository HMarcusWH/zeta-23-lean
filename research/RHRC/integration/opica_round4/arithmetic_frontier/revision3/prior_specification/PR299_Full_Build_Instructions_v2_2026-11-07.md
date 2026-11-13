# PR #299 — Native Arithmetic Frontier
## Complete consolidated build instructions, revision 2

**Date:** 7 November 2026  
**Repository:** `HMarcusWH/zeta-23-lean`  
**PR / branch:** #299 / `research/madness`  
**Inspected head:** `c27abd86b2371b080e3b193ca359438ad008711c`  
**Inspected tree:** `36386fe15e6038b5180966bdc2a7e76801c49e88`  
**Original specification baseline:** `9c517db0befa1131bb60d37cfef2888ed69447a9`, tree `6d737c3e3f74a607ae1e1a4b958cc1e2cf9854e9`  
**Release class:** full replacement execution specification, not a proof or compiler receipt.  
**Terminal status:** Step 4 OPEN; RH OPEN.

This revision preserves the original work packages, source requirements, alternative closing routes, and claim gates. It recognizes completed implementation, inserts an evidence-repair increment before further numerical promotion, and concentrates the subsequent research on a complete signed arithmetic estimate. It does not restart the project, replace its objects, or turn every optional supporting programme into a prerequisite.

The review used the current PR metadata; the committed build specification, experiment and open-premise registers; the native certificate engine, independent checker and tests; the near-null scan; the E-H6 outcomes; and the previously inspected new Lean modules. The Round4 run was still queued with no conclusion at readback. No fresh Lean build or full native Arb replay was performed for this revision. Nine small exact-arithmetic/source-logic controls were executed in normal and optimized Python with identical results; their scope is explicitly not native certificate verification.

---

## 1. Decision and changes from the original plan

Continue in the same PR. Preserve the existing proof modules. Make the next implementation increment **2B: evidence semantics, acceptance repair, and independent replay**. Run the source-level arithmetic investigation in parallel; do not make a complete formalization of every numerical tool a prerequisite for analytic discovery.

After 2B, the primary mathematical increment is the complete native prime–Archimedean bound, or an independently proved alternative that reaches an existing closing consumer. A further finite checkpoint, a better inverse approximation, or a near-null count fit is not that supplier.

### 1.1 Current work-package status

| Original package | Current supported state | Instruction |
|---|---|---|
| A — source and constraint inventories | Registers exist; source coverage is partial and review levels vary | Complete provenance, correction and coverage records; do not equate a title-filtered search with the whole folder |
| B — exact native contracts | Seven modules added, with reported local compilation and explicit conditional premises | Preserve and qualify on the actual current head; do not rebuild |
| C — finite certificate engine | Engine, small independent reconstruction, large recorded outputs and tests exist | Repair acceptance semantics and distinguish raw verification from hash replay |
| D — discriminating experiments | L=6 is reported completed; coupled-response analysis is partial; leakage investigation not built | Compare exact certificate families and complete signed budgets before extrapolation |
| E — source-core reductions | General leakage/core consumer and conservative witness transport implemented | Add source-column/trace/approximate-kernel results only when they reduce a selected obligation |
| F — independent arithmetic supplier | OPEN | Research-critical work; no replacement by another definition of the desired inequality |
| G — adversarial controls | Preservation register and several tests exist; some engine tests skip in locked CI | Make acceptance-critical tests mandatory and restore exact historical target identities |
| H — unbounded availability | Limit-to-C1 consumer exists; all-parameter supplier remains OPEN | Prove escaping apertures and vanishing physical errors, or the same-packet exclusion |

### 1.2 Review findings requiring changes

**R1 — Overstated spectral conclusions.** The committed text describes positive, super-exponentially small bottoms across the tested states. The L=5 and L=6 records instead provide shifted lower bounds and small positive Rayleigh upper bounds. A positive Rayleigh value is not a positive lower bound on the entire slice. Keep the dedicated positive brackets at their exact small states and L=4 scopes; remove universal or asymptotic positivity language without its own theorem. Finite positive brackets also do not establish an asymptotic decay law.

**R2 — Floating decisions labelled as mathematical falsification.** In `native_slice.py:block_test`, branches can set `FALSIFIED_BOUND` using only floating eigenvalue comparisons. Equality is already a countercontrol: `A=[1], a=b=1` satisfies both `A>=aI` and `A<=bI`, while the inspected branch conditions take their falsification paths. Every claimed bound failure needs an exact/enclosed violating vector or a separately proved mathematical contradiction.

**R3 — Missing acceptance precondition.** `certify_psd` and `certify_shifted` test a squared residual against `tau^2` without first requiring `tau>0`. The exact input `A=[-1], tau=-2, R=[1]` has zero residual and passes that test although A is negative. Intended checkpoint calls use positive shifts; this countercontrol does not show their results are wrong. It does require a guard and regression test.

**R4 — Enclosures and witness norms must remain rigorous through the last comparison.** The custom `upper()` helper is not a general enclosing endpoint operation. For midpoint `m=-1+2^-54` and radius `r=1-2^-55`, its float conversion/addition can underestimate the exact upper endpoint `2^-55`. Some witness Rayleigh denominators also use `float(np.dot(v,v))`, not an exact/enclosed norm. Replace acceptance uses with certified endpoints and exact/enclosed quadratic norms. Display floats are not acceptance data.

**R5 — Different degree-64 certificates are being compared as though identical.** The current engine uses a proposed polynomial inverse action and an inverse-residual-square certificate. The historical scalar geometric-tail certificate is a different sufficient inequality. A result at `q^64/a>1` for the former does not replay or refute a threshold for the latter. Preserve both definitions and compare them on the same matrix.

**R6 — Historical gap-law targets changed.** The current `fixed_quarter_high_gap` concerns a shifted block in a reconstructed Fourier-prefix decomposition. The earlier report's strong high-mode law concerned an unshifted genuinely high-support legal slice. The interval, support, metric, and shift must all match before a result is called a reproduction. The registers themselves say the original definition was not imported.

**R7 — Independent replay coverage is narrower than record preservation.** The locked tests recompute the small archived cases. For the large endpoints they predominantly check hashes, stored statements, and stored statuses. The alternative assembly shares the canonical-source Arb backend. Name these assurance levels separately. A hash is not a reconstruction of the inequality, and 81 overlapping principal entries do not verify an entire large matrix.

**R8 — Near-null statistics changed definition.** The main engine counts `abs(lambda)<threshold`; the post-hoc scan counts `lambda<threshold`. The latter includes arbitrarily negative modes. For `diag(-1,10^-9,1)` and threshold `10^-8`, the counts are two and one respectively. The comparison is with the Riemann–von Mangoldt main term, not a certified exact zero count. The threshold dependence and P8 timing caveat must remain explicit.

**R9 — Corrected coordinates are not automatically orthonormal.** The interval-corrected basis has its own full Gram, potentially with nonzero cross blocks. The complete endpoint pencil includes the Gram, which is the right starting point. Do not separately describe its corrected complementary block as exactly physically orthogonal or transfer a coordinate gap to a physical gap without an adapter.

These findings require scoped repair and revalidation. They are not negative-energy witnesses for the actual native zeta form and do not invalidate the new general Lean proofs.

---

## 2. Standing mathematical and operational rules

Use the exact canonical source, every actual prime power and weight, the literal native cutoff, the actual parity and moment carriers, the canonical normalization, and the inherited physical norm. Preserve full complements, mixed terms, signed arithmetic, and all relevant tails.

Do not substitute a detector trial for a ground eigenvector; a retained first-birth cutoff for the original quartic cutoff; a synthetic negative matrix for a generated native packet; a phase average for the prescribed origin; a positive surrogate for the signed expression; or complex absolute squares for complex squares.

Proof states remain separate:

- **PROVED:** exact declaration and complete hypotheses established by verified Lean/compiler evidence at its stated source and environment.
- **DERIVED:** mathematical consequence or paper proof, with its exact premises; not a new formal declaration.
- **CERTIFIED FINITE:** rigorously justified finite computation on a frozen state; record its numerical assurance level, not Lean authority.
- **EXPERIMENTAL SIGNAL:** floating, fitted, or exploratory finding.
- **LEAD / HYPOTHESIS:** proposed mechanism or theorem.
- **OPEN:** unproved closing or supporting premise.

Local compilation and CI qualification are separate. A parent-head gate cannot qualify a changed successor merely because its conclusion was success. Unchanged proof bytes may retain accurately scoped historical proof evidence, but full successor acceptance still requires the prescribed current-source gates.

Preserve protected instructions, pins, historical registries, old semantic controls and existing public interfaces. No merge, draft-state change, permission change, or external publication is authorized by these instructions alone.

---

## 3. Closing contracts — retain all OR branches

### 3.1 C1: complete moment slices at sparse late apertures

At `K(L)=originalDetectorQuarticCutoff(L)`, retain

\[
\forall n\ge1\;\exists L\ge n+2\;\exists p\in\{e,o\}\;
\forall x\in\mathcal M_p(L,K(L)):\quad
Q_p(L,x)\ge-\frac1n\|x\|_{\rm physical}^2.
\tag{C1}
\]

Use the implemented `riemannHypothesis_of_cofinal_moment_slice_bounds`. Its arithmetic premise remains OPEN. The original eventual negative-witness theorem fixes one positive margin before all sufficiently large apertures and supplies witnesses in both parities. Preserve this exact composition.

One parity per checkpoint suffices, but the chosen parity must cover the entire slice. It cannot depend on the vector. No fixed parity, rank, inverse degree, positive spectral gap, rate, or interpolation between checkpoints is required.

The sequence adapter `cofinal_moment_slice_bounds_of_tendsto` is already implemented. Reuse it; proving the two limits and the bounds is still necessary.

### 3.2 Same-selected-packet source restriction

Use the implemented packet-uniform, one-output, or eventual-disjoint-quartic consumer. The actual selected packet has disjoint parity spectra at its own detector cutoff, so the two actual bottoms cannot tie there. This removes a separate global shared-ground exclusion only on that eligible route.

Supply the correctly oriented complete source responses below one at the same eligible lower negative ground. The existing identities give response one. Neither spectral noncollision nor channel nonvanishing gives a numerical separation or response bound.

A favorable aperture chosen independently from the packet does not suffice. Prove the restriction on eligible packet outputs or construct one output carrying both required properties. Keep the two existential selections coupled.

### 3.3 C2: actual long-term lower bound

Preserve the existing production theorem `riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower`. Its unresolved premise is

\[
\exists C>0\;\exists T\;\forall t\ge T:\quad
-C\le\operatorname{hyperbolaT}
(\operatorname{actualCorrelationLogarithmicTest}(t))
(\operatorname{actualCorrelationCutoff}(t)/2).
\tag{C2}
\]

Reuse the proved complete short-term, sampling, mass, diagonal, and normalization results. The required new result concerns the actual signed long term or its correctly adapted complete rank-one-plus-off-diagonal expression. Do not drop the positive rank-one contribution merely to match an easier-looking target.

### 3.4 Other branches

Keep the native K3 arithmetic programme and the source-conditioned causal residual/range programme as alternatives. K3 requires its own exact end-to-end reduction and uses a different carrier; the new quartic moment slices vanish at K3. For the causal route, distinguish already available convergence/tightness from the unproved zero residual or actual-input range statement. Reuse any existing qualified consumer after locating its exact source; a null navigation field is not proof that no historical theorem exists.

One completely proved branch suffices. Do not require all branches, all numerical tools, or all optional reductions before closing a successful route.

---

## 4. Preserve and qualify the implemented Lean layer

Keep the existing directory and namespace:

```text
Zeta23/OPICARound4/ArithmeticFrontier/
Zeta23.OPICARound4.ArithmeticFrontier
research/RHRC/integration/opica_round4/arithmetic_frontier/
```

Retain `MomentSlices`, `MomentSliceCoordinates`, `CofinalMomentClosure`, `SelectedPacketClosure`, `PhysicalBlockCertificate`, `SourceColumnCore`, and `Validation/Carriers`. The increment reports 97 new declarations, bringing the audited scope to 1,176 declarations in 97 modules and 96 semantic controls. Verify actual counts at the successor rather than freezing them as desired outputs.

Do not replace the conservative `d-3 eta` witness-transport theorem merely to recover a sharper paper constant. Improve a constant only if a candidate arithmetic proof needs it.

Keep the proof distinction between the general core consumer and a native source-column construction: `SourceColumnCore` currently accepts an arbitrary subspace or column map and a leakage hypothesis. It does not establish the trace identity, select actual source columns, or prove a universal approximation theorem.

### Acceptance

Fresh exact-source compilation, expanded independent consumers, full type/axiom audit, intended semantic rejections, and final current-attempt qualification. Conditional reductions remain labelled conditional after all these gates pass.

---

## 5. Increment 2B — repair numerical acceptance and evidence semantics

This increment is required before promoting new large-state numerical claims or extrapolating a degree/gap law. It is deliberately narrower than a complete formal verification of the numerical stack.

### 5.1 Exact status rules

`CERTIFIED` requires an accepted certificate of the exact stated inequality. `FALSIFIED_BOUND` requires a rigorously enclosed violating vector or a mathematical contradiction for that exact bound. Floating proposals, a failed Cholesky, an unresolved pivot, and equality at a non-strict bound do not establish falsification.

Use `UNKNOWN_PRECISION`, `NOT_ELIGIBLE`, or a separately versioned discovery status where appropriate. Invalid arguments must raise a declared error or use a versioned invalid-input disposition. Do not silently add strings outside the frozen schema.

For `A >= aI`, verify `v*(A-aI)v < 0` before marking failure. For `A <= bI`, verify `v*(bI-A)v < 0`. Store the exact vector and enclosing scalar. For a scalar-gap exclusion for every admissible a, certify the Rayleigh upper bound used in the quantifier argument, not just the final negative quadratic expression.

### 5.2 Certificate preconditions and endpoints

Require finite `tau>0` in shifted-factor acceptance. Check dimensions and establish the symmetry/Hermitian provenance required by the algorithm. Handle legitimate zero-dimensional complements explicitly, while rejecting vacuous smaller-cutoff substitution for a nontrivial quartic target. An LDL routine reading one triangle must not silently accept an unrelated nonsymmetric input.

Keep acceptance comparisons inside exact or outward-enclosing arithmetic. Use certified rational/dyadic endpoints, not custom midpoint/radius conversion through nearest-rounded floats. Store exact/enclosed physical or coordinate norms, according to the declared inequality. A vector made from binary floating entries is a legitimate exact dyadic proposal; its squared norm still needs exact/enclosed evaluation.

Proposed factors and inverse actions may be floating-generated, but all their residuals and final inequalities must be certified. Reject NaN, infinity, an uncertified inverse, an unidentified source, or a missing carrier/metric adapter.

### 5.3 Exact carrier semantics

An interval containing zero is a consistency check, not a proof of an exact equation. Preserve a mathematical definition of the exact corrected basis, e.g.

\[
Y_* = Z-E_P(C_*E_P)^{-1}C_*Z,
\]

with the exact native constraint matrix `C_*`, a certified invertible pivot block, and an interval enclosure of that exact construction. Prove `C_* Y_*=0` algebraically and certify rank through the full Gram. The existing correction approach can be justified this way; it is not necessary to discard it.

Alternatively use the existing fixed rational moment seed and proved diagonal map. Retain the exact relationship between the selected construction and the Lean carrier.

After correction, carry the actual full Gram, including any off-diagonal block. Call a basis an orthonormal **proposal** until exact physical orthogonality is proved. For physical block spectral claims use generalized eigenvalues relative to the relevant Gram or a proved orthonormalization.

The numerical real-symmetric representation also needs its explicit complex-space adapter: real constraints give a complexified slice, and a real symmetric form's value on `u+i v` is the sum of its values on u and v. Establish the actual source reality/symmetry before using this extension.

### 5.4 Proof-carrying outputs

Export reconstructible exact/dyadic proposal coordinates, pivot indices, correction recipe, full physical Gram/enclosure binding, factors or inverse actions, negative witnesses, and complete source-enclosure references. Record compiler/backend/library versions, precision, state parameters, source hashes, and environment identity.

A SHA of a midpoint float array is not a hash of the rigorous Gram enclosure. Store separate hashes for proposals, enclosures, exact semantic objects/recipes, and display summaries. Complete native entries may be streamed or represented by a certified formula plus rigorous remainder data; a huge duplicate matrix file is not mandatory if the verifier can reconstruct the whole object.

The final verifier must recalculate the decisive inequalities. It must not trust the producer's status string. A hash verification certifies byte identity only.

### 5.5 New mandatory countercontrols

Add equality-at-bound tests; zero and negative tau; tiny negative and tiny positive matrices; unsupported nonsymmetric input; non-enclosing endpoint conversions; wrong norm denominators; invalid carrier corrections; shifted/unshifted substitutions; wrong cutoff; modified prime weights; dropped Gram cross blocks; altered factor/residual/witness payloads; and mixed source/run attempts.

Use the accompanying exact miniature controls as specifications for regression cases, not as substitutes for tests against the repaired actual functions. Run acceptance-critical controls in the locked environment without optional NumPy skips. A NumPy discovery layer may remain separate, with honest optional status, but its absence must not remove essential acceptance checks.

### 5.6 Correct records without erasing history

Preserve original `increment2` records and source hashes. Add a correction/supersession map and new regenerated records, rather than rewriting every old record to match new code and calling it an unchanged replay.

Revise positive-bottom/asymptotic wording; float-only bound-failure labels; exact historical gap identities; polynomial-certificate identities; the threshold statistic; and the exact-source independence statements. A correction applies only to its identified claim and scope.

### Acceptance

The repaired functions reject all identified invalid controls; all promoted finite conclusions have reconstructible witnesses or sufficient certificates; changed acceptance paths trigger regeneration or explicitly justified revalidation of affected states. Report any result not yet rechecked as such. Nothing in 2B assumes that a valid old native endpoint is false.

---

## 6. Work package A — source, constraint and history reconciliation

Complete the original source ledger using the actual folder membership, not only titles matching a query. Record each Drive ID, filename, MIME type, hash when bytes are obtained, report/evidence relationship, exact repository pin, and coverage limitation.

Use distinct levels `DISCOVERED`, `FETCHED`, `TEXT_REVIEWED`, `PROOF_AUDITED`, `REPLAYED`, `LEAN_VERIFIED`. A discovered filename is not a proof reviewed; a successful download is not a replay. Files not retrievable with one connector path remain explicitly unavailable/unreviewed rather than implicitly irrelevant. Preserve authenticated provenance when using a supported raw-file retrieval alternative.

Reconcile metadata against current complete theorem types. Keep historical text in its historical scope. For every candidate record two axes: native validity and closing relevance. A proved identity can have no opposing-sign content, while a strong proposed bound may be false.

Each candidate needs the exact proposition, source/carrier, parameter order, retained hypotheses, dependencies, falsification controls, target consumer, expected budget improvement, and authority. Add a scope-specific correction ledger for this revision.

### Acceptance

Every closing premise and proposed source replacement has a named, inspectable record; no missing arithmetic inequality is hidden inside a data structure or generic regularity assertion. Source coverage is measurable and incomplete coverage is visible.

---

## 7. Work package B — exact carriers, metrics and consumers

Preserve the implemented moment slices: physical even M4 zero inside the actual even pole-neutral carrier; physical odd M3=M5 zero inside the actual odd pole-neutral carrier. Boundary-flat constraints are inherited, not replaced.

Reuse `beta=(L/(4 pi))^2` and `D_n=beta+n^2`. The specification chart `L^2+16 pi^2 n^2` differs by the fixed positive factor `16 pi^2`. Every energy and Gram conversion must carry that factor consistently.

The fixed seeds are

\[
V_{e,K}=\{y\text{ even}:M_0=M_2=M_4=M_6=0\},\qquad
V_{o,K}=\{y\text{ odd}:M_1=M_3=M_5=M_7=0\}.
\]

Retain the proved dimensions `K-3` and `K-4` with natural subtraction and the theorem's small-K hypotheses. Both slices vanish at K=3; the odd slice also vanishes at K=4. At the quartic cutoff for L>=2 their dimensions are at least 13 and 12.

For a complete coordinate inclusion U, the relevant matrices are

\[
F=U^*D_LE(L)D_LU,\qquad G=U^*D_L^2U,
\]

and the physical target is `F+eps G >= 0`, not `F+eps I >=0`. A fixed-aperture Gram-comparison theorem remains a supporting task when aperture transport is actually used; it is not a prerequisite for direct sparse endpoints.

Keep independent complete-type consumers and semantic controls for all-vector versus one-trial bounds, parity before vector, cutoff identity, K3 vacuity, metric transport, same-aperture composition, and trial/ground distinction.

### Acceptance

Do not rebuild what already compiles. Add only missing adapters needed by a selected proof/certificate. Conditional C1 and packet consumers stay conditional until their independent premises are proved.

---

## 8. Work package C — independent finite certification

### 8.1 Four assurance levels

Record these separately for each named result:

1. Byte/hash and schema verification.
2. Recalculation of the certificate inequality from supplied complete data.
3. Independent native source/basis reconstruction; name shared backend primitives.
4. Lean soundness plus a proved bridge from accepted enclosure data to the actual canonical source.

The current small-state checker gives genuine additional reconstruction coverage, but shares source primitives. The large recorded status checks are not level 3. No finite numerical result is level 4 merely because its generic Schur theorem exists in Lean.

### 8.2 Large-state verification

After 2B, independently reconstruct and verify the complete L=4, L=5 and L=6 targets actually being promoted. Prioritize the new L=6 physical quarter bound. Use the archived independent exact-rational source path where available, or a genuinely independent rigorous complete-form source adapter. Entry overlap alone is corroboration, not positivity proof.

It is acceptable first to complete a second basis/LDL or residual reconstruction using shared source primitives, provided the shared trust boundary is stated. It is not acceptable to relabel that as an independent transcendental-entry generator. Do not force a cubic naive full-matrix algorithm when streaming or certified structured assembly proves the same object.

Resource-limited runs must report their actual coverage; do not replace full coverage with sampled minors. Numeric validation is a parallel research workstream, not an indefinite barrier to an independent analytic supplier.

### 8.3 Preserve the endpoint ledger

Retain small archive margins and dedicated L=4 positive brackets as bounded claims. Preserve reported shifted L=4 bounds at 1/2 and 1/1024; L=5 at 1/3 and 1/1024; and L=6 at 1/4. Record whether each is original, newly generated, independently reconstructed, or correction-pending.

Do not infer positive unshifted L=5/L=6 minima from those shifted statements. Do not infer an asymptotic positive-bottom law from finite samples.

### 8.4 Lean numerical bridge

`FiniteCertificateSoundness` and the native enclosure bridge remain OPEN. Build them if certified endpoints are to become Lean facts or if the chosen final proof uses computational certificates. An analytic all-parameter proof may close the route without reflecting every historical numerical example.

### Acceptance

Each result's exact state, norm, source, full-vector quantifier, certificate family, and assurance level can be reconstructed independently. No necessary assertion is supported only by a stored success label.

---

## 9. Work package D — complete coupled-response experiments

### 9.1 Distinguish the three certificate families

On the same shifted pencil `B=[[D,C],[C*,A]]`, with `A>=aI>0`, keep distinct identifiers for:

**Scalar gap:** `D-a^-1 CC*`.

**Geometric tail:** with `T=I-A/b`, `P_m(A)=b^-1 sum_{j<m}T^j`, and certified `A<=bI`,

\[
S^{\rm tail}_m=D-CP_m(A)C^*-\frac{q^m}{a}CC^*,\qquad q=1-a/b.
\]

**Inverse-residual action:** for any exact proposed X and `R=C*-AX`,

\[
S_X=D-CX-X^*C^*+X^*AX-a^{-1}R^*R.
\tag{C3}
\]

The general certificate requires no upper bound on A. A chosen b may be merely a numerical parameter for proposing X; it becomes a mathematical upper-bound hypothesis only when a spectral polynomial/tail argument uses it.

For an exact polynomial action `X=P_m(A)C*`,

\[
R=T^mC^*,\qquad
S_{\rm exact}-S_X=R^*(a^{-1}I-A^{-1})R.
\]

This is not the historical scalar `q^m/a` penalty. If X is a rounded approximation to that polynomial action, its complete residual remains valid, but the exact polynomial identity needs an error adapter. Freeze certificate-family identifiers before comparing required degrees or interpreting P4.

### 9.2 Resolve inverse mass rather than fit a worst gap

Implement the original E-D1 cumulative coupling quantity

\[
M(s)=C\mathbf1_{(0,s]}(A)C^*.
\]

Its relevant inverse response is matrix-valued. For a rigorously separated low spectral region,

\[
CA^{-1}\mathbf1_{(0,s_0]}(A)C^*
=\frac{M(s_0)}{s_0}+\int_0^{s_0}\frac{M(s)}{s^2}\,ds.
\]

Work in proved physical orthonormal coordinates or carry the metric operator explicitly. Certify spectral projectors with gaps or use a rigorously bounded projector-free rational/polynomial/residual alternative. Floating eigenvectors alone do not define certified sharp spectral bands. If a band boundary intersects the spectrum enclosure, move it with a recorded rule or report unresolved membership.

Compare response against the retained signed diagonal in Loewner/quadratic-form terms. A trace or norm statistic may guide discovery but need not control the worst retained direction.

### 9.3 Predeclare what the next experiment will distinguish

Use the existing L=4,5,6 states to compare families, tolerances and source-aware split choices. Record coupling mass, full response, residual, near-band contribution, all errors and final physical margin. A fitted inverse degree is not an arithmetic theorem.

Call a degree the smallest successful **tested** degree unless all lesser cases are resolved or monotonicity justifies the assertion. Permit degree/rank to grow. Never argue that convergence of inverse approximation forces a nonnegative Schur complement: it also approximates a negative one faithfully.

### Acceptance

A proposed source-specific scaling inequality is frozen and survives matched tests, or a precise mechanism is falsified. Another positive endpoint without a discriminating signed-budget comparison does not complete D.

---

## 10. Work package E — source-core and mixed approximation support

Keep the implemented general C4 consumer:

\[
\eta\le\varepsilon/4,\qquad
D_I+(11\varepsilon/12)G_I\succeq0
\quad\Longrightarrow\quad H+\varepsilon I\succeq0.
\tag{C4}
\]

The leakage bound is against the complete complement, including all cross interaction. It is not a small quadratic-form statement restricted to that complement.

When useful, construct actual source columns `C=H[:,I]` in a declared physical frame, prove full column rank where an inverse is used, and define `P` as the physical orthogonal projection onto their span. Prove

\[
G_I=C^*C=(H^2)_{II},\qquad D_I=C^*HC=(H^3)_{II},
\]

and

\[
\|(I-P)H\|_F^2=
\operatorname{tr}(H^2)-\operatorname{tr}(G_I^{-1}(H^4)_{II}).
\]

Provide the nonorthogonal Gram version. In numerical use prefer directly enclosing the residual when subtracting nearly equal traces is ill-conditioned. An identity does not make every numerical evaluation stable.

Reuse `core_witness_transport`, retaining a nonzero projection of the same trial and a margin `d-3 eta` when its hypotheses apply. Do not rename it a ground eigenvector.

The universal approximate-kernel theorem remains a paper result to audit: endpoint jets and integration by parts, all zeros and multiplicities, reflected channels, unconditional counts, mixed Weil identity, exact physical normalization, dimension and nonvacuity, and parameter order must all be checked. Separate zero-defined existence from a source-computable core construction. Low-rank indefinite perturbations must remain part of its falsification suite.

### Acceptance

Only supporting results needed by a selected arithmetic argument become required formalization. The signed core premise is still an independent open condition; near-nullity, dimension savings, and fast approximation are not substitutes.

---

## 11. Work package F — independent native arithmetic information

This is the research-critical package. Conduct it alongside the finite checker repair rather than waiting for every numerical convenience theorem.

### 11.1 First proof target: actual pole-channel annihilation

Search the production theorem inventory before adding a duplicate. If not already exported at the needed level, formalize the exact pole-kernel factorization and its vanishing on the two actual pole-neutral carriers. Establish the full compressed sesquilinear/operator statement, not only one vector's numerical near-zero energy.

Then derive the exact canonical energy `-arch-prime` on the relevant carrier, retaining every scalar normalization and boundary term in those definitions. This is dependency compression, not positivity. Do not remove a term from numerical assembly until its exact adapter is established and independently checked against the unchanged complete source.

### 11.2 Main matrix investigation: the combined signed arithmetic

Study `-arch-prime` jointly, not separate minima as a replacement. The existing tests attack the particular separated-minimum sufficient estimate; they do not forbid every use of channel-specific information inside a coupled proof.

Seek a decomposition

\[
\text{required signed budget}
=\text{independently controlled native terms}
+\text{explicit remainder},
\]

with constants and parameter dependence fixed in the theorem. Keep the canonical diagonal, all mixed terms, nearby modes, prime powers and tails. A positive Gram representation is useful only after its equality to the full target is independently proved; defining a factor through assumed positivity is circular.

### 11.3 The one-normal source response

Build `MomentLeakage` and `NativeLeakageArithmetic` only with the correct compressed commutator identity. With physical orthonormal V, `P=VV*`, `D0=diag(n^2)`, `J=V*D0V`, `H=V*EV`, leakage `(I-P)D0V=w ell*`, and `z=V*Ew`, first prove

\[
[J,H]=V^*[D_0,E]V+z\ell^*-\ell z^*.
\]

Only discard `V*[D0,E]V` after proving its vanishing on the actual carrier. Retain the signed numerator `z_i conj(ell_j)-ell_i conj(z_j)`. Geometry spectrum J and energy spectrum A are different; crossing between them requires a proved adapter. Control of the commutator still leaves diagonal/absolute-energy information to be supplied.

### 11.4 Direct arithmetic alternative

Pursue C2 through the literal complete off-diagonal/rank-one expression or a precisely adapted source-conditioned prefix estimate. Reuse the proved sampling and diagonal bounds. Preserve actual Möbius coefficients, equal-product recombination, all prime powers, half-history cutoff, the original fixed source, and the prescribed origin.

A growing factor-count sector location, a good phase average, or a small high-mask tail does not control the original complete field. Give the remaining small masks, balanced region, and signed cross terms explicit budgets.

### 11.5 Candidate promotion contract

Before a candidate enters production Lean, require: exact object and theorem statement; independently proved native hypothesis; explicit parameter order; the previously unpaid term controlled; full remainder budget; adapter to a closing consumer; no hidden RH-equivalent premise; matched countermodel outcome; and an independent paper-proof review.

A property that distinguishes ordinary integers from a generalized model is not yet a supplier. Show how it forces the required sign. Conversely, a true general identity need not distinguish every model to be useful; the complete closing chain must use a genuinely restrictive native property somewhere.

Use the existing governed deduction engine and fixed-target elaboration. Add proved roots that close dependencies, not just a larger syntactic menu or an enlarged search budget. Search exhaustion is bounded-search evidence, not mathematical impossibility.

### Acceptance

An actual-source signed inequality with useful unbounded quantifiers is proved, or a named candidate is falsified/refined with a precise remaining lemma. An empty `ArithmeticSupplier` interface cannot complete F.

---

## 12. Work package G — adversarial models and experimental discipline

Keep separate preservation maps for scalar shifts, low-rank indefinite perturbations, on-line/off-line quartets, positive generalized arithmetic/completion, finite staircase truncations, stationary averages, separated arithmetic sectors, and contact/extension controls. Never pool preserved features of different models into a fictional single counterexample.

Match the source, carrier, support, cutoff, metric, sign convention and conditional eligibility of the proposed theorem. A test on a positive arbitrary trial is not a test of an actual negative-ground identity. No eligible native packet means `NOT_ELIGIBLE`, not successful exclusion.

The previous pure-high-support unshifted-gap failure must be reproduced on that exact support and metric, or remain a separately cited historical result. The newer shifted-prefix test gets a separate ID. Apply the same discipline to degree-64 certificate families and upper caps with different constants.

For the near-null experiment record separately: `#(|lambda|<delta)`, `#(lambda<delta)`, negative-eigenvalue information, undecided eigenvalue enclosures, and threshold delta. Compare against a quantity named `N_main(T)` until an exact certified zero-count input is supplied. Do not insert unverified on-line zero locations into a universal argument.

A concrete prospective test requires fixed numerical tolerance/constants, not “deviation greater than O(log T).” Preserve P8 as timing-compromised/post-hoc-risk evidence. Do not erase its caveat by recommitting the same prediction. Freeze new predictions before generation, with immutable source-state and rule hashes.

Near-null count tests have lower priority than signed-budget tests unless they directly select a verified core, bound its residual, or falsify a candidate supplier.

### Acceptance

The model map records precise exclusions, not blanket claims of impossibility. New test results distinguish source-sign information from generic low-rank or interpolation effects.

---

## 13. Work package H — unbounded availability and terminal composition

Close either C1, the same-packet restriction, C2, or another fully adapted branch. For the sequence route prove physical lower bounds along apertures escaping every bounded set and errors tending to zero. No rate is required.

A continuation procedure must prove non-stalling and its complete accumulated-error law. Positive increments can sum to a finite aperture; individually small errors can accumulate. Prove either direct endpoints or the necessary transport/error recurrence, with exact cutoff and carrier adapters.

The next possible diagnostic horizon after L=6 is `n=5, L>=7, eps<=1/5`. At exactly L=7, `K=2401`, with slice dimensions 2398 and 2397. One parity suffices. Do not automatically run it before a frozen signed-budget law states what the run will discriminate. A smaller epsilon at L=6 does not replace a later horizon for all n.

Once an independent supplier exists, compose it with the implemented conditional consumer and audit the exact Mathlib `RiemannHypothesis` conclusion. No undispatched arithmetic/RH-equivalent assumption may remain. A terminal theorem taking C1 or a source-response exclusion as an argument is still conditional, regardless of its name.

### Acceptance

Complete formal proof and claim-validation gates at the final source; no current-head gate borrowed from an earlier tree; no independent analytical premise hidden in a data import. Only then may the selected Step 4 route be called closed.

---

## 14. Data and schema requirements

Extend existing products rather than creating a second governance system. Preserve `SOURCE_LEDGER.json`, `CONSTRAINT_REGISTER.json`, `MODEL_PRESERVATION.json`, `STATE_SCHEMA.json`, `BUDGET_SCHEMA.json`, `EXPERIMENTS.json`, `CANDIDATE_RESULTS.jsonl`, `OPEN_PREMISES.json`, `WORKFLOW_HARVEST.json`, and `BUILD_SPEC.md`.

Add or extend versioned fields for:

| Field group | Required meaning |
|---|---|
| Exact target | statement ID, original/reconstructed/new formulation, certificate family and mathematical hypotheses |
| State | rational/exact aperture, literal cutoff expression/value, prime cell and complete weights, parity, carrier, dimensions, full physical Gram |
| Decomposition | support/projection, coordinate versus physical gap, shifted/unshifted object, complete coupling and inverse domain |
| Proposal | exact dyadic data, pivots, factors/inverse actions, seed and environment; distinct from certified enclosure |
| Evidence | complete payload locator/hash, exact endpoints, verification recipe, negative witness, producer/verifier identities |
| Verification | hash-only, supplied-data replay, independent reconstruction, independent entry generation, Lean bridge; no conflation |
| Prediction | immutable freeze, pre-output timing, exploratory/post-hoc status, fixed quantitative acceptance rule |
| Correction | superseded claim/scope, original record retained, reason, affected results and required rerun |
| Outcome | supported disposition plus uncertainty and resource limits; sign failure separated from estimate failure |

Bind exact enclosure bytes/recipes, not merely display decimals or midpoint arrays. A summary must not silently acquire a stronger claim than its payload.

---

## 15. Lean module roadmap

| Module / area | Action |
|---|---|
| Existing seven frontier modules | Preserve, audit and qualify; extend only for an actual missing adapter |
| `PhysicalBlockCertificate` | Retain exact residual identity and general certificate; add typed metric adapters when needed |
| Pole-channel identity module, name chosen after reuse search | Prove full native compression vanishes; derive unchanged complete source decomposition |
| `MomentLeakage` | Full compressed commutator, actual normal geometry, all terms retained |
| `NativeLeakageArithmetic` | Complete canonical source action on the normal; explicit normalization and signs |
| `SourceColumnCore` | Optional actual source-column construction, physical projection, Gram and residual identities |
| `FiniteCertificateSoundness` | Pure verification soundness, validation preconditions and exact statuses |
| Native enclosure bridge | Actual source entry/form inclusion, all prime powers and analytic remainders |
| `NativeApproximateKernel` | Optional universal mixed estimate after paper audit and utility decision |
| `ArithmeticSupplier` | Create only with a concrete independently proved estimate, not as fulfilled empty infrastructure |
| `Step4Terminal` | Compose a proved supplier and quantified reach/selection into exact RH |

Proposed names are not claims of existing files. Search the accumulated theorem inventory first. Generic mathematical helper files must not import a conditional RH consequence to supply their own premise. Audit logical dependence as well as axiom declarations.

---

## 16. Integration, tests and workflow qualification

Continue through the existing closed manifest and path-policy amendment mechanism. Keep original content/proof scope hash-bound. Update roots, math contracts, MADNESS scope, independent validation consumers, acceptance matrix, closure obligations, research dispositions, graph classifications and canonical generated products coherently.

`SOURCE_CONSTRAINTS.json` and `EXPECTED_TESTS.json` are protected in the implemented contract. Do not weaken or casually rewrite them. Register additional requirements through the supported additive mechanism; any necessary scope amendment must be explicit and independently validated. Do not preserve a nominal test count by silently hiding a new required skip.

Port acceptance-critical controls away from optional NumPy. Keep discovery dependencies in an explicitly declared environment. No ad hoc dependency installation inside a hash-locked gate, deletion of negative controls, relaxed placeholders, or acceptance of prior-attempt producer artifacts.

Integrate the work into the existing lanes: contract/generated-state, mathematical support, semantic negatives, source numerics, formal composition, parent regression/current compatibility, replay campaign, independent groups, and final acceptance.

For each workflow/job record the exact head, tested tree, run and attempt; classify formal validity, regression, or research-producing role; extract its actual scientific disposition; compare with the previous frozen result; and preserve running, skipped and unavailable evidence as those states. A successful historical falsifier is not a positivity theorem.

Require full types without elisions, transitive axioms, exact environment identity, no `sorryAx`, no project axioms, and only admitted standard axioms. Distinguish raw source inspection, verified local compilation, current-head CI, and proof of numerical enclosure correctness.

Update the PR's stale front-page progress note so that it describes the current continuation rather than only the November 2 paused handover. Keep historical links and statements intact as history.

---

## 17. Revised execution order

**Increment 2B — correctness and evidence repair.** Correct statuses and claims, add guard/countercontrol coverage, freeze exact targets and certificate families, export verifiable payloads, and independently recheck affected large results. Deliver a per-result correction table rather than a blanket invalidation.

**Increment 3A — exact native source simplification, in parallel.** Reuse or prove pole-channel annihilation. Establish any missing real/complex and metric adapters. Study the complete signed prime–Archimedean expression. This work need not wait for every large numerical replay.

**Increment 3B — discriminating response tests.** Complete E-D1, retain diagonal and near-band budgets, distinguish all sufficient certificates, and test the smallest candidate native inequality on the existing states. Near-null counting remains a diagnostic, not the main endpoint.

**Increment 4 — formalize the useful candidate prerequisites.** Build leakage, source-column, mixed-kernel, or fixed-origin helpers only when they reduce a named missing estimate. Reuse the existing typed deduction system.

**Increment 5 — independent arithmetic supplier.** Produce a complete paper proof, adversarial review, exact-source Lean theorem and required parameter control. Record failed candidate laws with their scoped reasons.

**Increment 6 — quantify and close.** Prove cofinal availability, same-packet exclusion or the selected alternative, then compose and validate the exact final theorem. Preserve the OR structure; bypass unnecessary numerical/support work if an independent branch closes directly.

A staged PR increment may legitimately finish with quantified research progress and an OPEN supplier. It must state exactly what changed and must not relabel that increment as Step 4 closure.

---

## 18. Post-Green Research Pass and delivery requirements

After each meaningful green result, immediately read and use its exact statement. Report:

1. What became formally true, at which source/environment, with which premises.
2. What every workflow established, preserved, falsified, skipped or left pending.
3. What changed in strength, assumptions, generality and dependencies.
4. Upstream simplifications or weakened assumptions now available.
5. Downstream obligations made smaller or newly reachable.
6. Earlier failed routes whose failure reason changed, with precise evidence.
7. New RH-relevant clues, labelled as leads rather than theorem authority.
8. Fast falsification checks, including scope-preserving countermodels.
9. Highest-leverage next mathematical move, prioritized by information gained.

Deliver updated source/evidence/constraint/open-premise registers, complete proof/certificate payloads and receipts, exact matched negative controls, the workflow harvest, and a human-readable handover. No source or CI change was made by the review that produced these instructions.

**Final decision rule:** a new build earns mathematical value by establishing a genuinely restrictive fact about the actual signed source, or by precisely eliminating a candidate mechanism. Cleaner interfaces, stronger replay and compression are useful supporting work, but the closing estimate must still be independently proved.

---

## 19. Source register for this revision

All repository file links below are pinned to the inspected head. The original full build plan in the conversation is the preserved scope baseline; the committed BUILD_SPEC is an implementation progress record, not a replacement for every original obligation.

- PR metadata: https://github.com/HMarcusWH/zeta-23-lean/pull/299
- Current build record: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/BUILD_SPEC.md
- Native engine: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/native_slice.py
- Independent checker: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/independent_check.py
- Test coverage: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/tests/test_arithmetic_frontier_native.py
- Experiments and historical-scope caveats: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/EXPERIMENTS.json
- Near-null scan: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/nullcount_scan.py
- E-H6 outcomes: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/evidence/increment2/E-H6_OUTCOMES.json
- Open premises: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/research/RHRC/integration/opica_round4/arithmetic_frontier/OPEN_PREMISES.json
- Exact C1 consumer: https://github.com/HMarcusWH/zeta-23-lean/blob/c27abd86b2371b080e3b193ca359438ad008711c/Zeta23/OPICARound4/ArithmeticFrontier/CofinalMomentClosure.lean
- Round4 workflow inspected, not yet qualified at readback: https://github.com/HMarcusWH/zeta-23-lean/actions/runs/42375571963

The accompanying `review_exact_controls.py` and its two JSON receipts check nine miniature exact/source-logic cases. They do not execute the repository Arb engine or validate native matrices. The counterexample to the hand-rolled endpoint helper is about that helper's general enclosure promise; the negative-tau example is about an unchecked API precondition. Neither is presented as a negative vector for the actual canonical source.
