# Proposed PR #283 — Canonical compressed contact calculus and inherited saturation

**Repository:** `HMarcusWH/zeta-23-lean`  
**Specification date:** 4 October 2026  
**Status:** IMPLEMENTED CANDIDATE on branch `proof/post282-canonical-contact-calculus`; exact-head Lean/CI validation pending. Candidate declarations are not PROVED until the compiler, axiom, proof-escape, research-integrity, and post-green gates pass.  
**Suggested branch:** `proof/post282-canonical-contact-calculus`  
**PR number:** #283 candidate (branch prepared for pull request creation).  
**Terminal claim:** `RH_OPEN`.

## 0. Executive decision

Build one connected theorem-and-certification PR that replaces the missing analytic inputs of the post-#282 strict-even frontier with actual production proofs. The primary mathematical endpoint is a generated-contact alternative: a transverse strict-even crossing must be fresh-born; an inherited strict-even crossing must instead satisfy the exact stationary arithmetic saturation balance.

The PR has a mandatory calculus/completion contract and a bounded arithmetic-discovery contract. It is not complete merely because modules with the expected names exist. It does not close RH unless it also proves a separate, branch-complete canonical arithmetic barrier and composes that barrier with the existing off-line-zero construction.

Three distinctions are essential:

1. The canonical matrix, carriers, production source value, and off-line-zero construction are inherited objects, not redesigned here.
2. The raw ambient derivative candidates and their old curvature are not universally correct seam derivatives. Introduce correctly named compressed-first derivatives and curvature, retain the old meanings, and prove compatibility only where it holds.
3. A source-derived arithmetic exclusion is a research target. The saturation equality itself is a necessary condition, not exclusion.

Source identifiers `[Sxx]` refer to `SOURCES.json`. Existing-source facts, proposed theorem targets, and new finite sanity checks are distinguished throughout.

## 1. Exact merged starting point and authority

| Object | Verified identity |
|---|---|
| Merged PR | #282 |
| Validated human head | `de2869d1614d71b5d851d7088be514901af11b74` |
| Tested synthetic merge | `e84716bb77dc8579bdb765e2de29e7a206d2b6cf` |
| Actual merge / current main at review | `01871f7d2256b1eac2dbd7967346954367c8eef9` |
| Human-head, tested-merge, and actual-merge tree | `c7749d37c4b63270818c3fb0d7fb5dbc22638790` |
| Merge time | `2026-10-03T22:13:50Z` |
| Previous #281 merge | `0c22ae4101d7ad3e0b1a81029fff1472c52a5750` |
| Previous #281 tree | `f729b05e6fee9f6fbeb9d18a65e26742086244f8` |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc2` |

These were read from live GitHub. Equality of the source trees transfers the exact-tree compiler evidence to the merged source object; no claim depends solely on the PR title. [S01–S04]

The original 16-run, 41-job cohort is fully successful. Its last main `python-rhrc` job printed `Control v2 smoke: PASS` at `2026-10-03T22:07:35.9616111Z`. An additional same-head post268 replay, run `37157710493`, completed ten more jobs. Its 44-check harvest records clean source de2869/c7749, no missing/extra/duplicate results, no errors, and no theorem promotion. Thus the observed scope is 17 successful runs and 51 successful jobs, with no remaining running or failed job in that scope. The additional run began around merge time and finished afterward; this specification does not infer why GitHub triggered it. [S05–S07]

The full per-job observation is in `evidence/PR282_FINAL_WORKFLOW_HARVEST.json`. It reconciles the supplied exact-tree harvest with live final statuses and the newly read smoke/aggregate logs. It is not a claim that all 44 raw scientific logs of the additional replay were independently reread in this review.

### 1.1 What is now PROVED

On the merged tree, the following results have exact compiler/axiom support:

- An off-line zeta zero produces `Nonempty GeneratedGlobalFirstCrossing`.
- The global first-negative-boundary package retains a positive base, an exact zero, a nonnegative left prefix, and negative values arbitrarily close on the right.
- Responsible parity and selected cutoff are aligned at the same aperture. Global nonnegativity descends to the selected cutoff through existing N-antitonicity.
- A strict-even branch supplies its own nonzero normalized kernel vector; callers need not inject an unrelated vector.
- The strict-even source value is positive under its exact zero-ground/opposite-parity-positive hypotheses.
- The existing response and curvature algebra compile under their stated derivative-realization and balance assumptions.

The last statement is not a proof of those assumptions. Accepted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or placeholder is to be introduced.

### 1.2 What merging did not establish

Weighted derivative-test admissibility, actual compressed derivative realization through seams, the concrete production curvature identity, outgoing stationary zero-curvature necessity, arithmetic exclusion, odd/tie exclusion, and RH remain unproved at the start of this PR. The source itself records this separation. [S08–S10]

### 1.3 Workflow harvest and historical implications

| Workflow or family | Classification / exact disposition |
|---|---|
| Ordinary Lean and closure compiler jobs | FORMAL VALIDITY GATE: the scoped existing statements compile and their audits pass; no open premise is discharged merely by compilation. |
| RHKG compiler/materializer | Formal/evidence integration: exact registered bindings and derived-state generation passed; navigation does not add theorem authority. |
| Main Python and Control-v2 | REGRESSION GATE: 236 control tests and final smoke passed; historical routing, #117 control semantics, and `RH_OPEN` preserved. |
| Generated-contact campaign | RESEARCH-PRODUCING CHECK: 4,800 canonical state rows, 14,400 total model rows, 899 floating canonical brackets, 11 selected cases. Arb replay selected four brackets and seven probes; zero certified sign brackets and zero first boundaries. |
| Post-280 saturation | REGRESSION: 33 canonical Q comparisons, 27 resolved, six unresolved, zero resolved mismatches; 66 planted controls; 27 exact source checks. |
| Post-279 quotient | `LIFTED_RELATION_SPACE_MATERIALIZED__POINTWISE_CANONICAL_EQUALITY_RIGIDITY_OPEN`; rank 5/nullity 5 in its stated relation class. |
| Post268 original and extra replay | REGRESSION / execution harvest: 44 checks accounted for. Green preserves their individual scientific dispositions. |
| Post-190 realizability | `EXACT_TWIN_SURVIVES`; later general layers unresolved; finite H1 panel only. |
| Post-192 trajectory | `TRAJECTORY_RIGIDITY_UNRESOLVED`. |
| Post-194 sharp enclosure | `PARTIAL_TRAJECTORY_ORIENTATION`; 63/64 in frozen scope. |
| Post-196 residual cell | `GLOBAL_MONOTONE_ORIENTATION` only on the covered frozen scope, not all-aperture monotonicity. |
| Post-198 / post-200 | Source/discrepancy decomposition dependency remains unresolved. |
| Post-202 composite parity gap | `COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`. |
| Post-214 dual geometry | `FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED`; full-space sign indefiniteness preserved. |
| Post-222 bi-regular scalar | `NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED`. |
| Permansson | Unrelated formal result and axiom/placeholder checks preserved; no RH authority transferred. |

Earlier frozen dispositions are not repeated as new discoveries. The new generated global state provides stronger local hypotheses for future arguments; it does not invalidate the old countermodels or widen their empirical scope.

## 2. Corrections from the adversarial plan review

### C01 — Do not try to prove a false universal legacy realization statement

The old `productionApertureFirstMatrix` differentiates ambient entries before compression. A raw seam kink may vanish after legal compression, so totalized raw derivatives need not give the derivative of the legal family. The old scalar fixed-energy derivative is already defined on the right object and can be retained. [S09]

Create compressed-first derivative operators and a new optimized-curvature name. Do not silently change the meaning of an old named definition and then reuse an old proof receipt as though it certified the new object. Interior compatibility is a theorem; universal seam compatibility with the old candidate is not a required target.

### C02 — Pointwise twice differentiable is not the required local C2 family

The new primary regularity result is `ContDiffOn` on `Ioi 0`, or equivalent `ContDiffOn` on an explicit positive neighborhood of every aperture, for the operator-valued legal family. First and second derivative values alone do not provide the continuity of jets needed by the local Schur argument.

The independent variable is real aperture L. The target is a complex-linear endomorphism space regarded as a real normed space. No complex differentiability of the piecewise production family across seams is claimed.

### C03 — The #280 arbitrary-functional theorem is not a production linearity theorem

`optimizedCurvatureLinearFunctional_eq_remainder_sub_source` accepts a linear map on all real functions. The singular production integral does not provide such an unrestricted map. [S11]

Use the existing pointwise identity plus add/subtract/scalar lemmas with actual integrability hypotheses, or use a linear map on a proved admissible submodule. Do not obtain the desired bridge by passing an invented universal functional.

### C04 — Weighted tests are not automatically mixed dictionary tests

The existing complete-physical-RHS theorem has a specific mixed-dictionary domain and zero-centered hypothesis. Polynomially weighted source derivatives must receive their own proof of physical authority. A single existing quadratic-normal instance cannot be transported by name alone.

Use the existing pole/prime/archimedean normalization and general Fourier/physical lemmas where applicable, proving the additional finite-span regularity and integrability obligations. Existing physical-coordinate C2 gluing is a reusable pattern, not a ready-made theorem about aperture seams. [S12]

### C05 — Prove the corrected arithmetic identity before assuming a response

The useful stronger target is a pair identity for arbitrary fixed legal even z,w. Define

\[
B_2(L,z,w)=\Re\langle z,E''(L)z\rangle+2\Re\langle z,E'(L)w\rangle.
\]

Prove

\[
\boxed{\Delta(L,z,w)=B_2(L,z,w)+2J_1(L,z)/L.}
\]

This target does not require an eigenvalue, ground status, perpendicular response, stationarity, or existence of a contact. It is a proposed strengthening supported by the source-transport algebra and chain rule; production differentiation/integrability still have to be proved. Only after w is the actual eigenbranch response is B2 called optimized curvature.

### C06 — Inherited restriction is not full derivative annihilation

Prove the vanishing of the first-variation restriction on the embedded predecessor kernel. Do not infer that E' maps that kernel to zero. It may couple into its complement, and that coupling supplies the response cost.

The required inclusion is L-independent and its energy compatibility holds in an aperture neighborhood, not only at L*. The existing centered zero extension and finite kernel tower supply the correct objects. [S13]

### C07 — Arbitrary complement dimension and native carrier instances

The generic Schur theorem must allow a finite-dimensional complement, not just a scalar 2x2 matrix. Preserve the existing native-even carrier conventions. For orthogonality, use the established kernel of the inner-product functional where this avoids known subtype/typeclass problems; do not replace it casually with a different `Submodule.orthogonal` instance stack.

The zero-dimensional complement is legitimate. It has w=0 and zero response cost; it is not an inverse-of-empty-spectrum failure.

### C08 — A near-contact sample is not an exact contact

At nonzero eigenvalue lambda, use E-lambda I and retain the eigenvalue subtraction in the spectral source comparison. The existing shifted intertwining theorem is an upstream input. [S14]

A nonzero near-contact transport defect does not falsify a law quantified only over exact generated contacts. A finite sign bracket is not the first global boundary. No-contact requires covered-domain evidence, not root non-detection.

### C09 — Pointwise residual tests are stronger than almost-everywhere propagation

The projected-dilation defect test follows from a pointwise PSD residual with finite coefficient at the stationary contact. It is not automatically a consequence of an almost-everywhere differential inequality with a merely locally integrable coefficient. Keep those hypotheses and their numerical applicability separate.

### C10 — Encode exact bounds, not rounded decimal displays

Use directed Arb endpoints and their exact mantissa/exponent representation. The old fixed-digit decimal strings cannot be an exact reconstruction interface. Harden strict integer parsing, reject Booleans, and avoid converting exact identifiers or interval numerators through float. The shared codec remains the single format implementation. [S15,S20]

### C11 — Version the old completion gate, rather than deleting its firewall

The current build checker hard-codes #281/#282 current state and refuses promotion of some obligations this PR intends to discharge. Preserve the historical record, introduce a current successor ledger, and tie new discharge to exact theorem bindings. Do not change the old failure into a pass by removing an inconvenient check. [S16]

### C12 — Do not make arithmetic discovery a fake theorem deliverable

No numerical positive result is an admission criterion for RH. A candidate arithmetic inequality can be rejected and the research job still pass, if the rejection is correct and preserved. Core completion still requires actual production calculus, not a blanket of unresolved interfaces.

## 3. Mathematical notation and fixed objects

Let p be a reversal parity and K a fixed finite Fourier cutoff. Use the repository's existing complex Euclidean legal parity space V(p,K), its inclusion iota into the ambient centered-coordinate space, and its orthogonal projection P. Neither inclusion nor projection depends on L.

\[
E_{p,K}(L)=P_{p,K}\,\texttt{canonicalSourceMatrix}(L,K)\,\iota_{p,K}.
\]

This is the existing compressed canonical operator, represented as a continuous complex-linear map. No new matrix normalization, basis norm, or sign convention is introduced.

For generated strict-even c:

- L* is `c.generated.shell.Lstar`;
- K is `c.generated.shell.k + 1`;
- n is the least zero successor index;
- k is the least outgoing-negative successor index;
- N is the terminal witness index, with 1 <= n <= k <= N;
- z is the existing normalized nonzero even kernel vector;
- E_even(L*) is PSD with one-dimensional kernel, and the odd bottom is strictly positive.

Use `cutoff_Q` in machine records for floor(exp L), and `source_Q` for the scalar source value. Do not use one unqualified JSON key Q for both.

Write a=2*pi and retain

\[
\mathcal Q(L,z)=\texttt{productionStrictEvenSourceValue}(L,K,z).
\]

This is the existing real part of the conjugate source functional multiplied by the fourth moment, not a new nonnegative square. Its strict positivity theorem has exact contact hypotheses. [S10]

The actual aperture derivatives will be denoted E1 and E2. The names below are proposed API names, not assertions that declarations already exist:

- `canonicalParityApertureFirst` and `canonicalParityApertureSecond`;
- `canonicalEvenApertureFirst` and `canonicalEvenApertureSecond` as native-even adapters;
- `canonicalStationaryEvenResponse`;
- `canonicalContactSecondPairing`;
- `canonicalOptimizedContactCurvature`.

Reuse the current scalar `productionContactFixedEnergy`, `productionContactFirstVariation`, and `productionContactFixedSecondVariation` and prove their compatibility with the actual derivatives. Their existing mathematical meanings need not change.

## 4. Formal work packages and acceptance statements

### F01 — Compressed operator regularity

**New file:** `Zeta23/CCM/CanonicalCompressedApertureC2.lean`.

Inputs: existing frozen complete canonical family, canonical value-gluing, parity compression, source derivative transport and endpoint cancellations. No RH, contact, simplicity, or positivity premise.

Build:

1. A continuous-linear-map form of the existing legal compression; prove pointwise agreement with `parityCompressedCanonical`.
2. Real-aperture differentiability of the frozen compressed family and its first two jets.
3. Matching compressed value, first jet and second jet for the Q=q-1 and Q=q frozen continuations at L=log q, q>=2.
4. The real production family is locally equal to the appropriate frozen family on each side. Glue the operator-valued jets across every positive integer threshold.
5. A genuine `ContDiffOn R 2` result on positive aperture. The C2 theorem can allow all K, including trivial carriers; ground/contact consumers require K>=2.
6. Actual first/second derivative operators and `HasDerivAt` witnesses, Hermitian symmetry, and quadratic/mixed scalar derivative identities.
7. An explicit native-even isometric identification with the generic even-parity carrier, so the response code does not rely on accidental definitional agreement of instances.

At a true prime-power seam, the canonical update has the minus-prime sign. Derive vanishing of the first two compressed jets from source-coordinate cancellation and the chain rule; use polarization to pass from quadratic forms to the whole operator. At a zero-von-Mangoldt threshold the entering term is identically zero. Neither case authorizes a ninth-order background barrier or all-aperture positivity.

**Acceptance:** the final regularity statement has only the production carrier, fixed finite K, and positive aperture assumptions. It does not accept a continuity/derivative/realization proposition as an input.

### F02 — Weighted physical-test calculus

**New file:** `Zeta23/CCM/ProductionWeightedTestCalculus.lean`.  
**Modify:** `FirstCrossingProductionTests.lean`.

Define an analytic admissibility object for the actual physical test span. It must contain verifiable regularity/support/integrability properties, not the desired curvature equality as a field.

For L>0 and legal even z,w, omega=1-t/L, prove admissibility for:

\[
\begin{aligned}
k_N(t)&=\Re(\overline{M_4(z)}H_z(\omega)),\\
k_1(t)&=t\,e'_z(\omega)/L^2,\\
k_2(t)&=t^2 e''_z(\omega)/L^4,\\
k_D(t)&=t^2e_{Dz}(\omega)/L^4,\\
k_M(t)&=t\,\Re(e'_{z,w}(\omega))/L^2.
\end{aligned}
\]

The source and mixed derivatives are with respect to omega. The operator derivatives E1,E2 are with respect to L.

For each required test, establish:

- its positive-half physical meaning and an explicit even compact extension to the whole line;
- enough endpoint jets to make the global extension C2;
- pole and archimedean integrability under the exact production weights;
- finite prime-sample identity at the actual cutoff;
- the correctly normalized literature-RHS/physical-RHS equality;
- complex conjugation/real-part compatibility;
- addition, subtraction, and real scaling on the admitted span.

At t=0 the singular archimedean density behaves like a constant times 1/t; the admitted weighted tests have at least quadratic vanishing. At t=L the entering-coordinate endpoint is omega=0 and the existing high-order jets imply the lower-order support gluing needed here. These are different endpoints and different obligations.

The unweighted mixed energy need not vanish at physical zero. Do not split it into separately divergent integrals. Use its existing regularized dictionary expression. The physical functional is linear on the admitted span because the component integrals are integrable, not because Lean defines an integral for every function.

For differentiation, provide a locally uniform dominating function on a neighborhood of the aperture and a common physical support bound, or an exact finite analytic primitive proof with equivalent domain control. C2 compact support at one parameter is not a substitute.

**Acceptance:** construct the existing admissibility/physical-authority instances for all tests actually used; no caller-provided `ProductionPhysicalTestAuthority` remains in the production derivative/bridge endpoint.

### F03 — Concrete remainder, phase, and source normalization

**Modify:** `FirstCrossingProductionRemainder.lean`.

Retain the existing concrete remainder source. Prove the exact simplification

\[
R_{L,z,w}(t)=\frac{a^2}{L^2}k_N(t)-\frac{a^2t^2}{L^4}e_{Dz}(1-t/L)
+\frac{2t}{L^2}\Re(e'_{z,w}(1-t/L)).
\]

The current tangential definition is e_Dz minus the normal channel; no separate arbitrary remainder is accepted. This identity is exact algebra and is one of the finite review checks.

Prove:

- the assembled remainder is admitted by F02;
- production evaluation of the normal channel equals the existing source scalar Q, with complex conjugation intact;
- simultaneous unit-phase rotation `(z,w) -> (u*z,u*w)` leaves Q, R, J1 and all scalar balances invariant;
- the chosen response is phase-covariant, using uniqueness in F05.

Intrinsic identification of the tangential channel with a legal projected D*D vector can be added if useful, but is not a prerequisite for this minimal identity. Do not make the main proof depend on unproved legality of an unprojected D^2 z.

**Acceptance:** R remains the original concrete production function, with proved authority and no extra arbitrary source parameter.

### F04 — Actual derivative identities and the general pair balance

**Modify:** `FirstCrossingProductionFirstVariation.lean`, with the pair-balance assembly in `FirstCrossingProductionCurvatureBridge.lean`.

Prove from the complete regularized production energy:

\[
J_1(L,z)=\Re\langle z,E_1(L)z\rangle=\mathcal A_L[k_1],
\]

\[
J_{2,\mathrm{fixed}}(L,z)+2J_1(L,z)/L=\mathcal A_L[k_2],
\]

and the actual mixed first-variation formula

\[
\Re\langle z,E_1(L)w\rangle=\mathcal A_L[k_M].
\]

Retain all pole, scalar archimedean drift, and prime normalization contributions. Do not differentiate a cutoff staircase as though it were a smooth real function.

Define the pair second-order quantity

\[
B_2(L,z,w)=J_{2,\mathrm{fixed}}(L,z)+2\Re\langle z,E_1(L)w\rangle.
\]

Use the genuine source transport e''_z=-a^2 e_Dz and admitted-span linearity to prove

\[
\boxed{\texttt{productionContactSaturationGap}(L,K,z,w)
=B_2(L,z,w)+2J_1(L,z)/L.}
\]

This statement is for fixed legal even z,w and L>0, K>=2. It has no contact, eigenmode, perpendicularity or response premise. This is the proposed upstream compression of the previous plan; if a hidden normalization prevents this generality, record the exact obstruction and correct the theorem contract openly rather than assume the identity.

**Acceptance:** source/Q identification is proved from F02–F03; the RHS is not used to define E1/E2 or B2.

### F05 — Unique actual response and generic stationary contact theorem

**Modify:** `FirstCrossingProductionResponse.lean`.  
**New file:** `Zeta23/CCM/StationarySchurContact.lean`.

First prove the native-even response theorem using the actual E1. Inputs are L>0, K>=2, a unit nonzero even kernel vector, strict odd positivity, and J1=0. No legacy operator-realization hypothesis is required: F01 supplies actual derivative meaning.

Use the existing kernel-line theorem and the range/kernel method already successful in the repository. A convenient complement is the kernel of `inner_sl C z`; preserve the native instance stack. Solve E w=-E1 z, then use normalization to impose inner(z,w)=0. Prove uniqueness, response equation, orthogonality and phase covariance. For complement dimension zero, w=0.

For a generic finite-dimensional self-adjoint C2 family F(s), a normalized zero mode z, and PSD F(0) with kernel span(z), prove:

1. The restriction C(s) to z-perp is positive definite on some neighborhood of zero. Its positivity is a consequence of PSD plus the simple kernel, not an extra assumption on a larger ambient space.
2. The exact Schur scalar sigma(s)=a(s)-b(s)^*C(s)^(-1)b(s) exists there and controls the inertia relative to the positive complement.
3. sigma(0)=0; sigma'(0)=J1; sigma''(0)=B2(z,w), where w is the stationary perpendicular response.
4. If the family is nonnegative on a left neighborhood and negative in some direction arbitrarily close on the right, and J1=0, then sigma''(0)=0.

The last step follows from the signed quadratic Taylor term: a negative second derivative violates left nonnegativity; a positive second derivative gives a positive right neighborhood. Use the local C2 theorem, not a presumed moving eigenvector.

The generic theorem must handle arbitrary finite complement dimension and the zero-dimensional case. Existing real/Hermitian 2x2 Schur calculus can support a reduction, but cannot stand in for the general theorem. No new complete spectral perturbation library is required.

**Acceptance:** the production specialization proves actual optimized curvature zero from generated geometry and stationarity; `hkappa` is not an input.

### F06 — Inherited-kernel stationarity

**New file:** `Zeta23/CCM/FirstCrossingInheritedStationarity.lean`.

Work first for either selected parity. At the predecessor cutoff k, take its contact kernel and embed it into the selected successor cutoff k+1 through the existing centered zero extension. Denote this embedded subspace U.

Prove energy compatibility for fixed vectors under this inclusion throughout a positive neighborhood of L*, using the existing L-independent centered extension. At an inherited contact n<k:

- the predecessor is nonnegative to the left by generated-prefix descent;
- it is nonnegative on a right neighborhood by least-outgoing-index stability;
- its contact kernel has zero energy at L*.

Therefore the derivative quadratic form vanishes on U. Polarization yields

\[
\boxed{P_U E_1(L_*)\iota_U=0.}
\]

Do not strengthen this to E1 iota_U=0; the latter is false even in small exact crossing controls.

For strict-even generated contacts, prove the selected normalized kernel belongs to U using the inherited seed/tower and strict simplicity. Then J1(z)=0. This implication covers n<k, not fresh-born k=n. It uses no tower past N and works for k=N. The k=1 edge cannot be inherited since n>=1.

**Acceptance:** inherited stationarity is a theorem about existing generated objects. No `z_is_inherited` premise is added to the final strict-even theorem unless separately constructed from the original state.

### F07 — Completed frontier and exact premise contract

**Modify:** `FirstCrossingProductionCurvatureBridge.lean`, `FirstCrossingGeneratedStrictEvenFrontier.lean`.  
**New file:** `Zeta23/RHRC/ContactCalculusContract.lean`.

Define `canonicalOptimizedContactCurvature` from actual derivatives and the actual response, independently of the arithmetic gap. Retain legacy curvature definitions under their old meanings. Prove interior compatibility where their operators agree.

The main proposed endpoint, stated mathematically rather than as a claim of compiling Lean syntax, is:

\[
\begin{aligned}
c:\texttt{GeneratedStrictEvenContact}\quad\Longrightarrow\quad
&(k=n\ \wedge\ J_1<0)\\
&\quad\lor\\
&\bigl(J_1=0\ \wedge\ \exists w:\ \text{unique perpendicular response }Ew=-E_1z,\\
&\qquad\kappa_{\mathrm{actual}}=0,\quad
\mathcal A_{L_*}[R_{L_*,z,w}]=a^2\mathcal Q(L_*,z)/L_*^2>0\bigr).
\end{aligned}
\]

A separate inherited theorem takes only c and n<k and proves the second branch. The stationary theorem may take J1=0 as a legitimate branch condition; the inherited theorem may not.

Suggested exports:

- `GeneratedStrictEvenContact.firstVariation_nonpos_production`;
- `GeneratedStrictEvenContact.firstVariation_eq_zero_of_inherited`;
- `GeneratedStrictEvenContact.actual_stationary_curvature_eq_zero`;
- `canonicalSecondPairing_euler_eq_productionSaturationGap`;
- `GeneratedStrictEvenContact.production_stationary_saturation`;
- `GeneratedStrictEvenContact.production_frontier`;
- `GeneratedStrictEvenContact.inherited_production_saturation`.

Freeze allowed types in the contract module with explicit applications supplying only existing contact data and the allowed branch premise. Check transitive bundled premises as well as visible binders. Existing global/shell/strict-even contact constructor fields must not gain realization, balance, or exclusion assumptions.

For the new completed endpoints, forbidden supplied premises include legacy C2 realization, an actual-curvature/arithmetic identity, a zero-curvature equality, arbitrary R, arbitrary kappa, a source-Q equality, an endpoint barrier, RH, or an RH-equivalent positivity hypothesis. Standard typeclass data and the original generated contact fields are permitted. The proof may use generic conditional lemmas internally only after discharging their analytic premises from production theorems.

**Acceptance:** theorem types and definitions, not only declaration names or grep tokens, establish completion. A direct equality with the new actual curvature replaces the old seam-unsafe bridge as the current contract; the old proposition is not falsely labelled universally discharged.

## 5. Numerical certification and evidence contract

### N01 — Exact interval reconstruction

Modify the shared `research/RHRC/closure_batch/interval_codec.py` and its existing tests. Add an Arb adapter rather than a second interval format.

For a finite Arb ball B, call its directed `lower()` and `upper()`, then extract each exact endpoint's integer mantissa and binary exponent with `man_exp()`. Normalize those exact dyadics into the existing common-denominator representation, or use a versioned exact endpoint representation with one canonical decoder. The transport must never pass through a fixed-digit decimal display. Official python-flint documentation supports these endpoint/extraction operations, but implementation must run against the repository-pinned python-flint version. [S20]

Harden the decoder: require actual integral JSON values or explicitly validated canonical integer strings; reject Boolean values, fractional numbers, nonfinite values, inverted intervals, invalid exponents, excess resource sizes, and ambiguous field sets. Preserve support for old legitimate exact interval records. Optional Arb support must not make the lightweight RHRC framework import the numerical dependency unexpectedly.

Required invariant:

\[
\operatorname{decode}(\operatorname{encode}(B))\supseteq B.
\]

Validate both original-ball containment and independent exact-rational endpoint decoding. Test tiny radii near order-one midpoints, very small and large magnitudes, negative and sign-straddling balls, exact zero, precision changes, and corrupted schemas. Outward widening is allowed and must be reflected in sign resolution. Display decimals are explicitly non-authoritative.

Old artifacts are not rewritten. Their recorded internal Arb signs and their lossy decimal endpoints remain separate historical facts.

### N02 — Frozen independent calibration and controls

The initial panel consists of:

1. The exact #282 selected-neighborhood list from artifact `11282789337`, run `37149698793`, tied to head de2869 and the original protocol digest. Copy exact integer-cell/rational-fraction coordinates from that artifact. Do not reconstruct them from the floating L values in an audit summary.
2. K=2 at L=log 2, with unit even vector `(1,-4,6,-4,1)/sqrt(70)`; exact legal norm and moment constraints checked independently.
3. One-sided seam comparisons at q in {2,4,8,9,16} and zero-weight controls q in {6,10,14,15}; use K in {2,3} and declared rational/logarithmic offsets, not floating floor guesses at a seam.
4. Existing exact generic and actual-carrier crossing controls, including higher odd contact orders, quartic touch, transverse and reflected-odd crossings, ties, and zero-dimensional complement.

Source artifact ZIP digest: `67a8dc2e766e2c7ea6ec02809ade4e4d530b055be382901637368e4cf9711e39`. Original discovery JSON digest: `9cd30f99a1841e5ef70951f1339ff18b9b9492e5273659bb560fb5e457aedd0a`. Original Arb JSON digest: `e137b8db0c726085c1fc9875efa778ff115de705c26fd1205154133541baea29`. Original protocol digest: `f02fcb60ac8ba0138282ac3874c28d02d32e28b3935a11070f75c7157bc6c7e5`. These are provenance constraints, not substitutes for reading the artifact.

The K=2/log2 calibration must independently certify positive energy and negative actual first variation, with matching compressed left/right derivatives. Its formerly reported decimal derivative is a diagnostic comparison value, not a hard-coded input or a claimed new certificate. It is an ordinary positive-energy state, not a generated zero contact.

The proposed default precision ladder is 192, 384, 768 bits. For the nondegenerate K=2 calibration, require independently computed derivative/remainder/balance enclosures of absolute width at most 2^-80 and the stated energy/first-variation signs. This is a proposed qualification threshold, not a previously achieved result. Near-contact cases may remain unresolved under a separate bounded budget.

Retain all 11 selected cases and their selection reasons even if point coordinates repeat; cache duplicate exact evaluations but preserve case identity. Four selected brackets are not all 899 floating brackets. A broader replay of the remaining brackets is optional and must have a separate coverage/selection record.

### N03 — Validated response and independent arithmetic evaluation

Add `canonical_contact_balance_arb.py`. It must provide separate status and error budgets for:

- both parity eigenvalue enclosures and selected-sector isolation;
- normalized eigenvector/projector error;
- actual first and second compressed jets;
- source scalar Q from arithmetic and correctly shifted spectral representations;
- perpendicular response;
- independently evaluated physical remainder;
- optimized curvature, Euler-corrected saturation gap, and eligible ratio.

Away from an exact zero eigenvalue, response satisfies

\[
(E-\lambda I)w=-(E_1-\lambda'I)z,\qquad z^*w=0.
\]

A validated bordered system is an acceptable implementation:

\[
\begin{pmatrix}E-\lambda I&z\\z^*&0\end{pmatrix}
\begin{pmatrix}w\\\eta\end{pmatrix}
=\begin{pmatrix}-E_1z\\0\end{pmatrix}.
\]

The certificate must enclose the response of the actual isolated eigenpair, not only solve a midpoint system. Use a validated inverse/Krawczyk-style bound or an equivalent proved residual-and-conditioning estimate, propagating eigenvalue and vector errors. A tiny residual without a conditioning bound is insufficient. If the relevant gap includes zero, return an explicit unresolved or multiple-kernel status rather than divide by it.

For arithmetic evaluation use the concrete weighted tests and exact physical weights, with certified endpoint treatment and quadrature/tail or analytic-primitive errors. Derive any acceleration from those formulas; do not define the remainder by rearranging the curvature identity. Compare independently obtained intervals for

\[
\Delta_{\mathrm{sat}}\quad\text{and}\quad\kappa+2J_1/L.
\]

The nonzero-eigenvalue spectral Q check must retain the eigenvalue subtraction. Prove its exact source normalization as a specialization of the shifted intertwining identity before treating it as an expected identity. [S14]

If Q is certified strictly positive and numerator/denominator are separately enclosed, report rho=L^2 A[R]/(a^2 Q). If Q is unresolved, report unresolved eligibility. If Q is certified nonpositive on an ordinary sample, the strict-contact ratio is ineligible; this is not a contradiction of the contact-only positivity theorem.

There must be at least one nondegenerate canonical calibration with independently certified response/curvature/remainder comparisons. Implementing only status stubs that return unresolved everywhere does not qualify N03. Individual difficult panel rows may remain unresolved after the frozen budget, and their counts must be reported honestly.

### N04 — Matched ablations and adversarial certificates

Preserve frozen-state and reoptimized ablations as distinct quantities. The same L,K,z,w are held fixed only in the former; the latter recomputes the isolated eigenstate and response of the modified operator.

All channel attributions use the inverse/response of the complete model. Do not replace it by a sum of channel-wise inverse responses. For planted tests, change the matrix, jets, and arithmetic functional consistently. If no matched arithmetic functional is constructed, label the arithmetic comparison NOT_APPLICABLE; do not apply canonical theorem authority to the planted object.

Negative-control tests must reject: fake contact flags, duplicated or missing selected cases, wrong source tree, corrupted protocol hash, ambiguous cutoff/source Q, reversed/inexact cell coordinates, fake enclosing endpoints, an uncertified inverse, unnormalized vectors, source/response gauge mismatch, omitted Euler correction, omitted spectral eigenvalue subtraction, and empty successful payloads. Run guard tests under normal Python and `python -O`.

### 5.1 Proposed research files

Under `research/RHRC/routes/R003_ccm_bridge/`, add:

- `canonical_contact_balance_arb.py`;
- `post282_contact_calculus.py`;
- `check_post282_contact_calculus_contract.py`;
- `write_post282_contact_calculus_receipt.py`;
- `fixtures/post282_contact_calculus_v1.json`;
- `tests/test_post282_contact_calculus.py`.

Modify the existing `canonical_contact_frontier_arb.py`, `check_post281_generated_contact_results.py`, and their tests only for explicit compatible codec/validation improvements. Preserve old protocol meaning and version the new output schema.

Receipts contain checkout/head/base/tree identities, source-file hashes including transitive numerical evaluators, dependency versions, exact protocol and output hashes, dirty-tree status, case/coverage identities, quantity-specific resolutions, and `RH_OPEN`. Hash every actual input; do not rely on an assumed graph edge or a nearby green head.

## 6. Bounded research producing genuinely new arithmetic information

These activities run alongside the proof work but are not assumed successful arithmetic theorems.

### X01 — Inherited response balance

Use the exact predecessor/selected-shell geometry and the matched full-model response to investigate the historical predecessor-curvature versus shell-response/Gamma-derivative balance. The historical formula is a lead requiring its own normalization proof; it is not a compiled identity to impose on data.

The question is whether a canonical source property forces a strict inequality or a degeneracy incompatible with the necessary saturation equality. Generic positivity or Cauchy-Schwarz is insufficient because the archived exact finite-carrier controls attain saturation with nonzero source and fourth moment. Any candidate must state the additional arithmetic hypothesis, the exact contact regime, and an adversarial control that does not satisfy it.

A successful experiment may reject a plausible law. Preserve the rejection. Do not retune the witness, protocol or preferred gap after observing the result.

### X02 — Explicit projected-dilation residual

On a declared fixed legal carrier, retain the energy-independent generator

\[
T_K=P_KH_KP_K,\qquad
(H_K)_{nm}=\begin{cases}1/2&n=m,\\m/(m-n)&n\ne m.\end{cases}
\]

The elementary identity H+H*=11* and legal zero-sum constraint imply T*=-T. The exact finite review checks confirm this algebra for K=2,3,4,6; they do not prove a canonical energy inequality.

Evaluate source-derived candidate residuals

\[
\mathcal R_a(L)=L E'_K(L)+[E_K(L),T_K]+a_K(L)E_K(L).
\]

A PSD residual with an admissible locally integrable a_K/L on a right neighborhood of every generated boundary would propagate contact nonnegativity and contradict the retained right-negative sequence. Formalizing that generic implication does not supply the canonical inequality.

No coefficient fitted through division by the unknown ground energy is promoted to a source-derived certificate. Check integrability through the contact. The constants may depend on the fixed finite state; uniformity in all K is not needed merely to contradict that state.

For the stronger pointwise finite-coefficient certificate at a stationary simple contact, PSD plus zero quadratic value on z implies

\[
\mathcal R_a(L_*)z=E(L_*)\bigl(T_Kz-L_*w\bigr)=0,
\qquad
P_{z^\perp}T_Kz=L_*w.
\]

The transport defect is a necessary test only under those stronger hypotheses. An ordinary near-contact value does not decide an exact-contact statement. Failure of a full-matrix residual does not automatically defeat a weaker ground-only relative inequality.

### 6.1 Discovery scope and dispositions

Initially reuse the frozen calibration/selected panel. Permit at most 12 additional neighborhoods selected before saturation-gap or rho inspection, using the old allowed features: independent sign brackets, magnitude, parity separation, sector gap, and dimension diversity. Freeze hypotheses and candidate coefficients before confirmatory replay.

Proposed bounds are 192/384/768 bits, at most 96 refinement steps per neighborhood, and an explicitly recorded per-job timeout. These are resource limits, not absence certificates. The outcome vocabulary distinguishes implementation error, scientific falsification, bounded survival, unresolved resolution, ineligible branch, missing matched model, and insufficient coverage.

X01/X02 must never block core theorem acceptance solely because an arithmetic candidate is false. They do block release if the evidence runner incorrectly labels a false or unresolved result as certified.

## 7. File inventory and dependency wiring

### 7.1 Seven new Lean modules

| Path | Role |
|---|---|
| `Zeta23/CCM/CanonicalCompressedSeamJets.lean` | F01 exact entering-atom value/first/second legal seam jets. |
| `Zeta23/CCM/CanonicalFrozenApertureC2.lean` | F01 frozen analytic C2 and left/right seam continuation identities. |
| `Zeta23/CCM/CanonicalCompressedApertureC2.lean` | F01 compressed real-aperture C2 family and actual derivatives. |
| `Zeta23/CCM/ProductionWeightedTestCalculus.lean` | F02 admissible-span physical calculus. |
| `Zeta23/CCM/StationarySchurContact.lean` | F05 generic arbitrary-complement stationary contact theorem. |
| `Zeta23/CCM/FirstCrossingInheritedStationarity.lean` | F06 inherited-kernel first variation and strict-even specialization. |
| `Zeta23/RHRC/ContactCalculusContract.lean` | F07 exact endpoint-type and definition contract. |

F01 is split into the two explicit helper modules above; both are mandatory build/axiom/proof-escape targets. Further splitting requires an updated inventory and import audit. It must not change the mathematical scope or bypass the contract.

### 7.2 Six existing Lean modules changed

`FirstCrossingProductionTests.lean`, `FirstCrossingProductionRemainder.lean`, `FirstCrossingProductionFirstVariation.lean`, `FirstCrossingProductionResponse.lean`, `FirstCrossingProductionCurvatureBridge.lean`, and `FirstCrossingGeneratedStrictEvenFrontier.lean` under `Zeta23/CCM/`.

Keep the global-boundary and selected-shell constructors and fields unchanged. Additional transport lemmas may be placed in the new inherited module. Preserve legacy operator/curvature meanings and add explicit actual-object names and interior compatibility.

### 7.3 Import direction

```text
existing frozen canonical families + canonical continuity + legal source jets
                               |
                  CanonicalCompressedApertureC2
                               |
existing production RHS -> ProductionWeightedTestCalculus
                               |
             FirstCrossingProductionTests -> concrete Remainder
                               |
                  FirstCrossingProductionFirstVariation
                               |
                  FirstCrossingProductionResponse
                      /                         \
     FirstCrossingInheritedStationarity    StationarySchurContact (generic)
                      \                         /
                  FirstCrossingProductionCurvatureBridge
                               |
                  FirstCrossingGeneratedStrictEvenFrontier
                               |
                    RHRC.ContactCalculusContract
```

The generic Schur module does not import the frontier. The admissibility helper does not import its downstream test instances. The contract module is a consumer, never a production premise. New low-level modules do not import ExceptionalZero or conditional RH closure. Existing compiled finite-dictionary/explicit-formula infrastructure remains the source of normalization.

### 7.4 Shared framework and CI files changed

- `research/RHRC/closure_batch/interval_codec.py` and `test_interval_codec.py`;
- `research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_build.py` and scope/version tests;
- `research/RHRC/tools/run_suite.py`;
- `research/RHRC/closure_batch/check_lean_proof_escapes.py` and its tests;
- `research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json`;
- `.github/workflows/rhrc.yml`;
- `.github/workflows/rhrc_closure_campaign.yml`;
- `.github/workflows/rhrc_post281_generated_contact_frontier.yml` only where legacy/current gate separation requires it;
- new `.github/workflows/rhrc_post282_contact_calculus.yml`.

Keep the toolchain, mathlib lock and pinned numerical versions unchanged unless a separately explained compatibility defect forces a scoped change. No unrelated package upgrade belongs in the PR.

### 7.5 Control, claims and documentation

Add under the R003 route:

- `POST282_CONTACT_CALCULUS_BUILD_SPEC.md`;
- `POST282_CONTACT_CALCULUS_OBLIGATIONS.json`;
- `POST282_CONTACT_CALCULUS_PROTOCOL.md`;
- `POST282_MERGED_WORKFLOW_HARVEST.json`;
- `POST282_CONTACT_CALCULUS_POST_GREEN.md` after the exact final run, or an explicitly pending template before it.

Update `CONTROL_STATE.json` with merged theorem authority #282 and the new candidate. Preserve #117 Control-v2 semantic authority and independently frozen research anchors. Do not replace every historical PR number with the newest one.

Use `render_current_state.py` for the 14 managed blocks: root README/AUDIT/FORK_NOTES; RHRC CURRENT_RESEARCH_PLAN, DOCUMENTATION_AUTHORITY, FB05_INCOMPATIBILITY_PROGRAM, OBSTRUCTION_LEDGER, DEAD_ROUTES, README, RESEARCH_LEADS, VALIDATION_PROTOCOL; control_v2 README; R003 README; countermodels README.

Update applicable control/current-state tests without relaxing their semantic assertions. Update research prose outside managed blocks where scope has changed. Preserve the meaning of OBS-060N (production derivative/admissibility bridge), OBS-060O (saturation exclusion), and OBS-060J/K (interior/seam endpoint barriers). A corrected derivative contract replaces a legacy candidate gate; do not misdescribe that as proving a universally valid legacy equality.

Proposed new registered supporting claims are compressed production C2, weighted production pair balance, inherited first-variation restriction, and the completed strict-even frontier. Assign final IDs only after checking the live registry for collisions. Bind exact declarations via existing `R003_PROMOTED_BINDINGS.json`, `REGISTERED_THEOREM_BINDINGS.json`, `ClaimBindings.lean` and `RegisteredClaimBindings.lean`, and closure obligation bindings where relevant. Source theorem scope and legitimate contact premises must be recorded even if a registry status label uses the term unconditional for a theorem without extra axioms.

Do not register RH or arithmetic exclusion as proved. Generated graph/compiler products must be emitted by the existing transactional materializer, not hand-edited. Actual commit IDs belong in execution receipts; avoid making a checked-in file require its own final commit hash.

## 8. CI and theorem-admission gates

| Job | Gate type | Contract |
|---|---|---|
| `lean-compressed-calculus` | FORMAL VALIDITY GATE | Build F01–F04 roots and all relevant new targets; audit axioms and proof escapes. |
| `lean-contact-completion` | FORMAL VALIDITY GATE | Build F05–F07, exact allowed endpoint types, and all downstream consumers. |
| `research-calibration` | REGRESSION GATE | Codec reconstruction, seam calibration, adversarial controls, normal and optimized Python guards. |
| `arb-contact-balance` | RESEARCH-PRODUCING CHECK | Source-bound independent enclosures and explicit scientific dispositions. |
| `contact-calculus-complete` | Aggregate gate | All four required jobs succeeded; skipped or cancelled jobs do not count as success. |

Retain ordinary Lean, closure, registered-binding, anti-circularity, no-project-axiom, no-placeholder, source normalization, historical numerical, and graph checks. The new targets must be present in ordinary CI as well as the dedicated workflow.

Use an all-target build receipt: a first failing dependency must not prevent later requested targets from being attempted and reported. The job still exits nonzero if any mandatory target fails. Each target receipt records the exact tree and its disposition.

The exact contract module tests endpoint applications and expected source objects. A linter that only searches for the spelling `hbridge` cannot prevent a hidden equivalent premise in a record or typeclass. Audit immutable generated-contact constructor fields and transitive theorem assumptions; inspect definitions as well as theorem types.

Proposed timeouts: 90 minutes per Lean job and 60 minutes per bounded numerical job, revisited only with a documented operational reason. Timeout is an execution disposition, not scientific falsification or no-contact evidence.

## 9. Commit/build order

**Wave 0 — baseline and contracts.** Start from exact main 01871f7. Freeze merge/harvest observations and source manifests. Add versioned successor obligation and semantic migration maps. Draft expected theorem contracts; do not claim they compile yet. Preserve old source snapshots.

**Wave 1 — upstream correctness.** Implement actual compressed C2 and the shared exact codec. Prove the lower-order seam gluing and interior legacy compatibility. Run the exact kink-cancellation toy and independent K=2/log2 calibration.

**Wave 2 — production arithmetic.** Build weighted admissibility and allowed linearity, exact normal-source/Q identification, simplified remainder, complete derivative formulas, and the general Euler-corrected pair balance. Keep this wave independent of contact existence.

**Wave 3 — contact completion.** Build arbitrary-complement Schur necessity, actual response, inherited first variation and phase covariance. Assemble the completed strict-even frontier and enforce the exact premise contract.

**Wave 4 — certified research and integration.** Complete response/remainder enclosures, frozen ablations and bounded arithmetic hypotheses. Wire all registries, ordinary/dedicated workflows, managed docs and generated graph products. Scientific rejection remains a permitted result.

**Wave 5 — final validation and post-green research.** Re-anchor exact head/tested/merge trees; read every attached job; compare each disposition against the base; record theorem/definition changes and investigate any changed scientific result before claiming completion.

Do not label Wave 1 alone as fulfilling the full spec. A scoped partial PR is possible only through an explicit revision of scope and acceptance, not by changing missing mathematical work to optional after the run.

## 10. Explicit acceptance and rejection criteria

### Mandatory formal acceptance

- F01 actual local C2, not supplied realization.
- F02 actual admitted weighted span and production authority.
- F03 concrete R and Q normalization/phase compatibility.
- F04 independently proved corrected pair balance, with Euler term.
- F05 actual unique response plus generic and production stationary zero-curvature necessity.
- F06 inherited first-variation restriction and strict-even stationarity.
- F07 completed generated strict-even alternative without supplied analytic balance/zero-curvature premises.
- Exact contract types, accepted axiom footprint, no proof escapes, unchanged input geometry, and successful downstream build.

### Mandatory evidence acceptance

- Exact dyadic endpoint round trips and strict malformed-input rejection.
- Independent seam calibration, including actual production evaluation rather than recycled identity RHS.
- A nonvacuous canonical response/remainder qualification case and honest per-quantity resolution on the bounded panel.
- Preserved higher-odd crossing and actual-carrier countermodels.
- Frozen candidate selection, same-model arithmetic, source hashes, full coverage accounting, and unchanged `RH_OPEN` unless actual RH closure gates pass.

### Release rejection conditions

Reject any implementation that obtains green by inserting axioms, weakening the production object, assuming the desired bridge in a new structure, redefining curvature as the arithmetic gap, using unrestricted singular-functional linearity, silently reusing legacy seam derivatives, interpreting float root non-detection as exclusion, or promoting a synthetic model's result to canonical zeta authority.

Reject a claim that inherited stationarity annihilates all cross-coupling, that a positive fixed-vector curvature excludes a zero optimized curvature crossing, that source nonvanishing alone excludes saturation, or that a finite kernel tower continues beyond N.

## 11. Optional closure extension and remaining branches

The mandatory PR advances the strict-even contact frontier. It does not establish arithmetic saturation exclusion or a nonnegative right neighborhood.

To close RH in the same PR, an additional theorem must eliminate every generated crossing state. It must cover strict-even, strict-odd and ties/multiple kernels; fresh-born and inherited contacts; transverse and stationary/higher-order behavior; and interior and true/zero-weight seam cases.

A sufficient local endpoint is a canonical right-neighborhood PSD statement at every generated boundary. A suitable branch-complete relative-energy estimate is one possible mechanism. A strict-even stationary source-rigidity theorem is another useful result, but by itself is not branch-complete.

If a proof is obtained only for the new globally aligned state, do not apply it as though every older `CanonicalParityFirstCrossingShell` carried opposite-parity global information. Use an explicit transport theorem where valid, or a small terminal adapter quantified over `GeneratedGlobalFirstCrossing`. The adapter alone is not the research headline.

Only after the arithmetic exclusion is actually proved should the implementation add a literal premise-free Mathlib `RiemannHypothesis` declaration, check its exact type and zero-domain correspondence, audit its complete dependency closure, and update the terminal claim. No additional determinant-to-Xi limit is needed for this particular route, since off-line zero to finite generated obstruction is already available. Finite numerical agreement alone still cannot discharge it.

## 12. Post-green research interpretation

**What became formally true:** the new report must list the precise compiled equalities and implications, which old candidate definitions were retained, and which new actual derivative objects replace them in current use.

**Workflow harvest:** record every job, including historical replays; distinguish execution success from a falsified or unresolved research mechanism. The 899-bracket discovery population and the four selected replayed brackets must remain separate.

**What changed:** analytic bridge premises become proved production facts; inherited transverse strict-even crossing is eliminated; stationary strict-even crossing is reduced to an exact positive arithmetic balance.

**Upstream implications:** a general pair identity avoids unnecessary contact hypotheses; the admissible test span is smaller than an unrestricted functional domain; actual compressed regularity is reusable for both parities and future kernel-valued arguments.

**Downstream implications:** source-specific saturation exclusion can use a complete same-state theorem rather than re-proving calculus; nonstationary strict-even work can focus on fresh-born contacts; odd/tie work can reuse the new operator and inherited-kernel calculus.

**Resurrected routes:** contact-conditioned arithmetic bounds may be worth re-testing because the actual generated geometry is stronger than old generic dangerous panels. Unconditional drift-sign, generic null-jet and inverse-positivity shortcuts remain defeated for their old reasons.

**New RH-relevant clues:** seek a canonical arithmetic restriction not satisfied by the existing synthetic fixed-carrier countermodels, or a locally integrable relative-energy law. Treat the projected-dilation transport condition only as the scoped necessary test derived above.

**Falsification checks:** test normalization, scalar drift, seam matching, response conditioning, complex phase, finite tower endpoints, off-contact shifts, and whether a purported invariant is merely a restatement of the desired conclusion.

**Highest-leverage next moves:** complete actual calculus; narrow the inherited branch; certify the independently evaluated balance; then invest theorem effort only in arithmetic mechanisms that survive the countermodels. Green closes validation of the checked object, not the research investigation.

## 13. Review evidence and limitations

This specification was checked against the live merged PR, exact Git objects, final workflow statuses/logs, current source fragments and supplied detailed audit/handoff material. The older full handoff repository was used for dependency archaeology, not substituted for the live merged tree. Live source hashes are recorded for the key reviewed modules.

The review ran 18 exact finite algebra checks in SymPy: remainder simplification, pointwise source subtraction, Euler chain rule, five higher-odd stationary crossings, surviving inherited cross-coupling, the compression-before-derivative toy, projected-dilation skewness for four finite K, and four dyadic reconstruction arithmetic cases. See `review_checks/plan_sanity.py` and `evidence/PLAN_SANITY_RESULTS.json`.

These are finite algebra checks, not Lean proofs and not fresh canonical Arb certificates. No new local Lean build or production Arb replay was performed in this planning turn. Formal authority comes from the verified existing GitHub compiler/axiom evidence. Repository implementation is now checked into the candidate branch. Exact compiler and numerical workflow dispositions are intentionally deferred to CI; this document remains a build/acceptance contract rather than proof authority.

## 14. Source index

Full URLs and hashes are in `SOURCES.json`; repository files are pinned to merged main unless noted.

- [S01] Merged PR #282.
- [S02] Actual merge Git object.
- [S03] Main ref read during review.
- [S04] Frozen Lean toolchain — `lean-toolchain`.
- [S05] Main exact-head RHRC run.
- [S06] Final Control-v2 smoke job.
- [S07] Additional same-head 44-check replay.
- [S08] Current generated strict-even frontier — `Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean`.
- [S09] Current scalar/ambient-candidate derivative split — `Zeta23/CCM/FirstCrossingProductionFirstVariation.lean`.
- [S10] Actual physical functional and Q normalization — `Zeta23/CCM/FirstCrossingProductionArithmetic.lean`.
- [S11] Pointwise and arbitrary-functional algebra — `Zeta23/CCM/FirstCrossingOptimizedCurvatureAlgebra.lean`.
- [S12] Existing physical-coordinate residual C2 construction — `Zeta23/CCM/DictionaryResidualSecondOrderGluing.lean`.
- [S13] Existing centered extension and kernel tower — `Zeta23/CCM/ParityKernelTower.lean`.
- [S14] Shifted even-eigenmode intertwining — `Zeta23/CCM/GlobalParityBottomIntertwining.lean`.
- [S15] Shared exact interval codec — `research/RHRC/closure_batch/interval_codec.py`.
- [S16] Legacy build/current-state hardcoded gate — `research/RHRC/routes/R003_ccm_bridge/check_post281_generated_contact_build.py`.
- [S17] Existing source-coordinate endpoint jets — `Zeta23/CCM/CanonicalSourceEnergyJets.lean`.
- [S18] Existing canonical aperture C0 seam gluing — `Zeta23/CCM/CanonicalGroundContinuity.lean`.
- [S19] Original generated-contact run.
- [S20] Official python-flint Arb endpoint/extraction API.
- [S21] Official Mathlib one-dimensional higher differentiability API.
- [P01] BUILD_SPEC.md.
- [P02] RH_Frontier_Audit_2026-10-03(1).md.
- [P03] WORKFLOW_HARVEST(2).json.
- [P04] contact_evidence_analysis(1).json.
- [P05] RH_Research_Handoff_2026-10-01.zip.