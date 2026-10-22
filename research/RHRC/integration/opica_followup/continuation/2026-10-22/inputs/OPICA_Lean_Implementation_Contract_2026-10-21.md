# OPICA — Step 2 Repository Implementation Contract

**Prepared:** 21 October 2026. **Status:** specification for the next user-requested stage. No implementation, compiler run or repository change is claimed.

**Input paper:** `OPICA_Paper_Construction_v1_0_2026-10-21.md`. **Pinned source:** `97926d6a949fed7af0429a373b47abc772012834`; tree `3b8fb2b29f53247ad5143a603c047e160bddd37c`. Recheck live head before building and reconcile changes rather than silently replacing this pin.

**Mathematical firewall:** RH, A-X, B-Y, C-Schur and OPEN-J46 remain open. Generic implications may consume explicit premises; do not introduce a new axiom asserting a native upper.

# 12. Lean construction contract for the next message

## 12.1 No repository implementation in this step

No new `.lean` file, Git commit, branch, PR, CI workflow or registry promotion was created. Source snapshots in the evidence package are read-only copies of the existing repository and historical papers. The proposed module names below do not yet exist in the checked repository.

The next implementation should retain the pinned toolchain unless an explicitly reviewed migration is separately authorized. Current online Mathlib documentation confirms the relevant analytic/meromorphic order concepts, but it is not a promise that every current API name exists at the pinned revision. Existing project proofs already demonstrate usable `AnalyticAt`, `analyticOrderAt`, `analyticOrderAt_mul`, `analyticOrderAt_comp_of_deriv_ne_zero`, and iterated-derivative APIs. Pin-specific checks must precede implementation. [R2–R5; W1–W3]

## 12.2 Implement witnesses before building a large germ library

The paper uses germs for conceptual clarity. The minimal Lean implementation can avoid introducing a complete local-ring quotient library at the outset.

A `SimplePoleData`-style structure can contain:

- a center `lambda : Complex`;
- a nonzero residue `R : Complex`;
- an analytic remainder `h` at that center;
- equality of the proposed meromorphic expression with `R / (z-lambda) + h z` on a **punctured neighborhood**.

A `MultiplierOrderData`-style structure can contain:

- an order `k : Nat`;
- an analytic unit representative `u` with `u lambda != 0`;
- a genuine-neighborhood identity `M z = (z-lambda)^k * u z`.

For `k >= 1`, define the regular representative explicitly as

$$g(z)=(z-\lambda)^{k-1}u(z)[R+(z-\lambda)h(z)].$$

Prove its analyticity, derivative vanishing and leading derivative. Do not define it by arbitrary totalized division at the center and then assume that representative is analytic there.

For energy, use schedules and the finite real logarithmic inequality E1. A generic predicate `SubexpAlong T u` should mean the explicit limit in Section 5, with $T_n>0$ and $T_n\to\infty$ supplied where needed. It must not be a postulated property of the native prime field. The full-rate theorem is a separate hypothesis in generic comparison lemmas; a native J5.2/MS1 instantiation must retain its not-yet-formalized status until actually proved.

## 12.3 Proposed module and declaration map

All proposed modules live under `Zeta23/OPICA/`. Exact suggested declaration names are recorded in the separate implementation contract and theorem ledger.

| Module basename | Paper content | Public interface family |
|---|---|---|
| `LocalObstruction` | L1–L3 | Unit residues, completed jets, residual congruence and repeated completions |
| `AffineTransport` | L4 | Exact correction ledger, total order and raw-cancellation fixture |
| `EnergyRate` | E1–E3 | Log comparison, subexponential errors and tempered scales |
| `Composition` | E4–E5, C1–C2 | Accumulated budget, quotient faithfulness and cofinal-rate consumer |
| `ObservationCompatibility` | O1–O4 | Recovery criterion, left-null certificates and exact counterexamples |
| `NativeJetAdapter` | Existing native jets | Source-bound actual-input/kernel adapters with visible damping and multiplicity |
| `DivisorMask` | A1–A3 | Divisor bounds, low-primitive bilinear estimate and regrouped-mask comparison |
| `FourierCompatibility` | H1–H4 | Involution sign, signed separator and fully corrected Fejer identity |
| `Validation` | Exact roots | Aggregate consumer, declaration types and axiom prints |

These are proposed names and boundaries, not claims of compilation. The algebraic involution lemma from H3 can be implemented before the measure theory in H1. The quotient/Taylor equivalence (4.4) can be formalized as a separate representation theorem after the explicit leading-jet lemmas. The exact integral version of A2 requires its finite-sum/source-support interface, not just a theorem about an abstract majorant.

## 12.4 Existing native declarations to reuse, not re-postulate

The pinned source contains the following relevant names:

- `nativeZeroMultiplicity_order` and `nativeZeroMultiplicity_deriv_order`;
- `nativeZeroJetKernelMultiplier_order` and `nativeZeroJetInputMultiplier_order`;
- `nativeZeroJetInputMultiplier_jet` and `nativeZeroJetSourceFactor_ne_zero`;
- `nativeActualInputLaplace_eventuallyEq_multiplier` and `nativeActualInputLaplace_order_of_zero`;
- `nativeCompletedInput_zeroJet_value` and `nativeCompletedInput_zeroJet_ne_zero`;
- the actual kernel moment and adjoint-kernel declarations in `NativeActualKernelZeroJets.lean`;
- the three explicitly conditional cuts in `Step4OutputSufficiency.lean`.

The two actual-transform modules distinguish analytic formulas from the physical integrals. Their neighborhood equalities are precisely the interface OPICA needs. Do not replace them with a new caller premise asserting the desired native nonzero jet, source visibility, or prime-field membership.

The original constrained-contact paper is not present as a fully compiled C05 theorem suite on the audited scope. An OPICA contact application must therefore remain a clearly labelled paper adapter or a theorem conditional on explicit mathematical hypotheses until those source theorems are formalized. It must not be smuggled into the native producer as an axiom.

## 12.5 Dependency and acceptance order

**Core first.** Implement local leading-jet algebra, correction composition, elementary log comparison, finite-chain propagation, projection/compatibility algebra and exact counterexamples. These do not need the conjecture or an independent Step 4 upper.

**Native binding second.** Instantiate the local laws using the existing source-specific zero/kernel/input declarations, checking the precise right-zero choice, damping shift and source. The result should explain the already proved nonzero input jet, not claim a new native upper.

**Analytical extensions third.** Formalize the low-mask integral, Fourier separator and any J5.2/MS1 native rate instance only with all their analytic dependencies. Generic rate lemmas may compile earlier with a stated rate-limit hypothesis; that is not a compiled proof of the native hypothesis.

**Required gates.** For every promoted root, record the exact Git SHA and tree, full declaration type, imports, assumption closure and `#print axioms`. No `sorry`, `admit`, new project axiom or hidden RH-equivalent premise is permitted. The gate must distinguish ordinary kernel-checked evaluation from trust extensions such as native compiler evaluation. Compile the actual consumer modules, not merely a new definition with no native use.

The existing `.github/workflows/rhrc_post290_step123_output.yml` names implemented components explicitly. The next PR should either add the new component list through the reviewed integration process or supply a separately pinned OPICA workflow with its own exact receipts. It must not silently change the historical 44-field acceptance contract, semantic approval rules, D2 state or existing Step 4 claim caps.

A compiled theorem with a new false axiom would not prove its conclusion. Lean tracks axiom dependencies, but does not establish the truth of newly postulated axioms. This is why the dependency inventory is part of acceptance, not a cosmetic report. [W3]

## 12.6 What success in the next message would and would not mean

A successful first OPICA implementation would formally establish the requested preservation architecture's core and source-bound jet adapters at their exact scopes. It would also formalize the relevant counterexamples to the overly broad proposals. That is a useful new theorem package.

It would **not** establish A-X, B-Y, C-Schur, OPEN-J46, native contact-to-heat positivity, or RH merely because the architecture compiles. The independent-constraint layer records the exact location where new mathematics must enter. That layer may have generic implication lemmas, but no supplied native closing certificate in this paper.


## Exact proposed names by paper statement

### L1: General local multiplier law
- Module: `Zeta23/OPICA/LocalObstruction.lean`.
- Proposed public name: `completion_leading_jet` (not yet implemented).
- Paper section: 4.2.
- Premises: simple pole R/x+h with R != 0; holomorphic multiplier x^k u with u(0) != 0.
- Conclusion: Exact order k-1 and leading derivative (k-1)! u(0)R when k>=1.
- Prerequisites: standard mathematical foundations stated in the paper.

### L2: Zero ideal, residual and completion quotients
- Module: `Zeta23/OPICA/LocalObstruction.lean`.
- Proposed public name: `residual_congr_preserves_residue` (not yet implemented).
- Paper section: 4.3.
- Premises: Z has finite positive analytic order m; holomorphic coefficient germs.
- Conclusion: O/(Z) is truncated Taylor algebra; residual congruence preserves residue; completion induces an isomorphism of the stated one-dimensional carriers.
- Prerequisites: L1.

### L3: Repeated completions and normalization
- Module: `Zeta23/OPICA/LocalObstruction.lean`.
- Proposed public name: `iterated_completion_leading_jet` (not yet implemented).
- Paper section: 4.4.
- Premises: positive finite completion count; nonzero leading units.
- Conclusion: Exact order pm-1, factorial coefficient, and the double-completion Leibniz binomial.
- Prerequisites: L1.

### L4: Affine corrected finite composition
- Module: `Zeta23/OPICA/AffineTransport.lean`.
- Proposed public name: `affine_transport_corrected_eq` (not yet implemented).
- Paper section: 4.5.
- Premises: finite path; holomorphic backgrounds explicitly recorded; finite nonzero multipliers.
- Conclusion: Corrected output equals product multiplier times initial pole; raw output needs a separate background-vanishing condition.
- Prerequisites: L1.

### L5: Limit scope and residue continuity
- Module: `Zeta23/OPICA/LocalObstruction.lean`.
- Proposed public name: `residue_continuous_of_circle_uniform` (not yet implemented).
- Paper section: 4.7.
- Premises: common meromorphic disk and only center pole for continuity claim; uniform convergence on boundary circle.
- Conclusion: Residues converge under stated topology; compact-time or safe-half-plane convergence alone does not suffice.
- Prerequisites: standard mathematical foundations stated in the paper.

### E1: Logarithmic comparison inequality
- Module: `Zeta23/OPICA/EnergyRate.lean`.
- Proposed public name: `log_one_add_posPart_sub_le` (not yet implemented).
- Paper section: 5.2.
- Premises: real positive parts or real/complex magnitudes.
- Conclusion: Log-one-plus observations differ by at most log(1+absolute error).
- Prerequisites: standard mathematical foundations stated in the paper.

### E2: Subexponential additive rate preservation
- Module: `Zeta23/OPICA/EnergyRate.lean`.
- Proposed public name: `rate_congr_of_subexp_error` (not yet implemented).
- Paper section: 5.3.
- Premises: T_n>0 tending to infinity; actual difference is subexponential on same schedule.
- Conclusion: Magnitude and positive-part rate differences vanish; limits and limsups/liminfs transfer.
- Prerequisites: E1.

### E3: Tempered scaling and inverse cost
- Module: `Zeta23/OPICA/EnergyRate.lean`.
- Proposed public name: `rate_congr_of_tempered_scale` (not yet implemented).
- Paper section: 5.4.
- Premises: nonzero multiplier with subexponential magnitude and inverse; positive multiplier for positive-part claim.
- Conclusion: Magnitude rate preserved; positive-part requires orientation.
- Prerequisites: standard mathematical foundations stated in the paper.

### E4: Growing-chain accumulated budget
- Module: `Zeta23/OPICA/Composition.lean`.
- Proposed public name: `affine_chain_budget` (not yet implemented).
- Paper section: 5.5.
- Premises: full product and propagated additive budget controlled.
- Conclusion: Exact affine expansion; rate comparison follows only with total budget.
- Prerequisites: E2, E3.

### E5: Quiet cofinal observations
- Module: `Zeta23/OPICA/Composition.lean`.
- Proposed public name: `quiet_cofinal_rate_zero` (not yet implemented).
- Paper section: 5.6.
- Premises: full native rate limit separately supplied; same observable on cofinal sequence; zero limiting upper exponent and cost.
- Conclusion: The supplied full rate is zero; does not construct quiet windows.
- Prerequisites: standard mathematical foundations stated in the paper.

### C1: Faithful quotient map criterion
- Module: `Zeta23/OPICA/Composition.lean`.
- Proposed public name: `quotient_map_injective_iff` (not yet implemented).
- Paper section: 6.1.
- Premises: linear map respects the declared background subspaces.
- Conclusion: Induced quotient map is injective iff preimage of target background equals source background; faithful composition.
- Prerequisites: standard mathematical foundations stated in the paper.

### C2: Typed finite-path nonvanishing
- Module: `Zeta23/OPICA/Composition.lean`.
- Proposed public name: `obstruction_path_nonzero` (not yet implemented).
- Paper section: 6.3.
- Premises: source/domain admissibility; proved commuting carrier maps that reflect zero, or proved nonvanishing implications.
- Conclusion: Nonzero observations persist along the finite typed path; bridges are not postulated.
- Prerequisites: C1, L4, E4.

### A1: Explicit divisor bounds
- Module: `Zeta23/OPICA/DivisorMask.lean`.
- Proposed public name: `divisor_count_square_le` (not yet implemented).
- Paper section: 7.2.
- Premises: positive integer order and indices; X>=1.
- Conclusion: Submultiplicativity, squared divisor bound, and two finite weighted sum inequalities.
- Prerequisites: standard mathematical foundations stated in the paper.

### A2: Native low-mask and mixed-term bounds
- Module: `Zeta23/OPICA/DivisorMask.lean`.
- Proposed public name: `low_primitive_bilinear_bound` (not yet implemented).
- Paper section: 7.3.
- Premises: bounded causal drive with nonnegative gap; finite window; coefficient divisor envelopes; actual same-index masks.
- Conclusion: DC1 bound and the complete masked Type I estimates; source-variable costs explicit.
- Prerequisites: A1.

### A3: Lawful regrouped-mask adapter
- Module: `Zeta23/OPICA/DivisorMask.lean`.
- Proposed public name: `mask_regrouping_difference` (not yet implemented).
- Paper section: 7.4.
- Premises: two exact expansions of the same field; both low-mask budgets separately proved.
- Conclusion: High-mask difference equals difference of low masks; rate equality only with both costs controlled.
- Prerequisites: E2.

### B1: Weighted Laplace holomorphy and pole exclusion
- Module: `Zeta23/OPICA/NativeJetAdapter.lean`.
- Proposed public name: `laplace_holomorphic_of_weighted_L2` (not yet implemented).
- Paper section: 8.1.
- Premises: actual causal weighted L2 premise; source-identified meromorphic continuation on connected domain.
- Conclusion: Holomorphy in Re z>epsilon and derivative bound; nonzero pole there contradicts the weighted norm.
- Prerequisites: standard mathematical foundations stated in the paper.

### B2: Range separation by an actual annihilator
- Module: `Zeta23/OPICA/NativeJetAdapter.lean`.
- Proposed public name: `range_distance_of_annihilator` (not yet implemented).
- Paper section: 8.2.
- Premises: bounded linear forward map; nonzero continuous annihilator; actual input pairing nonzero.
- Conclusion: Input outside range closure with quantitative distance lower bound.
- Prerequisites: standard mathematical foundations stated in the paper.

### O1: Recovery after projection
- Module: `Zeta23/OPICA/ObservationCompatibility.lean`.
- Proposed public name: `observation_factors_iff_ker_le` (not yet implemented).
- Paper section: 9.1.
- Premises: linear maps on finite-dimensional spaces.
- Conclusion: Target factors through projection iff kernel inclusion; uniform cost needed across changing spaces.
- Prerequisites: standard mathematical foundations stated in the paper.

### O2: Gram-rank and operator-norm controls
- Module: `Zeta23/OPICA/ObservationCompatibility.lean`.
- Proposed public name: `gram_integral_not_rank_one` (not yet implemented).
- Paper section: 9.2.
- Premises: well-defined finite-dimensional Gram integral.
- Conclusion: PSD does not imply rank one; rank-two exact fixture; one observed bound not an operator bound.
- Prerequisites: standard mathematical foundations stated in the paper.

### O3: Finite compatibility dual certificate
- Module: `Zeta23/OPICA/ObservationCompatibility.lean`.
- Proposed public name: `incompatible_iff_left_annihilator` (not yet implemented).
- Paper section: 9.3.
- Premises: finite complex matrix and data vector.
- Conclusion: Range failure iff nonzero left-null pairing; exact distance dual formula.
- Prerequisites: standard mathematical foundations stated in the paper.

### O4: Equivalent observations preserve compatibility
- Module: `Zeta23/OPICA/ObservationCompatibility.lean`.
- Proposed public name: `compatibility_under_invertible_left_map` (not yet implemented).
- Paper section: 9.4.
- Premises: invertible left map for equivalence.
- Conclusion: Source-derived repeated observations do not create new inconsistent data.
- Prerequisites: standard mathematical foundations stated in the paper.

### H1: Signed sharp-gap separator
- Module: `Zeta23/OPICA/FourierCompatibility.lean`.
- Proposed public name: `signed_sharp_gap_separator` (not yet implemented).
- Paper section: 10.1.
- Premises: even real order-zero measure; linear total-variation growth; Fourier self-duality; exact open unit gap; nonnegative off-lattice restriction.
- Conclusion: Measure is zero; no native contact-to-measure map supplied.
- Prerequisites: standard mathematical foundations stated in the paper.

### H2: Global negative off-lattice mass budget
- Module: `Zeta23/OPICA/FourierCompatibility.lean`.
- Proposed public name: `signed_gap_negative_mass_budget` (not yet implemented).
- Paper section: 10.2.
- Premises: same growth, duality and gap; arbitrary signs off lattice.
- Conclusion: Weighted negative mass globally bounds the stated finite-region positive mass.
- Prerequisites: H1 pairing proof.

### H3: Involution commutator parity
- Module: `Zeta23/OPICA/FourierCompatibility.lean`.
- Proposed public name: `commutator_anti_invariant` (not yet implemented).
- Paper section: 10.3.
- Premises: linear involution; well-defined map on common space; selfdual input.
- Conclusion: Commutator output is anti-selfdual; its selfdual projection is zero.
- Prerequisites: standard mathematical foundations stated in the paper.

### H4: Fejer identity with affine completion correction
- Module: `Zeta23/OPICA/FourierCompatibility.lean`.
- Proposed public name: `fejer_completion_affine_identity` (not yet implemented).
- Paper section: 10.4.
- Premises: squared-sinc/triangle Fourier convention; t>=0; legitimate convergent Poisson pairing.
- Conclusion: Exact fractional-part kernel, cusp behavior and non-omittable transform correction.
- Prerequisites: standard mathematical foundations stated in the paper.

## Required source and execution receipts

For each actual implementation commit: record tree, changed declarations, exact theorem types, imports, axiom closure, compiler exit status and relevant workflow outcomes. Classify every new job as formal validity, regression or research-producing. Never report a skipped or running job as passed. Preserve historical D2/claim status. A green generic theorem is an input to post-green mathematical reasoning, not a promotion of RH.

### Acceptance distinctions

1. Core abstract lemmas: kernel-checked proofs from the permitted axiom base.
2. Native local adapter: actual fixed source, selected right zero, damping shift and physical-neighborhood identities from existing modules.
3. Native energy adapter: only promote once J5.2/MS1 and all required rate premises are actually formalized; a conditional generic theorem is not that promotion.
4. Native contact/heat adapter: not supplied by this paper. Keep its pending inputs explicit rather than importing a paper source as an axiom.

No generated `.lean` stub containing `sorry` or an unproved closing axiom accompanies this contract. The next stage must implement real proofs and report any remaining formalization gaps explicitly.
