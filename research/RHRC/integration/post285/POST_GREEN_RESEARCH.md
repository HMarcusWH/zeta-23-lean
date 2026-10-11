# Post-285 research report (Steps 18–120: M31, M38, M55, M65–M77)

Terminal claim: **RH_OPEN**. This report is the M77 integration note for the
post-285 branch. It sorts every result into one of five classes:

- **PROVED**: a Lean root in `PROOF_ROOTS.json` that compiles with only
  `propext`, `Classical.choice` and `Quot.sound`. It stays `PROVED_PENDING_CI`
  until the PR's CI is green.
- **DERIVED**: a correct argument on paper that Lean has not checked.
- **EXPERIMENTAL SIGNAL**: floating-point or interval evidence. It never counts
  as a proof.
- **LEAD**: a concrete next step that looks viable.
- **OPEN**: no proof, and no claim of one.

The machine-readable versions are:
- `STEP_STATUS_MATRIX.json` (Steps 18–120);
- `OPEN_OBLIGATIONS.json` (M31, M32, M38, M55, M65, M66, M70–M77 plus
  cross-references into the post-284 ledger);
- `PROOF_ROOTS.json`;
- `EXPERIMENT_DISPOSITIONS.json`;
- `WORKFLOW_HARVEST.json`.

`build_post285_ledgers.py --write` regenerates all five, and
`check_post285_ledgers.py` is the CI firewall that keeps them current.

## 1. PROVED in this PR (pending CI)

| Package | Module | Main roots | Steps |
|---|---|---|---|
| M74 | `CanonicalSecularResolvent` | `canonical_rankOneIntertwining`, `canonical_apply_resolventRay`, `canonical_det_eq`, `canonical_resolventRay_contact_iff`, `canonical_ker_eq_span_of_contact`, `canonical_ward_identity`, `canonicalResolventGamma_pos`, `canonical_momentFour_resolventRay`, `canonical_contact_phase`, `canonical_re_conj_mul_momentFour_pos_of_approx` | 49–52, 97, 111, 112, 116–118 |
| M70 | `CanonicalSourceExcursion` | `sourceEnergyRe_excursions_of_zeroSum` | 108 |
| M73 | `CanonicalCenteredIndexPoincare` | `centeredHalfShiftMass_eq`, `sum_normSq_le_four_mul`, `parityGap_mul_norm_sq_le_four_mul_source_mul_momentFour` | 89, 90, 115 |
| M75 | `CanonicalSourcePrimeSampling` | `norm_sourceEntry_sub_le`, `exists_sourceNegativeWindow`, `exists_prime_physicalSecondPrimeTerm_pos_and_two_neg` | 119, 120 |
| M72 | `CanonicalSourceSpectralFlow` | `exists_sourceDegenerate_of_half_neg`, `parityBoundaryFlat_sourceDegenerate` | 45, 110 (first passage) |
| M26–M28, M14 | `CanonicalShiftedSecular` | `canonical_shifted_det_eq`, `canonical_shifted_eigen_iff`, `canonical_finrank_eigenspace_le_one`, `canonical_contact_overlap`, `canonical_contact_overlap_norm_le`, `canonical_odd_ker_le_span`, `canonical_odd_contact_iff`, `canonical_odd_det_eq`, `canonical_tied_contact_orthogonality` | 58, 59 (simplicity), 60 (identity), 64; branch analysis |
| M28 | `CanonicalContactOverlapSign` | `exists_det_eq_ofReal_pos_of_coercive`, `secular_resolvent_slope_pos`, `secular_overlap_pos`, `canonical_contact_overlap_pos` | 60 (sign) |
| M65 | `CanonicalPrimeFreeF04` | `hasDerivAt_integral_moving_upper`, `matrixRealEnergy_canonical_eq_regularized`, `hasDerivAt_wCorrection`, `hasDerivAt_primeFreeFirstChannel`, `productionContactF04DerivativeAuthority_of_lt_log_two` | 21, 24, 27, 93, 101, 105 on `(0, log 2)` |
| M06/M53 (global F04) | `CanonicalGlobalF04` | `hasDerivAt_ite_le`, `productionArithmeticRealValue_eq_channels_sum`, `hasDerivAt_primeFirstChannel`, `productionContactF04DerivativeAuthority_of_pos`, `canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos` | 21, 24, 27, 93, 101, 105 at every `L > 0` |
| M66, Step 103, F07 | `CanonicalLocalBirdfishie` | `productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest`, `productionContactEulerCurvature_le`, `productionContactEulerCurvature_neg`, `GeneratedStrictEvenContact.secondPhysicalValue_eq_two_mul_responseCost`, `GeneratedStrictEvenContact.fresh_of_lt_primeFreeRadius`, `GeneratedStrictEvenContact.completed_production_frontier_unconditional` | 19, 27, 74, 102–104 |
| M31 (conditional barrier) | `CanonicalSecularGronwall` | `gronwall_lower_bound`, `gronwall_pos`, `evenCompressedCanonical_det_eq_zero_of_bottom_eq_zero`, `canonical_evenBottom_pos_of_gronwall` | 66 |
| M55, M38 | `CanonicalWeightedChebyshevAbel` | `psi_sub_self_eq_weightedRemainder`, `abs_psi_sub_self_sub_one_le`, `isGreatest_weightedRemainder`, `isGLB_weightedRemainder` | 75, 96 |

### What these results do not say

- **M74** works for every aperture `L > 0` and `K ≥ 2` where the odd Rayleigh
  bottom is positive. It does not say that a contact exists or that none exists.
  The condition `S_L(x_L) = 1` is equivalent to contact, so it is never used as
  an independent opposite side. `A_L` is the even compressed operator and is
  kept separate from the scalar `𝓐_L`. `D` is not assumed unitary anywhere.
- **M70** is a statement about the source energy `e_{Dz}(ω)` as a function of
  `ω`. It is not a statement about the arithmetic functional.
- **M73** improves the centered-index coercivity constant from `C_K < 5` to
  `4`. Only the upper bound is proved. That `1/4` is sharp is an experimental
  signal.
- **M75** proves that individual prime summands have opposite signs. It does
  not bound their sum. The aperture threshold is `L ≥ π² M_K log 2`, about
  `3.7·10³` at `K = 2`, so the theorem only applies at very large apertures.
- **`CanonicalShiftedSecular`** proves that every even eigenvalue below the odd
  floor is simple, and the exact Step 60 overlap identity
  `⟪x_L, D⁻¹g⟫ · S_L(w_L) = ‖x_L‖²` at an even contact. It does not prove the
  alternating root slopes. The odd-first and tied statements are identities.
  They exclude no branch.
- **`CanonicalContactOverlapSign`** proves that both `S_L(w_L)` and
  `⟪x_L, D⁻¹g⟫` are real and strictly positive at an even contact, given an
  even bottom `≥ 0` and an odd bottom `> 0`. The even-bottom hypothesis is the
  first-crossing geometry. It is assumed, never inferred from `T ≤ 1`. The
  theorem does not say that a contact exists.
- **M65 and global F04** are derivative transport only. They say that the three
  fields of `ProductionContactF04DerivativeAuthority L K` hold for the actual
  canonical even compressed family, at every `L > 0` and every `K`. They give no
  sign and exclude no contact. The single `cCorrection` repair is the one inside
  `canonicalSourceMatrix`; nothing adds it a second time.
- **M66** proves that the Euler-corrected curvature `E'' + (2/L)E'` is strictly
  negative on nonzero even boundary-flat vectors for
  `0 < L < ε_K = 1/(2π²(2K+1)K²)`. So a generated strict-even contact with
  `L* < ε_K` is not stationary, hence fresh-born. This is **possibly vacuous**:
  numerically the even ground is positive on all of `(0, log 2)` for
  `K = 2..16`, so no generated contact is known to lie below `ε_K`. It says
  nothing above `ε_K` and nothing about odd-first, tied or interior branches.
- **Step 103 and the F07 frontier.** At a stationary generated strict-even
  contact, the complete second physical value (pole, archimedean and every
  prime up to `e^{L*}`) equals `2⟨A w, w⟩ ≥ 0` for the stationary response `w`.
  The post-284 frontier theorems that needed an F04 hypothesis now hold without
  it (`*_unconditional`). They show the stationary production remainder is
  strictly positive at every stationary generated strict-even contact.
  Excluding that saturation is OBS-060O, which stays OPEN.
- **M55** is classical, unconditional arithmetic: the exact partial summation
  `ψ(x) − x = 1 + √x R(x) − ½∫₁ˣ R(t)/√t dt` for real `x ≥ 1`, and the transfer
  bound `|ψ(x) − x − 1| ≤ 2M√x` when `|R| ≤ M` on `[1, x]`. It proves no size of
  `R`. A bound `R(x) = O_ε(x^ε)` for every `ε > 0` would be RH-strength, so no
  theorem in this project may take it as a premise.
- **M38** makes the oscillation of `R` on `[1, e^L]` a finite computation: the
  supremum is a maximum over integers, and the infimum is a finite minimum that
  may be only a left limit. It bounds nothing.
- **M31** is a **conditional** barrier. The abstract part is the Grönwall lower
  bound `y(t) ≥ y(a) exp(−∫ₐᵗ C)` for `y' ≥ −C y` with `C` continuous. The
  canonical part says: if the odd bottom is positive on `[L₀, L₁]`, the even
  bottom is positive at `L₀`, and the secular margin `y = 1 − T`
  (`det A_L = det B_L · y`) obeys `y' ≥ −C y`, then the even bottom stays
  positive on `[L₀, L₁]`. The inequality `y' ≥ −C y` is the plan's (67.1), and
  no admissible `C_K` is known (M32, OPEN). The theorem excludes nothing by
  itself, and the start `A_{L₀} ≻ 0` is a separate hypothesis.
- **M72** proves a first degenerate passage on `(1/2, 1)` whenever the
  half-aperture form has a negative vector. The multiplicity count, which needs
  continuous eigenvalue branches, is still OPEN.

### Proof outline for F04 and M66

M65 starts from the real M05 regularized energy identity with the exact
weights `Λ(q)(log q)²/√q`. On `0 < L < log 2` no prime power lies below `e^L`,
so the energy is an integral against `W − ρ` plus the `w(L)` correction. Lean
differentiates it under a moving upper limit (`hasDerivAt_integral_moving_upper`)
with `t ρ(t)` replaced by the continuous `regularizedArchScale`, which removes
the `1/(2t)` singularity. The endpoint terms cancel because
`wCorrection'(L) = e^{−L/2} ρ(L)` and `e_z(0) = e'_z(0) = 0` on even
boundary-flat vectors. The mixed field follows by real polarization of both
sides.

Global F04 writes the prime staircase as a finite sum of terms switched on by
`log q ≤ L`. Each entering term has zero value and zero slope at its seam,
because `e_z(0) = e'_z(0) = 0` (energy channel) and `e'_z(0) = e''_z(0) = 0`
(first channel) on boundary-flat vectors. `hasDerivAt_ite_le` then glues the
one-sided derivatives at the seam.

M66 uses `e''_z = −(2π)² e_{Dz}` for zero-sum vectors to rewrite the
Euler-corrected second test as `−(2π)²/L⁴ · Q_K(L, z)`. It then applies the
existing M42 lower bound `primeFreeSecondTest_ge`,
`Q_K ≥ L² M (1/(4π²) − L(2K+1)K²/2)`.

### F04 strength audit

- **Statement.** `productionContactF04DerivativeAuthority_of_pos :
  ∀ (K : ℕ) {L : ℝ}, 0 < L → ProductionContactF04DerivativeAuthority L K`. The
  only premise is `0 < L`. There is no contact, sign, F04-equivalent or
  RH-equivalent hypothesis, and no section variable adds one.
- **Target.** `ProductionContactF04DerivativeAuthority` is the post-284
  structure itself, not a renamed copy. Its three fields are the first
  variation, the Euler-corrected fixed second variation, and the mixed aperture
  derivative of the actual canonical even compressed family, each equal to the
  complete physical functional (pole, archimedean and every prime up to `e^L`)
  of the clamped production test. This is the plan's F04 at every aperture.
- **Consumers.** Ten `Zeta23/CCM` theorems took this structure as a hypothesis.
  Each has an instance here with no F04 hypothesis:
  - `canonicalFirstVariation_eq_physical_of_pos`,
    `canonicalFixedSecondEuler_eq_physical_of_pos`,
    `canonicalMixedFirstVariation_eq_physical_of_pos`;
  - `canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos`,
    `canonicalStationaryCurvature_eq_productionSaturationGap_of_pos`;
  - `GeneratedStrictEvenContact.production_stationary_saturation_unconditional`,
    `…production_stationary_remainder_pos_unconditional`,
    `…inherited_production_saturation_unconditional`,
    `…completed_production_frontier_unconditional`,
    `…inherited_completed_production_frontier_unconditional`.
- **Not changed.** The eight claim-contract wrappers in
  `Zeta23/RHRC/ContactCalculusContract.lean` still take `hF04` as a parameter.
  They can be instantiated with the constructor; rebinding the registered
  claims waits for the #286 registry. The structure's docstring in
  `FirstCrossingProductionCurvatureBridge.lean` still calls F04 "presently
  OPEN". It is left as written to avoid editing #284 sources, and this ledger
  is the authority.

## 2. DERIVED (not formalized)

### M71: Andréief interior inertia (Step 109)

The planned route has these steps:
1. Prove the Andréief identity by Leibniz expansion and
   `integral_fintype_prod_eq_prod`.
2. Factor the Vandermonde (`Matrix.det_vandermonde`).
3. Get the sign of the kernel determinant from the monotonicity of `cos t` and
   `cos(a − t)` on the relevant ranges.
4. Turn signed leading minors into exact inertia, using a B-orthogonal
   Gram–Schmidt basis with pivots `D_k/D_{k−1}` and
   `exactInertia_of_orthogonal_split`.

**Status: OPEN.** Exact inertia is proved only at `ω = 1/2` (PR #285).

### M72 multiplicity

Continuous eigenvalue branches of the Hermitian family `ω ↦ S(ω)|_V` give at
least as many passages, counted with multiplicity, as there are negative
half-aperture eigenvalues. **Status: OPEN in Lean.**

## 3. EXPERIMENTAL SIGNAL

The details are in `FALSIFICATION_REPORT.md`.

- **M76.** Rank-one holds to 2e-15 on the executable canonical matrices. On the
  46 float-resolved points (`K = 2..5`, `L ≤ 6`), the margin `1 − T(L)` is
  positive, with a minimum of 4.4e-4.
  - Pole and prime channels cancel at up to 7e9 times the net value.
  - The other 50 points need Arb before any sign can be read from them.
- **M73.** The optimal Poincaré constant decreases toward `1/4`; it is 0.2513 at
  `K = 80`.
- **M75.** The window `η_K` is very conservative. The true negative run is
  about 198 times `2η_K`.
- **F04 regression.** At matrix level against the executable canonical matrix,
  the first identity holds to 5e-8 and the Euler identity to 1.2e-6 for
  `K = 2..5`. This covers the prime-free window, prime cells and the seams
  `log 3, log 4, log 5` exactly. Both negative controls (a nonzero coefficient
  sum, and `cCorrection` added twice) miss by exactly the predicted amount.
- **M66 radius.** The Euler form stays negative definite up to about
  `L = 0.55` (`K = 2`), falling to 0.30 (`K = 16`). The proved radius `ε_K` is
  smaller by two to four orders of magnitude.
- **No even contact below `log 2`.** For `K = 2..16`, the even compressed
  ground stays positive on `(0, log 2)`. Its minimum sits at the right end and
  falls from 0.096 (`K = 2`) to 0.003 (`K = 16`).

## 4. LEADS

1. **A larger Euler radius.** The proved `ε_K` is smaller than the observed
   negativity radius (0.3–0.55) by a factor of about `200` to `10⁴`. All of
   that loss sits in the M42 lower bound `primeFreeSecondTest_ge`. A sharper
   lower bound for `Q_K` on the even boundary-flat carrier would extend M66
   directly, possibly to a window that is not vacuous.
2. **The even ground below `log 2`.** The observed positivity of the even
   ground on `(0, log 2)` is the statement "no strict-even first contact in the
   prime-free window". With F04 and the Euler identity now proved there, a
   lower bound on `Q_K` along the whole window is a concrete target.
3. **Arb resolution of the 50 unresolved M76 points.** Use
   `canonical_source_arb.py` with the M76 channel split.
4. **A sharper M75 window.** The 198× slack in `η_K` suggests that a
   second-derivative window could lower the `π² M_K log 2` threshold by orders
   of magnitude.

## 5. Global branch analysis (M14, M77)

At a first-contact aperture `L*`, both bottoms are positive for `L < L*`.
Three branch types can occur at `L*`:

| Branch | At `L*` | What is available |
|---|---|---|
| Even-first (strict-even) | even bottom = 0, odd bottom > 0 | **PROVED (M74):** `ker A = ℂ ∙ x_L`; contact iff `S_L(x_L) = 1`; phase lock `Re(conj(S z) M4 z) = γ|S z|² > 0`. **PROVED (M28 sign):** `⟪x_L, D⁻¹g⟫ > 0`. **PROVED (M66):** not stationary when `L* < ε_K`. **PROVED (Step 103):** if stationary, the second physical value is `2⟨A w, w⟩ ≥ 0`. The opposite-side sign is OPEN (M76). |
| Even-first, eigenvalue structure | odd bottom > 0 | **PROVED (`CanonicalShiftedSecular`):** every even eigenvalue below the odd floor is simple; `det(A − λ) = det(B − λ)(1 − T_L(λ))`. |
| Odd-first | odd bottom = 0, even bottom > 0 | **PROVED (`CanonicalShiftedSecular`):** see the swapped instance below. |
| Tied | both bottoms = 0 | **PROVED (`canonical_tied_contact_orthogonality`):** see the tied identity below. Nothing beyond that. |

**Odd-first, swapped instance.** The relation
`A D⁻¹ − D⁻¹ B = (−D⁻¹ g) ⊗ (H ∘ D⁻¹)` is again a rank-one intertwining, so the
abstract M74 algebra applies with the roles of the two sectors swapped. This
gives:
- `ker B ⊆ ℂ ∙ D A⁻¹ D⁻¹ g`;
- contact iff `H(A⁻¹ D⁻¹ g) = −1`;
- `det B = det A · (1 + H(A⁻¹ D⁻¹ g))`.

**Tied identity.** For `A z = 0` and `B y = 0`, pairing the rank-one relation
with `y` and using the symmetry of `B` gives `H(z)⟨y, g⟩ = 0`. So either
`D z ∈ ker B`, or `g ⊥ ker B`.

Branches outside first contact (fresh-born, interior, later crossings) stay
OPEN, as in post-284 M14. No branch is excluded.

## 6. Audit of the post-284 OPEN rows

The post-284 ledger has 37 OPEN rows. This PR leaves those rows untouched and
records how this PR affects each one in `post284_cross_references`. Each row
falls into one of these classes:

| Class | Rows | Comment |
|---|---|---|
| F04-bound | F04_PRODUCTION_DERIVATIVE_AUTHORITY, M09_WEIGHTED_REMAINDER_IDENTITY, F_M33_M34, F_M37, F_M48, F_M49_M51, F_M53_M65, F_M66 | The F04 premise is discharged at every `L > 0`. F_M53_M65, F_M66 and the F04 authority itself are proved here. The others keep their non-F04 parts open |
| Operator seam germs | M07, M10, M11, F_M23_M24, F_M44 | Need operator-norm Taylor majorants at frozen prime seams |
| Classical arithmetic | F_M38, F_M55 | Proved here (M38, M55) |
| Abstract analysis | F_M31 | Proved here as a conditional barrier (M31); the coefficient bound M32 stays OPEN |
| Abstract algebra, provable now | M08_ABSTRACT_CUBIC_SCHUR, M03_RANK_TWO_LAPLACE, M03_WEIGHTED_STAIRCASE_REEXPRESSION | Candidates for the next pushes |
| Partly addressed here | M17 (→M71), M18 (first passage), F_M21 (phase identity), F_M46 (constant 4), F_M58_M63 (phase lock), F_M27 (simplicity), F_M28 (overlap identity and sign), M14 (odd-first and tied algebra) | See the cross-references |
| Research or contact-conditioned | M03_TWO_SCALAR, M13, M16, F_M22, F_M25, F_M29, F_M32, F_M39, F_M45, F_M56_M57, F_M68, OBS060O | No viable proof route identified in this PR |
| Provenance | OAI_SEVEN_EIGHTHS_LOCAL_IMPORT | Audit only |
| Terminal | RH | RH_OPEN |

## 7. OPEN, kept open on purpose

`check_post285_ledgers.py` refuses to let any of these leave OPEN:
- `M14_BRANCH_EXCLUSION`;
- `M32_CANONICAL_GRONWALL_COEFFICIENT`, the coefficient bound (67.1) that the
  M31 barrier needs;
- `M76_ARITHMETIC_COMPOSITION`, the opposite-side sign of the canonical complete
  arithmetic target;
- `OBS060O_STATIONARY_SATURATION_EXCLUSION`;
- `RH`.

Nothing in this PR excludes a strict-even first contact above `ε_K`, and
nothing excludes a stationary one (OBS-060O). Nothing in it proves a
sign of `𝓐_L`. No unconditional theorem in it assumes the desired inequality as a hypothesis;
the conditional M31 barrier states (67.1) as an explicit hypothesis and is not
an exclusion.
