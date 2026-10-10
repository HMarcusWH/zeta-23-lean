# Post-285 research report (Steps 18–120, M70–M77)

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
- `OPEN_OBLIGATIONS.json` (M70–M77 plus cross-references into the post-284
  ledger);
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
  `⟪x_L, D⁻¹g⟫ · S_L(w_L) = ‖x_L‖²` at an even contact. It does not prove
  the sign of `⟪x_L, D⁻¹g⟫`, and it does not prove the alternating root slopes.
  The odd-first and tied statements are identities. They exclude no branch.
- **M72** proves a first degenerate passage on `(1/2, 1)` whenever the
  half-aperture form has a negative vector. The multiplicity count, which needs
  continuous eigenvalue branches, is still OPEN.

## 2. DERIVED (not formalized)

### M65: prime-free F04 on `0 < L < log 2`

Start from the M05 regularized energy identity, using the exact weights. On
`0 < L < log 2` no prime power lies below `e^L`, so

`E_z(L) = ∫₀^L e_z(1 − t/L) (W(t) − ρ(t)) dt + (boundary terms)`.

Differentiate under the integral. The boundary terms cancel because
`e_z(0) = 0` and `w'(s) = e^{-s/2} ρ(s)`. This gives

- `E'(L) = ∫₀^L (t/L²) e_z'(1 − t/L) (W − ρ)(t) dt`;
- `E''(L) + (2/L) E'(L) = ∫₀^L (t²/L⁴) e_z''(1 − t/L) (W − ρ)(t) dt`. This one
  uses `e_z'(0) = 0`, which holds for legal `z`.

These are the clamped production tests in `ProductionContactF04DerivativeAuthority`.

To formalize this, a few things still have to be done:
- Justify dominated differentiation against the `1/(2t)` singularity of `ρ`,
  either through the substitution `t = Lx` or through Leibniz with a removable
  singularity.
- Prove the sesquilinear (`mixed`) version.
- Match the result field by field with the authority structure.

The estimated size is about 1000 lines. **Status: OPEN.** Even a full proof
would only give F04 on `(0, log 2)`, not the global
`F04_PRODUCTION_DERIVATIVE_AUTHORITY`.

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

## 4. LEADS

1. **Positivity of the Step 60 overlap.** `⟪x_L, D⁻¹g⟫ > 0` would follow from
   `S_L(w_L) > 0`. On paper, `S_L(w_L)` is the λ-slope `T_L'(0)`, and at a first
   contact `1 − T_L(λ) = det(A − λ)/det(B − λ) > 0` for `λ < 0`. Formalizing
   this needs the determinant of a positive-definite symmetric map to be
   positive, plus a one-sided limit.
2. **Arb resolution of the 50 unresolved M76 points.** Use
   `canonical_source_arb.py` with the M76 channel split.
3. **A sharper M75 window.** The 198× slack in `η_K` suggests that a
   second-derivative window could lower the `π² M_K log 2` threshold by orders
   of magnitude.

## 5. Global branch analysis (M14, M77)

At a first-contact aperture `L*`, both bottoms are positive for `L < L*`.
Three branch types can occur at `L*`:

| Branch | At `L*` | What is available |
|---|---|---|
| Even-first (strict-even) | even bottom = 0, odd bottom > 0 | **PROVED (M74):** `ker A = ℂ ∙ x_L`; contact iff `S_L(x_L) = 1`; phase lock `Re(conj(S z) M4 z) = γ|S z|² > 0`. The opposite-side sign is OPEN (M76). |
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
| F04-bound | F04_PRODUCTION_DERIVATIVE_AUTHORITY, M09_WEIGHTED_REMAINDER_IDENTITY, F_M33_M34, F_M37 (conditional), F_M49_M51, F_M53_M65, F_M66 (conditional) | Wait on M65 or global F04 |
| Operator seam germs | M07, M10, M11, F_M23_M24, F_M44 | Need operator-norm Taylor majorants at frozen prime seams |
| Abstract algebra, provable now | M08_ABSTRACT_CUBIC_SCHUR, M03_RANK_TWO_LAPLACE, M03_WEIGHTED_STAIRCASE_REEXPRESSION, F_M31, F_M38, F_M55 | Candidates for the next pushes |
| Partly addressed here | M17 (→M71), M18 (first passage), F_M21 (phase identity), F_M46 (constant 4), F_M58_M63 (phase lock), F_M27 (simplicity), F_M28 (overlap identity), M14 (odd-first and tied algebra) | See the cross-references |
| Research or contact-conditioned | M03_TWO_SCALAR, M13, M16, F_M22, F_M25, F_M29, F_M32, F_M39, F_M45, F_M56_M57, F_M68, OBS060O | No viable proof route identified in this PR |
| Provenance | OAI_SEVEN_EIGHTHS_LOCAL_IMPORT | Audit only |
| Terminal | RH | RH_OPEN |

## 7. OPEN, kept open on purpose

`check_post285_ledgers.py` refuses to let any of these leave OPEN:
- `M14_BRANCH_EXCLUSION`;
- `M28_OVERLAP_POSITIVITY`;
- `M65_PRIME_FREE_F04`;
- `F04_GLOBAL_PRODUCTION_DERIVATIVE_AUTHORITY`;
- `M76_ARITHMETIC_COMPOSITION`, the opposite-side sign of the canonical complete
  arithmetic target;
- `OBS060O_STATIONARY_SATURATION_EXCLUSION`;
- `RH`.

Nothing in this PR excludes a strict-even first contact. Nothing in it proves a
sign of `𝓐_L`. Nothing in it assumes the desired inequality as a hypothesis.
