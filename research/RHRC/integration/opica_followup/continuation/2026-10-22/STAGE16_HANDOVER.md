# Stage 16: the nonlinear square defect (R2-S3)

This stage starts from the Stage 15 record `f074ad7a`. The source commit checked here is
`098194685f9365bf6f091bf8192b9381c7d2ba43` (tree `d289da1fe7267a183a7031513e834a3bb0e995a5`).
Exact hashes, commands and logs are in [stage16 STATUS.json](evidence/current-codex/stage16/STATUS.json).
All 100 original roots and 28 acceptance units remain required. RH, Step 4 and the independent
closing inequalities remain OPEN. No frozen specification, PDF, parent mathematical source or
optional-amendment status changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/SquareDefect.lean` imports exactly
`Zeta23.OPICAFollowup.ZeroProfiles` and the parent `Zeta23.OPICA.Involution`, its BUILD_MANIFEST
`direct_project_imports` list, plus one Mathlib file (Riemann-Lebesgue). It defines the two required
definitions:
- `squareGapMeasure` h A: τ_h = \|A - h\|² dx - \|A\|² Σ_(n ≠ 0) δ_n, paired with Schwartz tests;
- `squareDualityDefect` h: d = h ⋆ conj h - \|h\|².

The self-dual projection is the unchanged parent `Zeta23.OPICA.involutionSelfdualProjection` for the
Fourier action T ↦ T ∘ 𝓕 on Schwartz functionals. The narrow runner now builds eighteen modules and
replays twenty-three consumer files. With this stage all four R2-S3 roots have narrow gates.

## Completed narrow gates (local, pinned Linux compiler, committed source)

Hypotheses throughout: h is even, continuous, in L¹ ∩ L², Fourier self-dual (𝓕h = h in the pinned
Mathlib convention), vanishes at infinity, and equals A on [-1, 1]. The last three roots also assume
h ≠ 0.

| Original root | Established | Evidence |
| --- | --- | --- |
| `square_fourier_defect` | - τ_h vanishes on tests supported in (-1, 1): the exact gap, with no origin atom;<br>- τ_h is nonnegative on nonnegative tests vanishing on the lattice (sign);<br>- its density is bounded;<br>- d is continuous, real and C₀, with d = 𝓕(\|h\|²) - \|h\|²;<br>- τ_h(𝓕φ) - τ_h(φ) = ∫ d φ for every Schwartz φ (S3.1). | [ExpectedSquareDefect.lean](consumers/ExpectedSquareDefect.lean) (10 receipts) |
| `square_defect_origin_positive` | - d(0) = ‖h‖₂² - \|A\|² > 0 (S3.2);<br>- ≥ \|A\|² when A ≠ 0;<br>- ‖h‖₂² > 0 when A = 0;<br>- the conjugation is retained. | same file |
| `square_no_lattice_repair` | No lattice weights c make τ_h + Σ c_n δ_n Fourier self-dual. | same file |
| `square_selfdual_projection_fills_gap` | The projection (τ_h + 𝓕τ_h)/2 is self-dual and equals τ_h + d/2 dx. For some 0 < ε < 1 its density d/2 is real and strictly positive on (-ε, ε), inside the old gap. | same file |

**Proof.**
- **Defect.** Self-duality and evenness give 𝓕(conj h) = conj h. The multiplication formula gives
  𝓕(\|h\|²) = h ⋆ conj h.
- **Poisson summation.** Σ_n 𝓕φ(n) = Σ_n φ(n) moves the constant and comb terms through 𝓕 with
  matching origin terms, which leaves 𝓕τ - τ = d dx.
- **Origin value.** Evenness gives d(0) = ‖h‖₂² - \|A\|². The plateau contributes 2\|A\|² to ‖h‖₂², and a
  nonzero continuous h has ‖h‖₂ > 0.
- **No repair.** Translation by one fixes 𝓕φ at every integer. Comparing the self-duality identity
  for φ and its translate, d(x + 1) - d(x) annihilates every test vanishing on the lattice. So d is
  1-periodic, and a 1-periodic C₀ function is 0, contradicting d(0) > 0. The argument compares values
  at the integers only. It never assumes that corrections are absent and never uses the temperedness
  hypothesis, so it excludes every lattice weight.
- **Projection.** 𝓕𝓕φ is the reflection of φ, and τ_h is reflection invariant (h is even), so the
  projection is self-dual. By S3.1 it equals τ_h + d/2. By continuity d > d(0)/2 > 0 near 0, and τ_h
  vanishes there.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **Self-dual.** 𝓕h = h for the Mathlib e^(-2πixξ) transform, which is the convention in which the
  Stage 9 zero profile is self-dual.
- **The measures** are functionals on Schwartz tests. "Tempered lattice-supported order-zero
  correction" is σ(φ) = Σ c_n φ(n) with polynomially bounded weights, and the theorem rejects even
  untempered weights.
- **The Fourier action on functionals** is T ↦ T ∘ 𝓕, passed to the parent projection.
- **"Exact gap/sign/origin".** These are the gap vanishing, the off-lattice sign and d(0), each stated
  separately.

The consumer instantiates every root at the actual zero profile h_κ, A = 1, of an actual zero. All
hypotheses are discharged from Stage 9, which gives d(0) = ‖h_κ‖₂² - 1 ≥ 1 and the gap-filling
interval.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for eighteen modules and twenty-three
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Eight negative
controls are rejected for their intended reasons:
- a self-dual square;
- the origin value ‖h‖² (no conjugate subtraction);
- a negative origin value;
- the plateau bound 2\|A\|²;
- a repairing lattice correction;
- the projection τ + d;
- a negative gap density;
- the identity without self-duality.

The ledger now records 41 historical, 46 narrow and 13 absent roots. This is not aggregate
acceptance of 87 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The four roots, the supporting results listed in
   STATUS.json and the actual-profile consumer, all standard-only.
2. **Workflow harvest at `bd918c7c`** ([complete harvest](evidence/current-codex/stage16/ci-harvest-bd918c7c.json)).
   - All 22 runs on the Stage 14 head have completed; no run was cancelled. This completes the Stage 15
     partial harvest.
   - OPICA preparation, the exact-source subset, the narrow job (sixteen modules, twenty-one consumer
     files) and the frozen-regression jobs pass in both the PR and the push run.
   - All eighteen inherited research replays pass, including the two long ones:
     - post287 WP2/WP4 interval research;
     - the post-284 source-inertia campaign, with its Lean build, axiom audit and proof-escape
       rejection, and every falsifier step through the WP2 Arb-interval verification, the WP4 D2 K3
       feasibility gate (UNRESOLVED allowed) and the WP5 non-zeta control.
   - These are regression and research outputs and create no OPICA theorem authority.
   - Only the designed fail-closed gates are red: Full release readiness (PR and push),
     opica-contract, opica-component-summary, python-rhrc and rhkg-compiler-receipt.
3. **What changed.** R2-S3 is complete at the narrow level. The square construction gives an
   explicitly positive gapped measure with an explicitly nonzero, calculated Fourier defect. No
   forbidden self-dual gapped measure is constructed, matching the paper's summary.
4. **Upstream.** The roots use only the Stage 9 profile facts (evenness, self-duality, plateau, L¹ ∩ L²,
   decay), Mathlib's Fourier inversion, the multiplication formula and Poisson summation, and the
   parent involution. They are zero-free and generic: any h with these properties works.
5. **Downstream.** The planned `Consumers` module imports SquareDefect (BUILD_MANIFEST); its
   `actual_zero_measure_span_consumer` is still absent.
6. **Resurrected routes.** None.
7. **New RH-relevant clues.**
   - EXPERIMENTAL SIGNAL ([numerical-falsification.log](evidence/current-codex/stage16/numerical-falsification.log)):
     - at the first zero, d(0) = 146.36 = ‖h‖² - 1 (‖h‖² = 2N₁₁ of Stage 12);
     - d changes sign first near x ≈ 0.17, so the positive interval inside the gap is short. Its length
       is comparable to π/γ ≈ 0.22.
   - LEAD: the gap-filling scale is set by the zero height. The formal statement guarantees only some
     ε > 0.
   - DERIVED (informal): d annihilates every self-dual test, because ∫ d φ = τ(𝓕φ) - τ(φ) = 0 when
     𝓕φ = φ. That is checked numerically on e^(-πx²). So the defect is anti-self-dual, and the
     obstruction lives entirely in the anti-self-dual sector.
8. **Falsification checks.**
   - Numerical (numpy FFT and mpmath, double precision, not interval certified): S3.1 holds on two
     non-self-dual Gaussians to 1e-6 and 3e-4.
   - The conjugation is not numerically visible on the critical line, where h is real. It is exercised
     formally through complex A, the A = 0 clause and the rejected unconjugated control.
   - Vacuity: the hypotheses are satisfied by every actual zero profile (consumer).
   - Circularity: no premise mentions d or self-duality of τ.
9. **Highest-leverage next moves.**
   - `BoundaryAmplitude` (F3): the generic forced profile for 1/2 < Re ρ < 1 is not a zero profile. It
     needs a local log-form representation without the zero hypothesis, the homogeneous power
     x^(ρ-1) = e^((ρ-1/2)t) in log variables, the generic tail -ζ(1-ρ)x^(-ρ)/b_ρ + κB₂({x})/(2x²), and
     uniqueness and inversion from Stage 15. It is then the native forced resolvent for every such ρ.
   - `CoPoissonJets` → `ConfluentProfiles` → `FiniteSpanSeparation`, J5.2/MS1, and `Consumers`.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 16 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the published Stage 16 record head, the 13 absent roots, RH, Step 4 and
the independent closing inequalities.
