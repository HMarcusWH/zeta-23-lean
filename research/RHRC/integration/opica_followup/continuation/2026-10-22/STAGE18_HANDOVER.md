# Stage 18: multiplicity-sensitive zero-jet measures (R2-H1)

This stage starts from the Stage 17 record `02c0ce8f`. The source commit checked here is
`ff7b7c70` (tree in [stage18 STATUS.json](evidence/current-codex/stage18/STATUS.json), with exact
hashes, commands and logs). All 100 original roots and 28 acceptance units remain required. RH, Step 4
and the independent closing inequalities remain OPEN. No frozen specification, PDF, parent
mathematical source or optional-amendment status changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/CoPoissonJets.lean` imports exactly
`Zeta23.OPICAFollowup.ZeroProfiles` (its BUILD_MANIFEST `direct_project_imports` list) plus one
Mathlib file (the sinh/cosh series). It defines the two required definitions:
- `zeroJetOrder` ρ, the analytic order of ζ at ρ;
- `normalizedZeroMeasureJet` ρ k: the CP1 zero measure at k = 0, and for k ≥ 1 the canonical-Jordan
  density measure of (1/k!) ∂_κ^k g_κ(|x|) at κ₀ = ρ(1 - ρ).

Here g_κ(y) = κ Σ_(1 ≤ k ≤ |y|) (e^(-u/2)/k) Sh(1/4 - κ, u), with u = log(|y|/k), is the entire κ-family
of the actual finite sums. It equals S_ρ(|y|)/b_ρ at every strip parameter ρ ≠ 1/2.

The narrow runner now builds twenty modules and replays twenty-five consumer files.

## Completed narrow gate (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `copoisson_zero_jets_measures` (R2-H1) | For an actual zero with 0 < Re ρ < 1, of multiplicity m ≥ 1, and every k < m:<br>- the local inverse ρ(κ) is holomorphic at κ₀ with derivative -1/(2ρ - 1), and ζ ∘ ρ(·) has order m;<br>- (parameter limits) on Schwartz tests ν_k is (1/k!) ∂_κ^k of the actual construction (CP1.7)/b along ρ(κ), explicitly ∫ g_k φ - [k = 0] Σ_(n≠0) φ(n) (H1.1); ν₀ is the CP1 zero measure;<br>- exact open unit gap, zero origin atom, even Jordan parts, linear variation growth;<br>- jet densities [k = 0] - ([k = 0] κ₀ + [k = 1]) B₂({\|x\|})/(2x²) + O(\|x\|⁻³);<br>- Fourier self-duality on Schwartz tests and as tempered distributions, also for the real part;<br>- the differentiated forced chain (H1.2): (L - κ₀) h₀ = κ₀ G, (L - κ₀) h₁ = h₀ + G, (L - κ₀) h_k = h_(k-1), with G = Σ_(n ≥ 1) δ_n - dx and ⟨L h, ψ⟩ = -∫ h (x² ψ')';<br>- 1 - ρ has the same multiplicity, node κ₀ and jets (its branch is 1 - ρ(κ)); conj ρ has the same multiplicity and conjugate jets. | [ExpectedCoPoissonJets.lean](consumers/ExpectedCoPoissonJets.lean) (9 receipts) |

**Proof.**
- **κ-family.** One cell term of the finite sums is -(2/k) e^(-u/2) sinh((ρ - 1/2) u), and
  τ Sh(τ², u) = sinh(τu) removes the branch. The kernel is entire in w and satisfies
  \|Sh(w, u)\| ≤ \|u\| e^(√\|w\| \|u\|). This gives \|g_κ(y)\| ≤ R (1 + \|y\|)^(3 + ⌈R⌉) on \|κ\| ≤ R.
- **Holomorphic parametric integrals.** For an entire, measurable family with locally uniform
  integrable bounds, every κ-derivative passes under the integral. Measurability of the derivative is
  obtained as a limit of difference quotients, the bounds by Cauchy estimates. A closed-disc version
  gives holomorphy of the Mellin pairing ∫ \|x\|^(ρ-1) φ on the strip.
- **Parameter limits.** At every strip parameter ρ ≠ 1/2 the construction is
  ∫ g_ρ φ + (ζ(ρ)/b_ρ) ∫ \|x\|^(ρ-1) φ - Σ_(n≠0) φ(n). Along ρ(κ) the boundary term is ζ ∘ ρ times an
  analytic factor, so its first m derivatives vanish (`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`).
- **Tails.** The Stage 9 expansion splits g_κ into 1, the power terms, -κ B₂/(2x²) and the remainder
  S-term/b, locally uniformly in κ. The power terms equal ζ(ρ(κ)) times an analytic factor, using
  ζ(1 - s) = E(s) ζ(s) with E(ρ₀) ≠ 0, so they vanish to order m. A Cauchy estimate on a closed disc
  inside the branch domain bounds the remainder jets by C x⁻³.
- **Self-duality.** The construction is Fourier self-dual at every parameter, so the jets are.
- **Chain.** The Stage 11 forced Euler identity holds at every strip parameter. It is reproduced under
  the `CoPoissonJets` namespace because ForcedEuler cannot be imported here. Its κ-jets are taken with
  the parametric-integral lemma and Leibniz for κ·P(κ).
- **Reflection and conjugation.** The order at 1 - ρ is computed through the functional equation.
  Conjugation uses `iteratedDeriv` of conjugation-symmetric functions and the global
  `riemannZeta_conj`.

**Recorded formalization choices (no premise added, no domain narrowed).**
- **The jet measure** is defined from the κ-jet of the actual density, plus the lattice at order zero.
  It is identified with the parameter jets of the actual construction by theorem, not by definition.
- **The hypothesis ρ ≠ 1/2 is derived** from ζ(ρ) = 0 (`zero_ne_half`), not assumed.
- **The chain** is stated on positive-axis tests in the paper's three cases, with the distributional
  meaning ⟨L h, ψ⟩ = -∫ h (x² ψ')'.
- **"Realification"** is the conjugate relation plus the real-part self-duality. Real span statements
  belong to H2.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for twenty modules and twenty-five
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Ten negative controls
are rejected for their intended reasons (STATUS.json). The ledger now records 41 historical,
49 narrow and 10 absent roots. This is not aggregate acceptance of 90 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The root and the supporting results listed in
   STATUS.json, all standard-only. The consumer additionally proves:
   - at every actual strip zero the order-zero jet is the CP1 zero measure, and its parameter limit
     is the construction;
   - the k = 0 chain is exactly the ForcedEuler identity;
   - at multiplicity ≥ 2 the first jet is a pure density measure with tail -B₂/(2x²) + O(x⁻³);
   - the reflected zero is not a new node.
2. **Workflow harvest.** No new harvest. The latest is the Stage 17 partial harvest of `c6ce649d`
   ([file](evidence/current-codex/stage17/ci-harvest-c6ce649d-partial.json)): 19 of 22 runs completed,
   only the designed fail-closed gates are red, and three research replays were in progress. CI on
   `02c0ce8f` was superseded by the push of `ff7b7c70`, and CI on that head was in progress at
   publication.
3. **What changed.** R2-H1 is complete at the narrow level. The whole multiplicity-sensitive family
   of jets that a finite multi-zero linear repair could use is now formally a family of gapped,
   self-dual, linearly growing measures.
4. **Upstream.**
   - Inputs: CP1 (construction, zero measure, self-duality), the Stage 9 expansion, the Stage 11
     cell lemmas.
   - Dependency compression (PROVED): the zero hypothesis enters only through the order of ζ ∘ ρ.
     Every other statement (family identity, construction identity, self-duality, chain) holds at
     every strip parameter.
5. **Downstream.** `ConfluentProfiles` (H2a) can now use the jets. Their first-cell densities are the
   κ-jets of κ Sh(1/4 - κ, u), so their odd Taylor coefficients are the Hermite data of the confluent
   determinant. `FiniteSpanSeparation` (H2b) needs H2a and the parent signed separator.
6. **Resurrected routes.** None.
7. **New RH-relevant clues.**
   - PROVED: beyond the multiplicity, the obstruction to the gap is exactly the boundary term. Its
     first nonvanishing jet is (ζ^(m)(ρ) ρ'(κ₀)^m/(m! b)) ∫ \|x\|^(ρ-1) φ.
   - EXPERIMENTAL SIGNAL ([log](evidence/current-codex/stage18/numerical-falsification.log)): at the
     first (simple) zero the k = 1 jet on a gap test has size 7.8e-4, nonzero. The k = 1 density jet
     decays only like y^(-1/2), matching the predicted power-term derivative with residual × y³ bounded.
   - LEAD: the multiplicity restriction is sharp.
8. **Falsification checks.**
   - The κ-family matches S/b to 2e-30.
   - The order-zero tail residual × y³ stays bounded up to y = 900.
   - The chain for h₁ holds on cells to 3e-30, and the jump of x² h₁' is -1.000001.
   - Vacuity: k = 0 is always admissible at an actual zero, since m ≥ 1.
   - Circularity: no premise mentions the jets, their gap or self-duality.
9. **Highest-leverage next moves.**
   - `ConfluentProfiles` (confluent Vandermonde determinant of the normalized jets; reflection removed).
   - `FiniteSpanSeparation`.
   - J5.2/MS1.
   - The remaining `Consumers`.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal, facade and
registration, the parent-extension wrapper, canonical regeneration (`rhkg-compiler-receipt`), CI on
the published head, the 10 absent roots, RH, Step 4 and the independent closing inequalities.
