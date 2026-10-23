# Stage 10: the logarithmic Fourier-Sobolev calculus (R2-S1b, F1, F2, F3)

This stage starts from the Stage 9 record `426ab786d0899b054e4851d550cb016a494785bd`. Stages 9
and 10 are published in one push. The source commit checked here is
`6a796f867f75e4ea59ac7aa6e4ddafe2540194c1` (tree `e95cb9f22663d9a69ed51c551f217391e0102b77`).
Exact hashes, commands and logs are in
[stage10 STATUS.json](evidence/current-codex/stage10/STATUS.json). All 100 original roots and 28
acceptance units remain required. RH, Step 4 and the independent closing inequalities remain
OPEN. No frozen specification, PDF, parent mathematical source or optional-amendment status
changed, and no existing Lean source changed.

The new module `Zeta23/OPICAFollowup/LogFourierSobolev.lean` imports exactly one project module,
`Zeta23.OPICAFollowup.ComplexLocalMeasures`. That is its BUILD_MANIFEST
`direct_project_imports` entry; all other imports are Mathlib modules. All four required
definitions exist:
- `logFourier`, the e^(-iξt) transform with no 2π in the phase;
- `logUnitary`, (U h)(t) = e^(t/2) h(e^t);
- `LogFormDomain`;
- `logForm` = ∫_0^∞ x²|h'|².

The narrow runner now builds twelve modules and replays seventeen consumer files.

## Completed narrow gates (local, pinned Linux compiler, committed source)

| Original root | Established | Evidence |
| --- | --- | --- |
| `log_unitary_form_identity` (R2-S1b, F1-F3) | For the actual form domain (h a primitive of a measurable, locally integrable h' on (0, ∞), h and x h' in L²(0, ∞)):<br>- U h is an L² isometry onto L²(ℝ) (unitary conversion);<br>- U h is the primitive of U'h(t) = e^(t/2)(h(e^t)/2 + e^t h'(e^t)) on every interval (weak derivative), with U'h ∈ L²(ℝ) and U h ∈ H¹(ℝ);<br>- ∫_0^∞ x²\|h'\|² = ∫\|ψ'\|² + (1/4)∫_0^∞\|h\|². | [ExpectedLogFourierSobolev.lean](consumers/ExpectedLogFourierSobolev.lean) (10 receipts) |
| `log_fourier_plancherel` (R2-S1b, F1-F3) | - The e^(-iξt) convention, with exact conversion 𝓕_log f(ξ) = 𝓕 f(ξ/(2π)) to the pinned Mathlib transform.<br>- Plancherel ∫\|f\|² = (1/(2π))∫\|𝓕_log f\|² on L¹ ∩ L².<br>- Differentiation 𝓕_log(f') = iξ 𝓕_log f.<br>- The H¹ norm with spectral weight a(ξ) = ξ² + 1/4.<br>- The continuous H⁻¹-H¹ pairing ∫ w (φ' - φ/2) of the actual force -(∂ + 1/2) w, with constant ‖w‖₂ and the exact identity ‖φ' - φ/2‖₂² = ‖φ'‖₂² + ‖φ‖₂²/4. | same file |

**Proofs.**
- **Boundary terms.** For 0 < a ≤ b, the absolutely continuous FTC (Mathlib, applied to real and
  imaginary parts) gives ∫_a^b (\|h\|² + 2x Re(conj h h')) = b\|h(b)\|² - a\|h(a)\|². The right
  side has limits at 0 and ∞ because the integrand is integrable. A nonzero limit L would force
  \|h(x)\|² ≥ L/(2x) near that end, contradicting integrability. So the boundary terms vanish
  without any decay assumption.
- **Unitarity and the form identity.** Both follow from the substitution x = e^t on all of ℝ.
- **Plancherel.** The L¹ ∩ L² Plancherel identity was not in the pinned Mathlib. It is derived
  in three steps: Mathlib's L² Fourier transform agrees with the tempered-distribution
  transform; the multiplication formula identifies that distribution with the integral
  transform; uniqueness against smooth compactly supported tests makes the identification
  almost everywhere, after which the L² isometry applies.
- **Cross term on the line.** The same two-sided boundary argument on ℝ gives
  ∫ Re(conj φ φ') = 0 for φ ∈ H¹(ℝ).

**Recorded formalization choices (no premise added, no domain narrowed).**
- "Actual form domain": a primitive representation h(b) - h(a) = ∫_a^b h' for all a, b > 0,
  with h' measurable and integrable on compact subintervals, h ∈ L²(0, ∞) and x h' ∈ L²(0, ∞).
  This is local absolute continuity together with the form-domain conditions. The derivative is
  a measurable representative: the form depends on h' only almost everywhere.
- "Weak derivative statement": U h is the primitive of U'h on every interval, which is the
  W^(1,1)_loc characterization. The distributional test-function form is not separately
  restated.
- H¹(ℝ) is realized by `LogH1` (primitive representation with φ, φ' ∈ L²).
- The force pairing is ∫ w (φ' - φ/2) for w ∈ L². No exponentially growing summand of the force
  is transformed separately.

The narrow runner reports `PASS_NARROW_ONLY` with a clean tree for twelve modules and seventeen
consumer files. The W04/W07 (52) and W06 (14) workflow consumers pass unchanged. Eight negative
controls are rejected for their intended reasons:
- form boundary term -1/4;
- unitary without the e^(t/2) weight;
- convention 𝓕 f(ξ) instead of 𝓕 f(ξ/(2π));
- Plancherel factor 1;
- derivative factor 2πiξ;
- weight ξ² + 1;
- force shift φ' + φ/2;
- Plancherel without the L² hypothesis.

The ledger now records 41 historical, 30 narrow and 29 absent roots. This is not aggregate
acceptance of 71 roots.

## Post-Green Research Pass

1. **Formally true (narrow, committed source).** The two roots above, with the generic
   supporting results:
   - `energy_identity_real` (boundary vanishing on the half-line);
   - `LogFormDomain.energy_identity`;
   - `integral_norm_sq_fourier_of_mem` (L¹ ∩ L² Plancherel, new relative to the pinned
     Mathlib);
   - `LogH1.cross_term`, `LogH1.force_pairing_bound` and `logH1_fourier_norm`.

   All receipts are standard-only. The consumer proves:
   - `expected_zero_profile_in_form_domain`: at an actual zero, the zero profile with its
     explicit right derivative lies in `LogFormDomain`;
   - consequently the paper's (S1.5), ∫_0^∞ x²\|h_κ'\|² = ∫\|ψ'\|² + (1/4)∫_0^∞\|h_κ\|², holds for
     actual zero profiles;
   - the two roots are compatible: the H¹ shift norm of U h equals the log form of h.
2. **Workflow harvest.** Stages 9 and 10 are published in one push, so the latest harvested head
   is `eacba23f`
   ([stage9 harvest](evidence/current-codex/stage9/ci-harvest-eacba23f.json)). All OPICA
   preparation, subset, narrow and regression jobs PASS there, as do all eighteen research
   replays. Only the designed fail-closed gates are red. CI on the new head is pending at
   publication.
3. **What changed.** The log-Fourier side of F1-F3 now has a verified convention and Plancherel
   factor. The quadratic form of the zero profiles is formally the H¹ energy of U h_κ, and the
   profile chain reaches the forced Euler equation.
4. **Upstream.** Stage 9's x h' ∈ L² and h' = O(x^-2) are exactly what puts h_κ into the form
   domain. The Stage 8 expansion supplies both bounds.
5. **Downstream.**
   - `ForcedEuler`: both of its imports now exist. The cell Euler identity
     (x² S'_cell)' = -κ S_cell and the cell integration by parts are already proved in scratch.
     The atoms come from the Stage 9 jumps. The second root ("not a homogeneous operator
     vector") uses κ ≠ 0 and the now formal (S1.5).
   - `SawtoothForce` (imports LogFourierSobolev and ProfileEulerMaclaurin), DERIVED: (F1.3)
     ∫_0^∞ {x} x^(-s-1) dx = -ζ(s)/s follows in a few lines from Stage 8's
     ζ(s) = s/(s-1) - 1/2 - s ∫_1^∞ B₁ t^(-s-1). The pieces 1/(1-s) and 1/(2s) cancel exactly.
     (F1.2) 𝓕_log w(ξ) = -ζ(1/2+iξ)/(1/2+iξ) then follows from the substitution x = e^t and the
     convention proved here.
6. **Resurrected routes.** None. The Stage 6/7 complex-variation tools were not needed here.
7. **New RH-relevant clues (LEAD/HYPOTHESIS, not formal).**
   - DERIVED (informal): since \|iξ + 1/2\|² = a(ξ) = ξ² + 1/4, the H⁻¹ norm of the actual force
     𝔤 = -(∂+1/2)w for the weight a equals ‖w‖₂ exactly. The formal pairing bound above is the
     dual form of the same fact. By (F1.4) the square is
     log(2π) - γ_E. This is an exact, zero-free constant, the paper's "valid but not RH-closing"
     budget. It cannot separate on-line from off-line zeros, because it does not depend on them.
8. **Falsification checks.**
   - Numerical, independent of Lean (mpmath 1.3.0, not interval certified;
     [numerical-falsification.log](evidence/current-codex/stage10/numerical-falsification.log)):
     - a Gaussian reproduces the closed-form 𝓕_log and Plancherel with factor 1/(2π) to 12
       digits;
     - the paper's (F1.4) budget agrees across three routes: ‖w‖² = 1.2606614 from exact cell
       integrals; (1/2π)∫\|ζ(1/2+iξ)\|²/(ξ²+1/4) = 1.260668 (truncated at \|ξ\| < 400 with a
       mean-value tail); log(2π) - γ = 1.2606614.
   - The 2π-free convention and the 1/(2π) factor are confirmed against an arithmetic identity,
     not only by a self-consistency check.
   - Vacuity: the domain is non-degenerate (h = e^(-x), a consumer theorem). The zero-profile
     clause needs an actual zero.
   - Circularity: no zero hypothesis enters the module; the consumer uses it only through
     Stage 9.
9. **Highest-leverage next moves.**
   - `ForcedEuler` (forced Euler equation; not a homogeneous operator vector).
   - `SawtoothForce` (F1.1-F1.3 via the Stage 8 continuation formula).
   - `CoPoissonJets` and `SquareDefect`.
   - J5.2/MS1 and R2-S3 in parallel.

`NEXT_AGENT_PROMPT.md` was not updated in Stages 4 to 10 and carries older counts. README,
REMAINING_WORK, this handover and the ledger are current.

## Still OPEN

Aggregate current-source export, the full100 receipt production/replay and review seal,
facade and registration, the parent-extension wrapper, canonical regeneration
(`rhkg-compiler-receipt`), CI on the Stage 10 head, the 29 absent roots, RH, Step 4 and the
independent closing inequalities.
