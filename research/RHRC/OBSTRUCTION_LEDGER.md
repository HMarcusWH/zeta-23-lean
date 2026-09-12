# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

> **Current theorem anchor:** merged PR #155, `7bd3f1028d42272fcadc347c43371b992d9c0bd7`.  
> **Validated theorem head:** `ecfd075c07923e6fc80ab1a5b4f2d49c724f5577`.  
> **Validated theorem tree:** `9a4f21ed55aa0cbdf54527164c2f5f96912c65de`.  
> **Claim firewall:** RH remains OPEN.

Historical obstruction origins below retain the PR number at which they were discovered/classified. A later theorem may close an escape without deleting the reusable warning.

## OBS-001 — TightMult information wall

**Status:** FORMAL / UNCONDITIONAL.

At `c=2`, the inherited Zeta23 certificate based on trace, Frobenius norm, on-line multiplicity atoms and a positive-index bound is simultaneously extremal for an on-line double zero and a tight off-line pair.

**Escape requirement:** introduce a genuinely new information channel.

## OBS-002 — density-one is not RH

Any method insensitive to `o(N)` exceptional zeros cannot close RH.

## OBS-003 — conditional support > 1

Routes requiring conjectural prime-pair / pair-correlation input remain conditional until that ancestry is independently discharged.

## OBS-004 — pointwise cancellation hazard

A single exponentially growing summand does not imply growth of the magnitude of the total residual. Cancellation must be controlled.

## OBS-005 — FFBBP target leakage

RUN_36 used target-dependent cost in association. Permanent regression fixture.

## OBS-006 — FFBBP source-side false-field bias

RUN_37 removed target leakage but still produced a field in a known-null world. Unknown-field discovery requires known-null suppression and matched controls.

## OBS-007 — window artifact

RUN_41 `curvature_gap` lost to a matched W96 adversarial null and failed the predeclared transfer condition.

## OBS-008 — scalar prime-upper equivalence wall

**Status:** FORMAL / UNCONDITIONAL (Lean).

The R001 scalar target `ArithmeticSideSubexponential` is logically equivalent to RH.

**Consequence:** closing that scalar arithmetic leg in the same observable class is proving RH, not obtaining a cheap auxiliary estimate.

## OBS-009 — band-limited Weil-positivity wall

**Status:** classical design constraint; not fully formalized as a project theorem.

The R002 negative-index arithmetic leg is a band-limited Weil-positivity assertion. Requiring the whole relevant family restores RH-strength positivity.

## OBS-010 — finite formula identity is not an ambient restriction theorem

**Status:** PROJECT FIREWALL.

A theorem

```text
finite source formula = matrix M
```

does not by itself prove

```text
QW_lambda restricted to E_N = M.
```

The latter additionally requires the correct carrier/function space, measure, source functional, normalization and restriction map.

**Origin:** repeated R003 source/normalization audits culminating in #71/#73.

## OBS-011 — scalar-normalization spectral-sign firewall

**Status:** FORMAL STRUCTURAL CONSEQUENCE.

If `A=M+cI`, commutators, eigenvectors/eigenspaces and eigenvalue gaps transport, but absolute eigenvalues and sign-sensitive quantities shift.

Therefore legacy `finiteMatrix` numerical inertia/PSD/lower-bound evidence cannot be promoted to canonical source spectral evidence.

## OBS-012 — function-level E_N is not bundled L2/form-domain E_N

**Status:** PROJECT FIREWALL.

A formula-level or zero-extended function representing the finite source Fourier span is not automatically an element/subspace of the exact `L2(d*u)` or form domain used by an external source theorem.

## OBS-013 — source-display reconciliation is a theorem obligation

**Status:** PROJECT FIREWALL.

Different source displays can encode distinct normalizations. Agreement with one source formula, executable or numerical oracle does not authorize relabeling another display.

**Origin:** direct equation-(4.4) versus later printed equation-(4.11)/(4.14) CCM normalization seam.

## OBS-014 — PR numbers are not mathematical dependencies

**Status:** DOCUMENTATION / GOVERNANCE.

Roadmaps repeatedly diverged from predicted PR numbering as proof results compressed or split dependencies.

**Consequence:** stable route documentation should use semantic work-package IDs; PR numbers are execution history.

## OBS-015 — source interface is not source negativity

**Status:** PROJECT FIREWALL.

A theorem defining or identifying the source functional does not by itself transport the project theorem `Re W(h,h)<0` into a strict negative value of an independently defined source `QW`.

**Escape requirement:** separately prove source negativity or an exact sign-preserving composition theorem.

## OBS-016 — raw periodic approximation is not hard-window legality

**Status:** PROJECT FIREWALL; PRIMARY R003 ESCAPE PROVED.

PR #91 proves uniform formula-level approximation by periodic finite localized Fourier functions on one fixed aperture, but not global hard-window `C²` legality for the raw zero extension. PR #93 closes the primary route with `exists_boundaryFlatFinite_WCONT_approx`.

**Permanent warning:** do not infer legality for unrelated raw periodic approximants or for the correction vector alone.

## OBS-017 — raw function-space norm is not Euclidean Rayleigh normalization

**Status:** PROJECT FIREWALL; PRIMARY ESCAPE CLOSED BY PR #107.

PR #98 closes the Euclidean carrier/quadratic bridge, #100 closes exact Euclidean N-flow, and #107 proves orthogonal parity compression, compressed/self agreement, symmetry and a negative constrained Rayleigh eigenmode.

**Permanent warning:** #100 isometry does not imply full compressed-operator intertwining; #110 proves only a rank-at-most-one parity defect.

## OBS-018 — merged source presence is not compiler validation

**Status:** PROJECT VALIDATION FIREWALL.

A `.lean` file existing, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate.

**Origin:** PR #103 merged `ParityBadness.lean` without putting it in the validated `Zeta23.CCM` import/build closure; #105 later closed that gap.

**Permanent rule:** theorem validity requires exact compiler-tested closure. Machine claim promotion is a separate surface and may require explicit binding/axiom checks.

## OBS-019 — one-dimensional successor shell is not an invariant negative line

**Status:** PROJECT FIREWALL; BLOCK-GEOMETRY ESCAPE CLOSED BY #112/#113; CANONICAL COORDINATE CLOSED BY #118; SPECIAL ZERO-SHIFT SHELL RESPONSE CLOSED BY #127.

Now PROVED:

```text
V = W ⊕ S
dim_C S = 1
intrinsicShellPart(v_bad) != 0
intrinsicShellPart(x)=0 <-> x in W
canonical cubic shell vector c != 0
canonical shell coordinate reconstructs every s in S
canonical quotient coordinate vanishes exactly on W
for the decoupled zero-shift trial u0:
  T u0 = shellPart(T u0)
  sigma0*c = T u0
  S0 = star(sigma0)<c,c>.
```

Still not proved:

- the negative eigenmode is purely shell;
- the shell is invariant under the compressed canonical operator;
- `u0` is an eigenvector;
- D transports the shell orthogonally;
- negative index exactly one / unique negative eigenline as a separately formalized theorem.

**Consequence:** the old “theoremize shell response” escape is consumed. Future arguments may use the exact special response, but must not silently upgrade it to invariant-subspace spectral theory.

## OBS-020 — exact one-channel parity factorization is not unitary rank-one perturbation theory

**Status:** PROJECT FIREWALL; FACTORIZATION CLOSED BY #112; QUOTIENT VISIBILITY CLOSED BY #118; SOURCE-EXPLICIT DEFECT CLOSED BY #129; SOURCE DECOMPOSITION CLOSED BY #131; ZERO-SHIFT SOURCE TRANSPORT CLOSED BY #134; ABSOLUTE ENERGY CLOSED BY #136; SOURCE PAIRING/ONE-STEP DETERMINANT CLOSED BY #137; METRIC/UNITARY TRANSFER THROUGH D STILL UNPROVED AND UNNEEDED FOR THE CURRENT ROUTE.

The project now has exact algebraic defect/source transport, scalar-sensitive self-energy, complex source pairing and the denominator-free one-step determinant. None of these upgrades D to an isometry or transports Hermitian perturbation theory through D.

Still not proved:

- useful sign of the full canonical one-step determinant;
- exact defect rank one rather than rank zero-or-one;
- D is unitary/isometric;
- conjugated odd compression is self-adjoint in the original even-sector metric;
- Hermitian rank-one interlacing, equal spectra or inertia transfer through D.

**Current escape route:** spend actual canonical source normalization through the source-energy/discrepancy machinery. Do not import metric perturbation theory through D.

## OBS-021 — shifted Schur identity is not an exact secular criterion

**Status:** HISTORICAL BLOCKER CLOSED BY PR #119; PERMANENT GENERIC-SCHUR WARNING REMAINS.

PR #119 proves

```text
cubicSecularScalar(lam)=0
  <-> full residual = 0
  <-> exists nonzero eigenmode at lam.
```

**Permanent warning:** exact secular equivalence is still not a contradiction. Generic Hermitian block systems can have negative secular roots.

## OBS-022 — quotient secular scalar versus explicit Schur scalar

**Status:** HISTORICAL BLOCKER CLOSED BY PR #121/#122; PERMANENT REPRESENTATION WARNING REMAINS.

PR #121 identifies the quotient scalar with the conjugated explicit Schur scalar; #122 proves the symmetry/realness needed for

```text
F(lam)=S(lam)/<c,c>
```

on the safe negative-shift regime.

**Permanent warning:** the identity is theorem-backed only under its stated hypotheses. Do not treat the two definitions as globally definitionally identical.

## OBS-023 — predecessor nonnegativity permits zero resonance

**Status:** STRUCTURAL OBSTRUCTION; CLASSIFICATION CLOSED THROUGH #128; ZERO-SHIFT SOURCE COMPATIBILITY CLOSED BY #134; CONDITIONAL RESONANCE REMOVAL CLOSED BY #137; SELECTED RESONANCE REMOVED BY #150; CANONICAL SIGN THEOREM OPEN.

Global-first-bad gives `Re <Aw,w> >= 0`, not a positive lower spectral gap. Thus a generic first-bad predecessor may have nontrivial kernel.

For the current selected #150/#153 state, resonance is removed directly. The surviving obligation is the independent source-specific arithmetic sign.

**Semantic firewall:** `ker A` is the kernel of the projected successor predecessor block. It is not identified with the kernel of the predecessor-size compressed operator.

## OBS-024 — root uniqueness is not root exclusion

**Status:** PERMANENT CLAIM FIREWALL.

Strict monotonicity/root-count control may give at most one negative root. A hypothetical off-line zero already forces one. Root uniqueness remains weaker than root absence.

## OBS-025 — negative zero-shift endpoint / signed shell response is not a contradiction by itself

**Status:** PROJECT FIREWALL; EXPOSED BY #125, SHARPENED BY #127/#128/#134, REGULAR NEGATIVE CERTIFICATE CLOSED BY #150/#153; OPPOSING SIGN OPEN.

The current retained selected state can carry

```text
lam < 0
explicit Schur root = 0
A x0 = b
canonicalSourceChannelEnergy(c-x0) < 0.
```

Therefore

```text
retained exact negative energy
  != contradiction
  != negative-root exclusion
  != RH.
```

## OBS-026 — generic first-bad structural package is insufficient; actual canonical source values must do work

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / CURRENT DESIGN FIREWALL.

Post-#128 discovery countermodels show increasingly rich generic structure can coexist with bad finite states. They are experimental/synthetic fixtures, not canonical source or zeta counterexamples.

**Post-#155 consequence:** a proposed contradiction based only on Hermitianity, first-bad minimality, parity, KKT, shell response, regularity, displacement structure, cross-parity transfer or generic smoothing is still not credible. The current proof must spend the exact canonical arithmetic and complete transformed residual.

## OBS-027 — the #131 raw source moment is linear, so universal one-sided sign is unavailable

**Status:** DERIVED STRUCTURAL FIREWALL FROM PROVED #131 INTERFACE.

`explicitCanonicalSourceMoment L K v` is linear in `v`, hence negation/scalar covariance blocks universal one-sided sign on the whole vector space unless the functional vanishes identically.

**Consequence:** the later energy/Riesz route is quadratic/Hermitian and is not a revival of raw source-moment positivity.

## OBS-028 — factorwise cross-parity nonvanishing/sign is not structural

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / EXACT RATIONAL REGRESSION FIREWALL.

Exact rational centered-grid reversal-symmetric diagonal models realize `Gamma=0`, source moment zero/nonzero, `alpha=0`, negative coefficients and both source-moment signs while preserving the generic transfer package.

**Consequence:** no argument may divide by `alpha`, `Gamma`, overlap, source moment, `Gamma0`, or `mu(z)` without a separate theorem.

## OBS-029 — scalar-shift-invariant transfer data cannot locate the absolute spectral origin

**Status:** DERIVED STRUCTURAL FIREWALL; ABSOLUTE-ENERGY ESCAPE CLOSED BY #136, PAIRING/DETERMINANT INTERFACE CLOSED BY #137, SELECTED NEGATIVE ENERGY CLOSED BY #150/#153, OPPOSING SIGN OPEN.

Under simultaneous generic scalar shift `M -> M+tI`, `lambda -> lambda+t`, the old shifted transfer package can remain unchanged while the spectrum moves relative to zero.

The remaining question is the independent nonnegative sign under exact canonical arithmetic.

## OBS-030 — one-step domination is an exact certificate; its arithmetic truth remains open

**Status:** FORMAL CERTIFICATE / DECISIVE UNIVERSAL SIGN CONTENT OPEN.

PR #137 defines `canonicalOneStepDomination` and proves its sufficiency for the desired zero-shift sign / negative-root exclusion mechanism.

The missing mathematics is not sufficiency. It is canonical arithmetic truth. Under predecessor nonnegativity and a one-dimensional shell, simply restating successor positivity has no research information gain.

## OBS-031 — exact zero-shift transport is not factorwise or branch exclusion

**Status:** FORMAL POST-#134 CLAIM FIREWALL; UNCHANGED BY #155.

PR #134 proves direct zero-shift transfer and `Gamma0*mu(z)=0` under both preimage hypotheses. Later determinant/regularity/certificate/discrepancy/Riesz results do not license factorwise conclusions from that product law.

## OBS-032 — determinant reduction can become a tautological positivity restatement

**Status:** POST-#137 RESEARCH-GAIN FIREWALL; UNCHANGED BY #155.

With `A>=0` and a one-dimensional shell, the universal determinant conditions encode essentially the missing positivity of the one-step block extension. A proof that merely assumes successor PSD, assumes absence of the negative root, or rewrites the same block positivity under a new name is circular.

**Escape requirement:** identify a canonical arithmetic mechanism implied by premises available before the desired conclusion.

## OBS-033 — the global/selected sign-failure countercertificate is not a contradiction

**Status:** FORMAL CLAIM FIREWALL; RETAINED/SHARPENED THROUGH #153 AND REEXPRESSED BY #155.

PR #137 first exposed global sign failure alternatives. PR #150 selects a regular negative-energy state. PR #153 retains its complete ancestry and exact negative source-channel state. PR #155 supplies a legal generic Riesz representation but no opposing sign.

**Consequence:** RH remains OPEN until new mathematics proves the opposing sign on the exact forced state and the terminal RH wrapper is validated.

## OBS-034 — theorem-backed pole-prime cancellation must not be discarded silently

**Status:** FORMAL INTERFACE / POST-#153 RESEARCH-DESIGN FIREWALL; STRENGTHENED BY #155.

PR #153 proves

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy.
```

PR #155 then proves a legal conditional Riesz representation of that exact discrepancy without differentiating the prime staircase.

**Consequence:** a proposed proof that immediately returns to independent coarse pole and prime majorants, or replaces the exact Riesz-transformed pairing by unrelated loose envelopes, discards theorem-backed cancellation and must prove the loss harmless at the selected-residual scale.

## OBS-035 — even source-energy jets are proved; odd production jets remain a theorem obligation

**Status:** POST-#155 CLAIM / ROADMAP FIREWALL.

PR #155 proves production source-coordinate oddness and therefore all **even** endpoint derivatives vanish. It also proves even-parity `M3=0`.

It does **not** by itself prove the odd derivative cancellations required for the unconditional sixth/eighth-order Riesz specializations.

The generic #155 Riesz theorem still requires explicit hypotheses

```text
iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0
```

for every `1 <= j <= r`.

**Consequence:** production order 6/8 remains OPEN until the odd jets are theoremized. The derived D-transport/moment-prefix recursion is the current intended escape.

## OBS-036 — real contraction derivative transport is not complex production source-energy transport

**Status:** POST-#155 IMPLEMENTATION / CLAIM FIREWALL.

The existing derivative/contraction infrastructure contains real-coefficient helper theorems. Production `sourceAtomRealEnergy`, however, is the real part of a genuinely complex sesquilinear quadratic form.

Therefore a proof only for a real contraction API does **not** establish

```text
g_u''(omega)=-(2*pi)^2 g_(D u)(omega)
```

for arbitrary complex production trials.

**Required escape:** prove the entrywise second-derivative/rank-two identity including the diagonal; coerce it to the complex source matrix; contract against `conj(u_i)*u_j`; explicitly annihilate the correction with `sum u=0`; then identify the `D A D` quadratic form with the production energy of `indexMatrix *ᵥ u`.

**Consequence:** no silent real-to-complex transport in FB-03E.

**RH remains OPEN.**