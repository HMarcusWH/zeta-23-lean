# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

> **Current theorem anchor:** merged PR #129, `e1192857afed9f68fa4a13143ce690b62191b997`.  
> **Validated theorem head:** `440be3e5b6bf05e94ae2c65b1704d52d20acc9af`.  
> **Validated theorem tree:** `2f042a3b0b3313e7c67d627a58a32d579d4e7ff7`.  
> **Claim firewall:** RH remains OPEN.

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

**Status:** PROJECT FIREWALL; FACTORIZATION CLOSED BY #112; QUOTIENT VISIBILITY CLOSED BY #118; SOURCE-EXPLICIT DEFECT COEFFICIENT CLOSED BY #129; METRIC TRANSFER THROUGH D STILL OPEN.

#110/#112 prove algebraic one-channel / rank-at-most-one parity defect structure and exact pointwise cubic factorization. #118 identifies the odd cubic defect coefficient with the canonical quotient coordinate. #129 proves the coefficient is exactly the canonical-source quadratic normal moment

```text
cubicDefectFunctional L K v
  = evenQuadraticSourceMoment L K v
  = <n2, canonicalSourceMatrix(L,K)v>/<n2,n2>.
```

Still not proved:

- useful sign or nonzeroness of this moment on the canonical first-bad trial vector;
- exact defect rank one rather than rank zero-or-one;
- D is unitary/isometric;
- conjugated odd compression is self-adjoint in the original even-sector metric;
- Hermitian rank-one interlacing, equal spectra or inertia transfer through D.

**Current escape route:** use #129 to spend actual canonical-source information. Do not import metric perturbation theory through D.

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

**Status:** CURRENT STRUCTURAL OBSTRUCTION; CLASSIFICATION/POLE INFRASTRUCTURE CLOSED THROUGH #128; SOURCE-SPECIFIC RESONANT EXCLUSION OPEN.

Global-first-bad gives `Re <Aw,w> >= 0`, not a positive lower spectral gap. Thus `ker A` may be nontrivial.

The theorem chain now gives:

```text
#122: Az=0 -> (<z,b>=0 <-> Tz=0)
#124: W=ker A⊕range A; exact resonant identity/bound
#125: canonical regular endpoint with Re S0<0
#127: exact special shell response
#128: canonical kernel coordinate K;
      k=K(b)=0 in the decoupled branch;
      k!=0 in the resonant branch;
      (-lam)K(R_lam b)=k.
```

The old escape split “construct the endpoint / theoremize the pole” is closed. The surviving obligation is source-specific:

1. show whether the actual canonical source formula can support `k=0`, `Re sigma0<0` and the #129 parity transfer simultaneously;
2. show whether it can support `k!=0`, the exact pole and the same parity transfer simultaneously.

**Semantic firewall:** `ker A` is the kernel of the projected successor predecessor block. It is not identified with the kernel of the predecessor-size compressed operator.

## OBS-024 — root uniqueness is not root exclusion

**Status:** PERMANENT CLAIM FIREWALL.

The exact root detector has a real explicit scalar representation, so strict monotonicity/root-count control is a legitimate theorem target. Even if E3-C proves at most one negative root, a single negative root may still exist — and a hypothetical off-line zero already forces one.

`at most one negative root` must never be documented as positivity or RH.

## OBS-025 — negative zero-shift endpoint / signed shell response is not a contradiction

**Status:** CURRENT PROJECT FIREWALL; EXPOSED BY #125 AND SHARPENED BY #127/#128.

The decoupled global-first-bad branch now has

```text
Re S0 < 0
S0 = star(sigma0)<c,c>
Re sigma0 < 0.
```

These are strict variational/response constraints, but generic Hermitian block systems with a nonnegative predecessor block can have a negative zero-shift Schur complement and a negative shell response. Therefore

```text
Re S0<0
Re sigma0<0
  != regular-branch exclusion
  != negative-root exclusion
  != positivity
  != RH.
```

Likewise, generic zero resonance may create negative spectrum rather than contradict it.

**Escape requirement:** use source information absent from the generic countermodels. PR #129 exposes the canonical source moment interface where that information can enter.

## OBS-026 — generic first-bad structural package is insufficient; actual canonical source values must do work

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / CURRENT DESIGN FIREWALL.

Post-#128 discovery countermodels show that increasingly rich generic structure can coexist with bad finite states:

- nonnegative predecessors with a negative regular Schur endpoint;
- exact zero resonance with a negative eigenvalue;
- actual centered-grid boundary-flat parity spaces with generic reversal-symmetric diagonal operators producing both-parity regular negativity, one-parity badness, or genuine resonance;
- reversal-symmetric diagonal perturbations preserving the displacement identity while altering the sign-sensitive successor state.

Exact rational discovery checks additionally support the #129 transfer architecture and show the predecessor correction in `D c+` is not optional.

These fixtures are **EXPERIMENTAL SIGNAL**, not Lean theorems, realizable zeta configurations or counterexamples to `canonicalSourceMatrix`.

**Consequence:** a proposed contradiction based only on Hermitianity, first-bad minimality, parity, KKT, rank-at-most-one defect, shell response, resonance classification or displacement structure is not credible unless it identifies an additional invariant the fixtures do not preserve.

**Current escape requirement:** theoremize a property of the actual `canonicalSourceMatrix` source formula — most directly through the #129 quadratic source moment, its overlap coefficient, or a composition with the branch/pole data — that invalidates the generic fixtures.

**RH remains OPEN.**