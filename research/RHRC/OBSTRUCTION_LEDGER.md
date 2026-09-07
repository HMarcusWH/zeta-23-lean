# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

> **Current theorem anchor:** merged PR #122, `b2d1210902d430f3cdd3c24c2961ab843469b5d6`.  
> **Validated theorem head:** `9c8154e3ea7a5762f8e65d508dc68bb9246db869`.  
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

If

```text
A = M + cI,
```

then commutators, eigenvectors/eigenspaces and eigenvalue gaps transport, but absolute eigenvalues and sign-sensitive quantities shift.

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

PR #91 proves uniform formula-level approximation by periodic finite localized Fourier functions on one fixed aperture, but not global hard-window `C²` legality for the raw zero extension.

PR #93 closes the primary route with `exists_boundaryFlatFinite_WCONT_approx`.

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

**Status:** PROJECT FIREWALL; INTRINSIC BLOCK-GEOMETRY ESCAPE CLOSED BY #112/#113, CANONICAL COORDINATE ESCAPE CLOSED BY #118.

Now PROVED:

```text
V = W ⊕ S
dim_C S = 1
intrinsicShellPart(v_bad) != 0
intrinsicShellPart(x)=0 <-> x in W
canonical cubic shell vector c != 0
canonical shell coordinate reconstructs every s in S
canonical quotient coordinate vanishes exactly on W.
```

Still not proved:

- the eigenmode is purely shell;
- the shell is invariant under the compressed canonical operator;
- D transports the shell orthogonally;
- negative index exactly one / unique negative eigenline as a separately formalized theorem.

**Consequence:** use canonical `W⊕S` and cubic quotient coordinates; do not silently invoke invariant-subspace spectral theory.

## OBS-020 — exact one-channel parity factorization is not unitary rank-one perturbation theory

**Status:** PROJECT FIREWALL; FACTORIZATION CLOSED BY #112, CANONICAL QUOTIENT VISIBILITY PARTLY CLOSED BY #118, METRIC TRANSFER THROUGH D STILL OPEN.

#110/#112 prove algebraic one-channel / rank-at-most-one parity defect structure and exact pointwise cubic factorization. #118 proves that on the odd successor carrier `cubicDefectFunctional` is literally the canonical quotient coordinate of the exact intertwining defect.

Still not proved:

- `cubicDefectFunctional` is nonzero on a specific input;
- exact defect rank one rather than rank zero-or-one;
- D is unitary/isometric;
- conjugated odd compression is self-adjoint in the original even-sector metric;
- Hermitian rank-one interlacing, equal spectra or inertia transfer through D.

**Current escape route:** use rank/kernel algebra for parity-nullity statements; do not import metric perturbation theory through D.

## OBS-021 — shifted Schur identity is not an exact secular criterion

**Status:** HISTORICAL BLOCKER CLOSED BY PR #119; PERMANENT GENERIC-SCHUR WARNING REMAINS.

PR #113 proved only a necessary shifted Schur identity for a genuine negative first-bad eigenmode. PR #118 canonically normalized the shell. PR #119 closes the missing converse by constructing, for every safe `lam<0`, a canonical trial vector and full residual, then defining the secular scalar as the faithful quotient coordinate of that residual. It proves

```text
cubicSecularScalar(lam)=0
  <-> full residual = 0
  <-> exists nonzero eigenmode at lam.
```

**Permanent warning:** exact secular equivalence is still not a contradiction. Generic Hermitian block systems can have negative secular roots.

## OBS-022 — quotient secular scalar versus explicit Schur scalar

**Status:** HISTORICAL BLOCKER CLOSED BY PR #121/#122; PERMANENT REPRESENTATION WARNING REMAINS.

PR #119 defines

```text
F(lam)=intrinsicCubicQuotientCoordinate(T u_lam - lam u_lam).
```

The explicit cubic Schur scalar is

```text
S(lam)=<Tc,c> - lam<c,c> - <R_lam Bc,Bc>.
```

PR #121 proves the exact pointwise identity

```text
F(lam)=star(S(lam))/<c,c>
```

for the safe negative-shift regime, with `<c,c> != 0`.

PR #122 proves the required projected symmetry/resolvent metric facts and realness of `S`, so the bridge sharpens to

```text
F(lam)=S(lam)/<c,c>.
```

The old obstruction to transferring real scalar analysis to the exact #119 root detector is therefore closed.

**Permanent warning:** the identity is theorem-backed only under its stated safe negative-shift/predecessor-nonnegativity hypotheses. Do not treat the two definitions as globally definitionally identical.

## OBS-023 — predecessor nonnegativity permits zero resonance

**Status:** CURRENT STRUCTURAL OBSTRUCTION; E4-A1 CLASSIFICATION CLOSED BY PR #122, BRANCH OUTCOME OPEN.

Global-first-bad gives

```text
Re <Aw,w> >= 0,
```

not a positive lower spectral gap. Thus `ker A` may be nontrivial. Although `A-lam I` is safely invertible for `lam<0`, the shifted resolvent can have a `1/(-lam)` singular component as `lam -> 0-`.

PR #122 proves the exact pointwise classification for

```text
A=P_W T|_W,
b=Bc:
```

```text
Az=0 -> (<z,b>=0 <-> T_(N+1) z=0).
```

It also proves the quantified equivalence

```text
b annihilates ker A
  <-> every z in ker A is already a genuine successor zero mode.
```

This is **not** a theorem that the coupling vanishes. The actual first-bad state may lie on either side.

**Current escape split:**

1. **Decoupled branch:** prove `b ⟂ ker A -> b ∈ range A` using finite-dimensional symmetry, obtain some `x0` with `Ax0=b`, and build a solution-based zero-shift endpoint without `A^-1`.
2. **Resonant branch:** from a witness `z∈ker A` with `<z,b>!=0`, theoremize the zero-eigenspace contribution to `R_lam b` and its effect on `S(lam)` near `0-`.
3. **Parallel:** use the same-space parity defect with finrank at most one for shifted-nullity comparison without unitary assumptions on D.

**Semantic firewall:** `ker A` is the kernel of the projected successor predecessor block. It is not identified with the kernel of the predecessor-size compressed operator.

## OBS-024 — root uniqueness is not root exclusion

**Status:** PERMANENT CLAIM FIREWALL.

After #122 the exact root detector has a real explicit scalar representation, so strict monotonicity/root-count control is now a legitimate theorem target. Even if E3-C proves at most one negative root, a single negative root may still exist.

**Escape requirement:** use additional CCM-specific information — shell/cubic/parity/KKT/N-flow structure, endpoint sign information, zero-resonance constraints, or an equivalent rigidity theorem — to exclude the remaining root.

`at most one negative root` must never be documented as positivity or RH.

**RH remains OPEN.**