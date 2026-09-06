# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

> **Current theorem anchor:** merged PR #119, `d4175d2bb305e62863f593824b3f40e921a46ee6`.  
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

**Status:** PROJECT FIREWALL; FACTORIZATION CLOSED BY #112, CANONICAL QUOTIENT VISIBILITY PARTLY CLOSED BY #118, METRIC ESCAPES OPEN.

#110/#112 prove algebraic one-channel / rank-at-most-one parity defect structure and exact pointwise cubic factorization. #118 proves that on the odd successor carrier `cubicDefectFunctional` is literally the canonical quotient coordinate of the exact intertwining defect.

Still not proved:

- `cubicDefectFunctional` is nonzero on a specific input;
- exact defect rank one rather than rank zero-or-one;
- D is unitary/isometric;
- conjugated odd compression is self-adjoint in the original even-sector metric;
- Hermitian rank-one interlacing, equal spectra or inertia transfer through D.

**Current escape route:** use rank/kernel algebra for parity-nullity statements; establish metric compatibility separately before importing self-adjoint perturbation theory.

## OBS-021 — shifted Schur identity is not an exact secular criterion

**Status:** HISTORICAL BLOCKER CLOSED BY PR #119; PERMANENT GENERIC-SCHUR WARNING REMAINS.

PR #113 proved only the necessary first-bad identity

```text
(A-lam I)w = -Bs
w = -(A-lam I)^(-1)Bs
<Ts,s> - lam<s,s> - <(A-lam I)^(-1)Bs,Bs> = 0
```

for a genuine negative first-bad eigenmode.

PR #118 canonically normalized the shell to the cubic direction.

PR #119 closes the missing converse by constructing, for every safe `lam<0`, a canonical trial vector and full residual, then defining the secular scalar as the faithful quotient coordinate of that residual. It proves

```text
cubicSecularScalar(lam)=0
  <-> full residual = 0
  <-> exists nonzero eigenmode at lam.
```

Therefore the historical blocker “Schur identity only necessary” is closed.

**Permanent warning:** exact secular equivalence is still not a contradiction. Generic Hermitian block systems can have negative secular roots.

## OBS-022 — quotient secular scalar is not yet the explicit Schur scalar

**Status:** CURRENT FORMALIZATION OBSTRUCTION / POST-#119 FRONTIER.

PR #119 defines

```text
F(lam)=intrinsicCubicQuotientCoordinate(T u_lam - lam u_lam)
```

for the canonical shifted-resolvent trial vector.

The older canonical cubic-shell Schur expression is

```text
S(lam)=<Tc,c> - lam<c,c> - <R_lam Bc,Bc>.
```

Current Lean proves `S(lam)=0` for genuine negative eigenmodes and proves `F(lam)=0` iff a genuine eigenmode exists. It does **not yet** prove a pointwise identity between `F` and the correctly normalized `S` for every safe negative shift.

**Escape requirement:**

1. prove projected predecessor symmetry in the exact repository inner product;
2. prove shifted resolvent symmetry / real quadratic values;
3. handle Mathlib's complex inner-product orientation exactly;
4. theoremize the pointwise normalized identity.

**Consequence:** do not transfer sign, reality or monotonicity from the explicit Schur expression to `cubicSecularScalar` until this bridge is green.

## OBS-023 — predecessor nonnegativity permits zero resonance

**Status:** CURRENT STRUCTURAL OBSTRUCTION / POST-#119 FRONTIER.

Global-first-bad gives

```text
Re <Aw,w> >= 0,
```

not a positive lower spectral gap.

Thus `ker A` may be nontrivial. Although `A-lam I` is safely invertible for `lam<0`, the shifted resolvent can have a `1/(-lam)` singular component as `lam -> 0-`.

**Fast structural test:** determine whether the canonical shell coupling `b=Bc` annihilates the zero eigenspace:

```text
z in ker A -> <z,b>=0 ?
```

If yes, the singular zero eigenspace decouples from the secular channel. If no, the resonant singular contribution may itself constrain negative roots.

**Parallel escape route:** use the existing same-space parity defect with finrank at most one to theoremize shifted-nullity comparison and classify simultaneous/zero resonance without assuming D is unitary.

## OBS-024 — root uniqueness is not root exclusion

**Status:** PERMANENT CLAIM FIREWALL.

Even if a later E3-C theorem proves the canonical real secular function is strictly monotone and has at most one negative root, a single negative root may still exist.

**Escape requirement:** use additional CCM-specific information — shell/cubic/parity/KKT/N-flow structure, endpoint sign information, zero-resonance constraints, or an equivalent rigidity theorem — to exclude the remaining root.

`at most one negative root` must never be documented as positivity or RH.

**RH remains OPEN.**