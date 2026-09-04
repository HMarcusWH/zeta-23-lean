# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

## OBS-001 — TightMult information wall

**Status:** FORMAL / UNCONDITIONAL.

At c=2, the inherited Zeta23 certificate based on trace, Frobenius norm, on-line multiplicity atoms and a positive-index bound is simultaneously extremal for an on-line double zero and a tight off-line pair.

**Escape requirement:** introduce a genuinely new information channel.

## OBS-002 — density-one is not RH

Any method insensitive to o(N) exceptional zeros cannot close RH.

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

**Consequence:** closing the remaining scalar arithmetic leg in that observable class is proving RH, not obtaining a cheap auxiliary estimate.

## OBS-009 — band-limited Weil-positivity wall

**Status:** classical design constraint; not fully formalized as a project theorem.

The R002 negative-index arithmetic leg is a band-limited Weil-positivity assertion. Requiring the whole relevant family restores RH-strength positivity.

## OBS-010 — finite formula identity is not an ambient restriction theorem

**Status:** PROJECT FIREWALL.

A theorem of the form

```text
finite source formula = matrix M
```

does not by itself prove

```text
QW_lambda restricted to E_N = M.
```

The latter additionally requires the correct carrier/function space, measure, source functional, normalization and restriction map.

**Origin:** repeated R003 source/normalization audits culminating in #71/#73.

**Escape requirement:** independently define the ambient source objects and prove the restriction theorem.

## OBS-011 — scalar-normalization spectral-sign firewall

**Status:** FORMAL STRUCTURAL CONSEQUENCE.

If

```text
A = M + cI,
```

then commutators, eigenvectors/eigenspaces and eigenvalue gaps transport, but absolute eigenvalues and sign-sensitive quantities shift.

Therefore legacy `finiteMatrix` numerical inertia/PSD/lower-bound evidence cannot be promoted to canonical source spectral evidence.

**Escape requirement:** run/prove sign-sensitive claims on `canonicalSourceMatrix` or transport them with an explicit proved scalar-shift theorem and threshold bookkeeping.

## OBS-012 — function-level E_N is not bundled L2/form-domain E_N

**Status:** PROJECT FIREWALL.

A formula-level or zero-extended function representing the finite source Fourier span is not automatically an element/subspace of the exact `L2(d*u)` or form domain used by the external source theorem.

**Escape requirement:** close the measure/Hilbert/form-domain interface explicitly.

## OBS-013 — source-display reconciliation is a theorem obligation

**Status:** PROJECT FIREWALL.

Different displays or derived rewrites in a source may encode distinct normalizations. Agreement with one source formula, one executable, or one numerical oracle does not authorize relabeling another display.

**Origin:** the direct equation-(4.4) versus later printed equation-(4.11)/(4.14) CCM normalization seam.

**Escape requirement:** pin the source convention, formalize both sides where material, prove the reconciliation or quarantine the suspect rewrite.

## OBS-014 — PR numbers are not mathematical dependencies

**Status:** DOCUMENTATION / GOVERNANCE.

Roadmaps repeatedly diverged from predicted PR numbering as proof results compressed or split dependencies.

**Consequence:** stable route documentation must use semantic work-package IDs (G1-B1B, G23, S-GEOM, S-NEG, etc.). PR numbers are historical execution references only.

## OBS-015 — source interface is not source negativity

**Status:** PROJECT FIREWALL.

A theorem defining or identifying the source functional, such as

```text
QW(kappa f,kappa g) = PsiSharp(F)
```

or the finite restriction

```text
QW_lambda|E_N = canonicalSourceMatrix
```

does not by itself transport the project theorem

```text
Re W(h,h) < 0
```

into a strict negative value of the independently defined source `QW`.

**Origin:** repeated Codex review findings on the R003 source lane (#76/#78), preserved after the post-W1 route split.

**Consequence:** every source-faithful path to G23/F1 must display a separate sign entry.

**Escape requirement:** prove either

1. an independent fixed-aperture source theorem producing `inf QW_lambda < 0` from an off-line zero (`S-NEG`), or
2. an exact theorem composing the genuine W/localized-additive value with the independently defined source QW so strict negativity is preserved.

G1-B1B/G1-final alone do not discharge this obstruction.

## OBS-016 — raw periodic approximation is not hard-window legality

**Status:** PROJECT FIREWALL; PRIMARY R003 ESCAPE PROVED.

PR #91 proves uniform formula-level approximation by periodic finite localized Fourier functions on one fixed aperture. It does **not** by itself make the raw zero extension outside [0,L] globally C².

**Consequence:** do not apply the genuine Weil form to a raw hard-window approximant merely because its interior formula is smooth and uniformly close to the strict-collar target. The #88 correction by itself is also not an independently legal hard-window C² test.

**Primary-route escape:** PR #93 proves `Zeta23.CCM.exists_boundaryFlatFinite_WCONT_approx`, combining the exact #88 projection, F0-B1A legality, global derivative identities and fixed-aperture WCONT control.

**Permanent warning:** this closes the R003 primary-route obligation only. Do not infer legality for unrelated raw periodic approximants or for the correction vector alone.

## OBS-017 — raw function-space norm is not Euclidean Rayleigh normalization

**Status:** PROJECT FIREWALL; PRIMARY ESCAPE CLOSED BY PR #107.

PR #96's raw norm remains distinct from the Euclidean/PiLp₂ norm. PR #98 closes the Euclidean carrier/quadratic bridge; PR #100 closes exact Euclidean N-flow; PR #107 proves orthogonal parity compression, exact compressed/self agreement, compressed symmetry and a negative constrained Rayleigh eigenmode.

**Permanent warning:** do not use the raw #96 unit vector as a Euclidean sphere theorem. #100 isometry still does not imply full compressed-operator intertwining; #110 later proves only a rank-at-most-one parity defect, not exact compressed intertwining.

## OBS-018 — merged source presence is not compiler validation

**Status:** PROJECT VALIDATION FIREWALL.

A `.lean` file existing, appearing in a PR, passing the no-placeholder grep, or being merged does not establish that its declarations elaborate.

**Origin:** PR #103 merged `Zeta23/CCM/ParityBadness.lean`, but the validated `lake build Zeta23.CCM` imported `ConstrainedParityGeometry.lean` and did not import `ParityBadness.lean`.

**Consequence:** declarations in an unbuilt/unimported file remain STAGED / NOT PROVED.

**Escape requirement:** put the module in an authoritative compiler-tested import/build closure or explicitly build it in an authoritative gate, then inspect the axiom surface where production promotion requires it.

The no-placeholder gate is syntactic hardening, not elaboration.

PR #110 illustrates a distinct follow-on rule: compiler validity and production axiom promotion are separate checks. Its final head was in the successful `Zeta23.CCM` import/build closure, but the last repair removed module-local `#print axioms` commands. The theorems are PROVED by compiler/CI; promoted claim registration still requires exact `#check/#print axioms` coverage in `ClaimBindings.lean`.

PRs #112/#113 reinforce the distinction: their declarations are compiler-authoritative because the exact CCM/ExceptionalZero build closure passed, while machine claim-promotion entries remain a separate control-plane action.

## OBS-019 — one-dimensional successor shell is not an invariant negative line

**Status:** PROJECT FIREWALL; INTRINSIC BLOCK-GEOMETRY ESCAPE CLOSED BY #112/#113.

Historical progression:

- #105 proved the ambient successor parity shell has complex finrank one;
- #107 proved a negative successor eigenmode is not inherited from the predecessor;
- #109 proved nonzero ambient orthogonal shell projection;
- #112 internalized predecessor W and shell S inside the exact successor parity subtype and proved `dim_C S=1` plus spanning;
- #113 proved W and S are complementary, exposed canonical projections, and proved the negative first-bad eigenmode has nonzero **canonical** shell coordinate.

Now PROVED:

```text
V = W ⊕ S,
dim_C S = 1,
intrinsicShellPart(v_bad) != 0,
intrinsicShellPart(x)=0 <-> x∈W.
```

Still not proved:

- the eigenmode is purely shell;
- the shell is invariant under the compressed canonical operator;
- D transports the shell orthogonally;
- negative index exactly one / unique negative eigenline as a separately formalized theorem.

**Consequence:** use the canonical direct-sum coordinates from #113, but do not silently replace the full eigenmode by a pure shell vector or invoke invariant-subspace spectral theory.

**Current escape target:** for shell-incidence questions, exploit `shellPart(x)=0 <-> x∈W`; prove non-membership in W rather than rebuilding ambient projection geometry.

## OBS-020 — exact one-channel parity factorization is not unitary rank-one perturbation theory

**Status:** PROJECT FIREWALL; FACTORIZATION ESCAPE CLOSED BY PR #112, NONZERO/METRIC ESCAPES OPEN.

#110 proved

```text
range(T_- D - D T_+) <= C g_N
finrank range(T_- D - D T_+) <= 1
```

with explicit nonzero `g_N=P_-d^3` for `N>=2`, plus the corresponding same-space algebraic conjugation bound.

#112 strengthens the operator description to an exact pointwise factorization

```text
F_N(v) = ell_N(v) • g_N
```

through the canonical `cubicDefectFunctional` and proves the algebraic pullback of the cubic generator is nonzero.

This still does **not** prove:

- `ell_N` is nonzero;
- the defect map is nonzero;
- exact rank one rather than rank zero or one;
- D or the induced equivalence is unitary/isometric;
- the conjugated odd compression is self-adjoint in the original even-sector inner product;
- Hermitian rank-one interlacing, equal spectra, inertia transfer or positivity.

**Consequence:** downstream work may use the exact one-channel algebraic identity, but must stay in algebraic rank/resolvent/kernel language unless a compatible metric theorem is separately established.

**Escape requirement:** prove `ell_N` nonzero only if actually needed and true; separately establish any metric compatibility before importing self-adjoint perturbation theory.

## OBS-021 — shifted Schur reduction is not a contradiction

**Status:** PROJECT FIREWALL; ORIGIN PR #113.

#113 proves the safe first-bad block reduction

```text
(A-lam I)w = -Bs,
w = -(A-lam I)^(-1)Bs,
<Ts,s> - lam<s,s> - <(A-lam I)^(-1)Bs,Bs> = 0
```

for the genuine negative first-bad eigenmode with `lam<0` and nonzero canonical shell coordinate.

This is a substantial reduction, but ordinary finite-dimensional Hermitian block systems with negative eigenvalues satisfy Schur/Feshbach identities of this type. The identity alone therefore does **not** prove positivity or exclude a negative eigenvalue.

What remains open:

- projected predecessor-block symmetry as a separate native theorem;
- quantitative shifted coercivity / resolvent positivity and monotonicity;
- cubic generator non-membership in the centered predecessor image;
- nonzero cubic intrinsic shell coordinate;
- identification of the cubic shell line with the negative-mode shell line;
- cubic-normalized scale-free secular rigidity;
- common even/odd resonance classification or exclusion.

**Current highest-value escape test:** cubic-shell incidence. Because #113 proves `intrinsicShellPart(x)=0 <-> x∈W`, show the cubic generator (and its algebraic even pullback) is not in W. A promising but unproved explicit route is the predicted formula

```text
g_K = d^3 - alpha_K d,
alpha_K = (3K^2+3K-1)/5,
(g_K)_(+K)=K(K-1)(2K-1)/5.
```

The formula must be derived from the exact repository projection/indexing conventions before use.

**Permanent warning:** uniqueness or monotonicity of a negative secular root is still not absence of a negative root. Additional CCM-specific shell/cubic/parity structure is required for an RH-directed contradiction.
