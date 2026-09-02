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

**Status:** PROJECT FIREWALL; PARTIAL ESCAPE PROVED BY PR #98; COMPRESSION REMAINS OPEN.

PR #96 proves a unit constrained negative witness on the raw function type. That norm remains a valid homogeneous scale normalization but is not the Euclidean/PiLp₂ norm used by Hilbert/Rayleigh APIs.

PR #98 separately proves coordinate transport to EuclideanSpace, the Euclidean constrained subspace with the same three moments, the exact quadraticForm / Euclidean inner-self identity, and off-line zero -> nonzero Euclidean constrained negative direction.

Still open:

~~~text
orthogonal compression of canonicalSourceMatrix.toEuclideanLin to the constrained subtype
finite-dimensional constrained Rayleigh/eigenmode extraction
~~~

Do not use the raw #96 norm-one statement as a Euclidean sphere theorem. Conversely, do not continue to describe the coordinate/subspace/quadratic bridge as open after #98.

Future finite-N zero-extension isometry must be proved directly in EuclideanSpace; the raw function-space norm is not a shortcut.

