# RHRC formal audit — theorem authority through PR #125; control authority through PR #117

> **RH remains OPEN.**

## Current authority split

```text
live main after #125 = 615437fd5854b4473471d9826b4d4787b2e8e42f
live main tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427

theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
theorem tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427
theorem-bearing merged through = PR #125
E4-A2 zero-shift kernel/range dichotomy + strict regular endpoint = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. The exact #125 theorem head passed the RHRC/Lean and Permansson workflows before merge.

## PR #112 — FIRST-BAD-RIGIDITY-D1

**PROVED:** global first badness; predecessor parities nonnegative below first bad size; intrinsic predecessor `W`; one-step shell `S` with `finrank S=1`; predecessor plus shell spanning; first-bad negative eigenmode with nonzero shell content; exact cubic parity-defect factorization; ExceptionalZero packaging at one common finite state.

## PR #113 — FIRST-BAD-RIGIDITY-D2

**PROVED:** canonical complementary decomposition `V=W⊕S`; predecessor/shell projections and orthogonality; projected predecessor block `A=P_W T|_W`; shell coupling; predecessor nonnegativity descends to `A`; for every real `lam<0`, `A-lam I` is bijective; canonical shifted resolvent; predecessor reconstruction; basis-free shifted Schur identity.

**Not proved:** shell invariance, `A^-1` at zero, strict predecessor positivity, root exclusion, RH.

## PR #115 — FIRST-BAD-RIGIDITY-E1

**PROVED:** canonical cubic successor direction is not inherited from the predecessor; `intrinsicCubicShellPart p N != 0` in the stated nontrivial range; the global first-bad state forced by an off-line zero carries both a nonzero negative-mode shell coordinate and a nonzero canonical cubic shell coordinate.

## PR #118 — FIRST-BAD-RIGIDITY-E2

**PROVED:** canonical shell coordinate, exact shell reconstruction, faithful quotient coordinate with predecessor kernel, normalized genuine negative eigenmode with shell part exactly `intrinsicCubicShellPart`, and identification of the odd cubic parity-defect coefficient with the canonical quotient coordinate of the exact intertwining defect.

## PR #119 — FIRST-BAD-RIGIDITY-E3-A

**PROVED:** for every safe `lam<0` under predecessor nonnegativity, the canonical trial vector

```text
u_lam = -(A-lam I)^(-1) Bc + c
```

has quotient coordinate one; its residual has zero predecessor part; and

```text
cubicSecularScalar(lam)=0
  <-> full residual=0
  <-> canonical trial vector is a genuine eigenmode
  <-> exists nonzero eigenmode at lam.
```

A hypothetical off-line zero therefore forces a global-first-bad finite state with an exact negative root of this canonical scalar.

## PR #121 — FIRST-BAD-RIGIDITY-E3-B2

**PROVED:** for

```text
S(lam)=<Tc,c>-lam<c,c>-<R_lam Bc,Bc>,
```

#121 proves

```text
cubicSecularScalar(lam)=star(S(lam))/<c,c>
```

and exact zero equivalence between `S`, the canonical quotient scalar, the canonical trial eigenmode and existence of a nonzero eigenmode.

## PR #122 — FIRST-BAD-RIGIDITY-E3-B1 / E4-A1

**PROVED — metric layer:** projected predecessor symmetry; shifted symmetry/coercivity; resolvent norm/quadratic bounds; shifted-resolvent symmetry; real/nonnegative resolvent quadratic value; realness of `S`; unconjugated exact bridge

```text
cubicSecularScalar(lam)=S(lam)/<c,c>;
```

and the first denominator-free root metric restriction.

**PROVED — E4-A1:** for `z∈ker A`, the full successor image lies in the one-dimensional shell and

```text
<z,Bc> = star(kappa(Tz)) <c,c>,
Az=0 -> (<z,Bc>=0 <-> Tz=0).
```

This classifies zero resonance; it does not choose a branch.

## PR #124 — FIRST-BAD-RIGIDITY-E4-A2

Exact theorem head: `75d015251b2792dcad65536f73d0b0dbbe95b00b`.
Merged main: `9b720dbcb3059ef8d114cebf803fe325e224f0b3`.

**PROVED — kernel/range geometry:**

```text
range A ⟂ ker A
range A ∩ ker A = {0}
W = ker A ⊕ range A.
```

**PROVED — decoupled branch:** if `b` annihilates `ker A`, then `b∈range A`, so there exists `x0` with `Ax0=b`; moreover

```text
Ax=b and Ay=b -> <x,b>=<y,b>.
```

Thus the zero-shift quadratic coupling is canonical without any zero-shift inverse.

**PROVED — resonant branch:** for `z∈ker A`, `lam<0`,

```text
<z,b> = (-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

**PROVED — ExceptionalZero composition:** an off-line zero forces the same global-first-bad state into the exact decoupled/resonant branch classification.

## PR #125 — FIRST-BAD-RIGIDITY-E4-A2-ENDPOINT

Exact theorem head: `533beb4a42fc96cd43a97e071c6e07e3178872b6`.
Merged main: `615437fd5854b4473471d9826b4d4787b2e8e42f`.

**PROVED — canonical zero-shift endpoint:** for any decoupled solution `Ax0=b`, define

```text
S0=<Tc,c>-<x0,b>,
u0=-x0+c.
```

The endpoint is independent of the selected solution.

**PROVED — zero-shift critical geometry:** the predecessor coordinate of `T u0` is zero and

```text
<Tu0,u0>=S0.
```

**PROVED — complete square:** predecessor displacements satisfy the exact affine-fibre quadratic decomposition, so predecessor nonnegativity makes `Re S0` the constrained minimum on that fixed-shell fibre.

**PROVED — strict endpoint sign:** at the safe negative explicit secular root carried by the first-bad state,

```text
Re S0 < 0.
```

**PROVED — ExceptionalZero composition:** an off-line zero forces the same global-first-bad state into either the strictly negative regular endpoint branch or the unchanged quantitative resonant branch.

**Not proved:** exclusion of either branch, exact resonant pole decomposition, shell-response coefficient identity, negative-root exclusion, positivity, finite-to-infinite closure, RH.

## PR #117 — latest control-plane authority

**CI-VERIFIED CONTROL INFRASTRUCTURE:** Control-v2 hardening, typed deformation-budget steps, horizon-certificate requirement, decision-commutation checks, archaeology-path binding, deterministic routing transparency, theorem/control anchor separation.

PRs #118/#119/#121/#122/#124/#125 changed theorem state but did not change Control-v2 semantics. Therefore the separate control-plane anchor remains #117.

## Current formal state

```text
least/global bad + predecessor nonnegative + 1d shell                   PROVED
negative parity-compressed eigenmode                                    PROVED
canonical V=W⊕S                                                         PROVED
safe shifted predecessor resolvent for lam<0                            PROVED
canonical cubic shell/quotient coordinate                               PROVED / #118
exact quotient-secular root <-> eigenmode                               PROVED / #119
exact explicit Schur root bridge                                        PROVED / #121
projected predecessor symmetry / shifted coercivity                     PROVED / #122
resolvent quadratic realness / nonnegativity / bounds                   PROVED / #122
ker(A) cubic-coupling <-> successor-zero classification                 PROVED / #122
range/kernel decomposition of projected predecessor block               PROVED / #124
zero-shift solution + solution-independent quadratic coupling           PROVED / #124
exact resonant identity + denominator-free bound                        PROVED / #124
canonical zero-shift endpoint + exact complete square                   PROVED / #125
decoupled branch at negative secular root -> Re S0<0                    PROVED / #125
off-line zero -> strict endpoint OR resonant first-bad package          PROVED / #125

zero-shift shell-response coefficient                                   DERIVED / OPEN FORMALIZATION
exact resonant kernel-pole decomposition                                LEAD / OPEN FORMALIZATION
E4-A3 branch exclusion / branch rigidity                                OPEN
parity shifted-nullity difference <=1                                   DERIVED / OPEN FORMALIZATION
resolvent monotonicity / strict root uniqueness                         OPEN
quantitative positive-floor one-step inequality                         LEAD / OPEN FORMALIZATION
negative-root exclusion                                                  OPEN
positivity / finite-to-infinite closure                                  OPEN
RH                                                                        OPEN
```

## Current research frontier

### E4-A3 — branch rigidity

Regular branch: theoremize the exact one-dimensional shell response of `T u0` from the already-proved zero predecessor coordinate. Do not upgrade this to an eigenvector statement without proof.

Resonant branch: exploit #124's `ker A ⊕ range A` split to theoremize an exact `1/(-lam)` kernel-pole decomposition of the shifted resolvent.

Then compose both branches with parity rank-at-most-one structure, KKT normal-space geometry, cubic quotient data, first-bad minimality and exact N-flow. Generic Hermitian block systems admit both a negative Schur complement and zero resonance, so a contradiction must use genuinely CCM-specific structure.

### E4-B — parity shifted-nullity

Use only finite-dimensional rank/kernel algebra from the rank-at-most-one parity defect and algebraic `D`-equivalence. Do not import unitary interlacing.

### E3-C — resolvent identity / monotonicity

The exact root detector is real and explicit on `lam<0`, so strict monotonicity/root-count control remains admissible.

**Firewall:** at most one negative root is not negative-root exclusion.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- supporting theorem checks do not automatically imply machine claim promotion;
- `V=W⊕S` does not imply shell invariance;
- D is algebraic, not unitary/isometric;
- `ker A` is not the predecessor-size compressed-operator kernel;
- no whole-space or range-only `A^-1` at zero;
- `Re S0<0` is not branch exclusion;
- generic zero resonance is not automatically contradictory;
- `T u0∈S`, if proved, is not an eigenvector theorem;
- root uniqueness remains weaker than root exclusion;
- no source-normalization, promoted-binding, positivity, finite-to-infinite or RH change is implied by #124/#125.

Detailed current post-green implications: `research/RHRC/RESEARCH_LEADS_POST_125_DELTA.md`.

**RH remains OPEN.**