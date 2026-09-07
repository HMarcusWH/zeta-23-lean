# RHRC formal audit — theorem authority through PR #122; control authority through PR #117

> **RH remains OPEN.**

## Current authority split

```text
live main after #122 = b2d1210902d430f3cdd3c24c2961ab843469b5d6
live main tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862

theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
theorem tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862
theorem-bearing merged through = PR #122
E3-B1 secular metric control + E4-A1 zero-resonance coupling classification = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. The exact #122 theorem head passed both `RHRC research and Lean checks` and `Permansson v0.1.6 formal verification`.

## PR #112 — FIRST-BAD-RIGIDITY-D1

**PROVED:** global first badness; both predecessor parities nonnegative below the first bad size; intrinsic predecessor `W`; intrinsic one-step shell `S` with `finrank S=1`; predecessor plus shell spanning; first-bad negative eigenmode with nonzero shell content; exact cubic factorization of the parity defect; ExceptionalZero packaging at one common finite state.

## PR #113 — FIRST-BAD-RIGIDITY-D2

**PROVED:** canonical complementary decomposition `V=W⊕S`; canonical predecessor/shell projections; predecessor/shell orthogonality; projected predecessor block `A=P_W T|_W`; shell coupling `B=P_W T|_S`; predecessor nonnegativity descends to `A`; for every real `lam<0`, `A-lam I` is bijective; canonical shifted resolvent; predecessor reconstruction; basis-free shifted Schur identity.

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

has nonzero quotient coordinate one; its full residual

```text
r_lam = T u_lam - lam u_lam
```

has zero predecessor part; and

```text
cubicSecularScalar(lam)=0
  <-> r_lam=0
  <-> u_lam is a genuine eigenmode
  <-> exists nonzero v, T v = lam v.
```

A hypothetical off-line zeta zero therefore forces a global-first-bad finite state with an exact negative root of this canonical scalar.

## PR #121 — FIRST-BAD-RIGIDITY-E3-B2

**PROVED:** define the explicit cubic Schur scalar

```text
S(lam)=<Tc,c>-lam<c,c>-<R_lam Bc,Bc>.
```

For the safe negative-shift regime, #121 proves

```text
cubicSecularScalar(lam) = star(S(lam)) / <c,c>
```

with `<c,c> != 0`, and exact zero equivalence between `S`, the canonical quotient scalar, the canonical trial eigenmode, and existence of a nonzero eigenmode.

**Boundary after #121:** realness/sign had not yet been transferred because the conjugation was still semantically relevant.

## PR #122 — FIRST-BAD-RIGIDITY-E3-B1 / E4-A1

Exact theorem head: `9c8154e3ea7a5762f8e65d508dc68bb9246db869`.

Merged main: `b2d1210902d430f3cdd3c24c2961ab843469b5d6`.

**PROVED — E3-B1 metric layer:**

- predecessor-block projection identities;
- `intrinsicPredecessorBlock_isSymmetric` in the induced ambient successor inner product;
- symmetry of `A-lam I` for real `lam`;
- negative-shift coercivity from predecessor nonnegativity;
- resolvent norm control, including `(-lam)||R_lam b|| <= ||b||` and quotient form;
- shifted-resolvent symmetry;
- real/nonnegative resolvent quadratic value;
- denominator-free quadratic estimate `(-lam) Re<R_lam b,b> <= ||b||^2`;
- realness of `cubicExplicitSchurScalar`;
- unconjugated exact bridge

  ```text
  cubicSecularScalar(lam)=S(lam)/<c,c>;
  ```

- at an exact negative root,

  ```text
  0 <= Re(<Tc,c>-lam<c,c>)
  (-lam) * Re(<Tc,c>-lam<c,c>) <= ||Bc||^2.
  ```

**PROVED — E4-A1 zero-resonance classification:**

For `z` in the kernel of the projected successor predecessor block `A=P_W T|_W`, the full successor image lies in the one-dimensional shell and the exact coupling coefficient satisfies

```text
<z,Bc> = star(kappa(Tz)) <c,c>.
```

Consequently

```text
Az=0 -> (<z,Bc>=0 <-> Tz=0).
```

The quantified theorem proves that `Bc` annihilates all of `ker A` iff every vector in `ker A` is already a genuine successor zero mode.

**Critical boundary:** #122 does not prove that this vanishing condition holds; it classifies the two possibilities.

**PROVED — ExceptionalZero composition:** a hypothetical off-line zero forces one common global-first-bad state carrying the explicit negative secular root, the real unconjugated scalar bridge, the first metric bound, and the pointwise E4-A1 kernel-coupling equivalence.

## PR #117 — latest control-plane authority

**CI-VERIFIED CONTROL INFRASTRUCTURE:** Control-v2 hardening, typed deformation-budget steps, horizon-certificate requirement, decision-commutation checks, archaeology-path binding, deterministic routing transparency, theorem/control anchor separation.

PRs #118/#119/#121/#122 changed theorem state but did not change Control-v2 semantics. Therefore the separate control-plane anchor remains #117.

## Current formal state

```text
least/global bad + predecessor nonnegative + 1d shell                   PROVED
negative parity-compressed eigenmode                                    PROVED
canonical V=W⊕S                                                         PROVED
safe shifted predecessor resolvent for lam<0                            PROVED
canonical cubic shell/quotient coordinate                              PROVED / #118
exact quotient-secular root <-> eigenmode                               PROVED / #119
exact explicit Schur root bridge                                        PROVED / #121
projected predecessor symmetry / shifted coercivity                    PROVED / #122
resolvent quadratic realness / nonnegativity / bounds                  PROVED / #122
quotient scalar = real normalized explicit Schur scalar                PROVED / #122
first denominator-free root metric bound                               PROVED / #122
ker(A) cubic-coupling <-> successor-zero classification                PROVED / #122
off-line zero -> same metric/resonance first-bad package               PROVED / #122

which E4-A1 branch holds at the actual first-bad state                  OPEN
zero-shift range/endpoint theorem without A^-1                          OPEN
parity shifted-nullity difference <=1                                  DERIVED / OPEN FORMALIZATION
resolvent monotonicity / strict root uniqueness                         OPEN
quantitative positive-floor one-step inequality                         LEAD / OPEN FORMALIZATION
negative-root exclusion                                                 OPEN
positivity / finite-to-infinite closure                                 OPEN
RH                                                                       OPEN
```

## Current research frontier

### E4-A2 — zero-shift / range endpoint

If `Bc` annihilates `ker A`, finite-dimensional symmetry suggests proving `Bc ∈ range A`, obtaining some `x₀` with `A x₀=Bc` and formulating the zero-shift secular endpoint algebraically without `A^-1`.

If the coupling does not vanish, the new E4-A1 identity identifies a genuine successor shell response on a zero mode of `A`. The next theorem should expose the corresponding resonant contribution to the negative-shift resolvent and secular scalar near zero.

### E3-C — resolvent identity / monotonicity

The representation barrier is closed: the exact root detector is now a real explicit scalar on `lam<0`. A finite-dimensional shifted-resolvent identity and strict monotonicity theorem can be attempted directly.

**Firewall:** at most one negative root is not negative-root exclusion.

### E4-B — parity shifted-nullity

Use only finite-dimensional rank/kernel algebra from the rank-at-most-one parity defect and algebraic `D`-equivalence. Do not import unitary interlacing.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- supporting theorem checks do not automatically imply machine claim promotion;
- `V=W⊕S` does not imply shell invariance;
- D is algebraic, not unitary/isometric;
- `ker A` is not the predecessor-size compressed-operator kernel;
- E4-A1 classification does not imply `Bc ⟂ ker A`;
- predecessor nonnegative does not imply a positive spectral gap;
- never replace `(A-lam I)^(-1)` for `lam<0` by `A^-1` at zero;
- #122 metric control and any future uniqueness theorem remain weaker than root exclusion;
- no source-normalization, promoted-binding, positivity, finite-to-infinite or RH change is implied by #121/#122.

Detailed current post-green implications: `research/RHRC/RESEARCH_LEADS_POST_122_DELTA.md`.

**RH remains OPEN.**