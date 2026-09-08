# RHRC formal audit — theorem authority through PR #129; control authority through PR #117

> **RH remains OPEN.**

## Current authority split

```text
live main after #129 = e1192857afed9f68fa4a13143ce690b62191b997
live main tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7

theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
validated theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
theorem-bearing merged through = PR #129
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. The exact #129 theorem head passed both authoritative workflows before merge, and the validated theorem tree is identical to the merged-main tree.

## PR #112 — FIRST-BAD-RIGIDITY-D1

**PROVED:** global first badness; both predecessor parities nonnegative below the first bad size; intrinsic predecessor `W`; one-step shell `S` with complex finrank one; first-bad negative eigenmode with nonzero shell content; exact cubic parity-defect factorization; ExceptionalZero packaging at one common finite state.

## PR #113 — FIRST-BAD-RIGIDITY-D2

**PROVED:** canonical `V=W⊕S`; predecessor/shell projections; projected predecessor block `A=P_W T|_W`; predecessor nonnegativity; safe bijectivity of `A-lam I` for `lam<0`; shifted resolvent; predecessor reconstruction; basis-free shifted Schur identity.

## PR #115 — FIRST-BAD-RIGIDITY-E1

**PROVED:** canonical cubic successor direction is not inherited from the predecessor; `intrinsicCubicShellPart p N != 0` in the stated range; the off-line-zero first-bad state carries both nonzero negative-mode and cubic shell coordinates.

## PR #118 — FIRST-BAD-RIGIDITY-E2

**PROVED:** canonical shell coordinate, exact one-dimensional shell reconstruction, faithful quotient coordinate with predecessor kernel, normalized negative eigenmode and identification of the odd cubic parity-defect coefficient with the canonical quotient coordinate of the exact intertwining defect.

## PR #119 — FIRST-BAD-RIGIDITY-E3-A

**PROVED:** for every safe `lam<0` under predecessor nonnegativity,

```text
cubicSecularScalar(lam)=0
  <-> full residual=0
  <-> canonical trial vector is a genuine eigenmode
  <-> exists nonzero eigenmode at lam.
```

An off-line zero therefore forces a global-first-bad state with an exact negative root of the canonical secular scalar.

## PR #121 — FIRST-BAD-RIGIDITY-E3-B2

**PROVED:** exact pointwise bridge from the quotient scalar to the explicit Schur scalar, initially with the conjugation forced by Mathlib's complex inner-product orientation.

## PR #122 — FIRST-BAD-RIGIDITY-E3-B1 / E4-A1

**PROVED:** projected predecessor symmetry, shifted coercivity, shifted-resolvent symmetry and metric bounds; realness of the explicit scalar and the unconjugated bridge on the safe real-negative axis; first denominator-free root metric restriction; and on `ker A`,

```text
Az=0 -> (<z,Bc>=0 <-> Tz=0).
```

This classifies zero resonance; it does not eliminate it.

## PR #124 — FIRST-BAD-RIGIDITY-E4-A2

**PROVED:**

```text
range A ⟂ ker A
range A ∩ ker A = {0}
W = ker A ⊕ range A.
```

If the coupling annihilates `ker A`, then a zero-shift preimage `Ax0=b` exists and `<x,b>` is solution-independent. In the resonant branch, for `z∈ker A` and `lam<0`,

```text
<z,b> = (-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

## PR #125 — FIRST-BAD-RIGIDITY-E4-A2-ENDPOINT

**PROVED:** canonical zero-shift endpoint

```text
S0=<Tc,c>-<x0,b>
u0=-x0+c
```

with solution independence, zero predecessor coordinate of `T u0`, exact identity `<T u0,u0>=S0`, exact predecessor-fibre complete square, and at the forced negative explicit root

```text
Re S0 < 0.
```

This is not regular-branch exclusion.

## PR #127 — FIRST-BAD-RIGIDITY-E4-A3a

Exact theorem head: `3e0a55f397601389387b614bd4595be634d1e572`.

**PROVED — special zero-shift shell response:** for the decoupled zero-shift trial vector, the specific image `T u0` is exactly its shell part. The canonical response scalar `sigma0` satisfies

```text
sigma0 • c = T u0
S0 = star(sigma0) * <c,c>.
```

The conjugation is theorem-relevant because Mathlib's complex inner product is conjugate-linear in the first argument.

**Not proved:** shell invariance of the full operator or that `u0` is an eigenvector.

## PR #128 — FIRST-BAD-RIGIDITY-E4-A3b

Exact theorem head: `a31f174c5748695369200cdc20b6514016accadd`.

**PROVED — regular branch:** at the same forced negative explicit root,

```text
Re sigma0 < 0.
```

**PROVED — canonical kernel coordinate:** the predecessor kernel coordinate vanishes exactly on `range A`; for the safe shifted resolvent,

```text
(-lam) • K(R_lam b) = K(b).
```

For the cubic coupling `b=Bc`, define `k=K(b)`. The decoupled branch has `k=0`; the resonant branch has `k!=0` and the exact divided `1/(-lam)` kernel-pole formula for `lam<0`.

**PROVED — ExceptionalZero composition:** a hypothetical off-line zero forces the same global-first-bad state into the strengthened regular/resonant classification.

**Not proved:** exclusion of either branch.

## PR #129 — FIRST-BAD-RIGIDITY-E4-A3c

Exact theorem head: `440be3e5b6bf05e94ae2c65b1704d52d20acc9af`.
Merged main: `e1192857afed9f68fa4a13143ce690b62191b997`.
Validated/merged tree: `2f042a3b0b3313e7c67d627a58a32d579d4e7ff7`.
RHRC #838: SUCCESS. Permansson #611: SUCCESS.

**PROVED — source-explicit cubic defect:** `SourceExplicitCubicDefect.lean` defines the orthogonalized quadratic normal `centeredQuadraticNormal` and the canonical source moment `evenQuadraticSourceMoment`. The main endpoint is

```text
Zeta23.CCM.cubicDefectFunctional_eq_evenQuadraticSourceMoment
```

which proves, for the actual `canonicalSourceMatrix`, that the cubic parity-defect coefficient is exactly the quadratic source moment.

**PROVED — exact cross-parity transport:** the compiler-audited theorem surface includes

```text
intrinsicCubicQuotientCoordinate_evenIndex
cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
crossParitySecularGamma_eq_trial_cubic_overlap_div
cubicSecularScalar_crossParity_source_transfer
cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
```

The exact transfer has the mathematical form

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

The predecessor correction in the D-transported cubic shell is retained; D is never upgraded to unitary/isometric.

**PROVED — global ExceptionalZero endpoint:**

```text
exists_globalFirstBad_crossParitySecularTransfer_of_offLine_zero
```

forces a hypothetical off-line zero to one global-first-bad finite state carrying the source-explicit parity certificate at the same negative explicit root. Even-root and odd-root cases are recorded without dividing by an unproved factor.

**Not proved:** useful sign/nonzeroness of `alpha`, `Gamma`, the overlap or source moment; regular/resonant exclusion; negative-root exclusion; RH.

## PR #117 — latest control-plane authority

**CI-VERIFIED CONTROL INFRASTRUCTURE:** Control-v2 hardening, typed deformation-budget steps, horizon-certificate requirement, decision-commutation checks, archaeology-path binding, deterministic routing transparency, theorem/control anchor separation.

PRs #118/#119/#121/#122/#124/#125/#127/#128/#129 changed theorem state but did not change Control-v2 semantics. Therefore the separate control-plane anchor remains #117.

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
range/kernel decomposition + zero-shift solve                           PROVED / #124
canonical zero-shift endpoint + exact complete square                   PROVED / #125
special zero-shift shell response + S0 relation                         PROVED / #127
regular response Re sigma0<0                                            PROVED / #128
canonical resonant kernel coordinate / exact pole                       PROVED / #128
cubic defect = canonical quadratic source moment                        PROVED / #129
exact cross-parity secular transfer                                     PROVED / #129
off-line zero -> source-explicit global first-bad certificate           PROVED / #129

useful sign/nonzeroness of source moment / Gamma / overlap               OPEN
regular branch source-specific exclusion                                OPEN
resonant branch source-specific exclusion                               OPEN
negative-root exclusion                                                  OPEN
explicit terminal RH bridge                                              OPEN
RH                                                                        OPEN
```

## Current research frontier

### E4-A4 — canonical-source branch exclusion

The shell response, kernel pole and exact parity transfer are now theorem-backed. Generic structural countermodels survive these kinds of constraints, so the next contradiction must use the actual canonical source formula, including the source diagonal/channel values exposed through the #129 quadratic moment.

Primary tasks:

1. exact decomposition of `evenQuadraticSourceMoment` through the production `canonicalSourceMatrix` formula;
2. source-specific regular-branch incompatibility;
3. source-specific resonant-branch incompatibility;
4. composition into global first-bad negative-root exclusion.

### E4-B — parity shifted-nullity

Still parallel. Use finite-dimensional rank/kernel algebra only; do not import unitary interlacing through D.

### E3-C — resolvent identity / monotonicity

Still parallel. At most one negative root remains strictly weaker than no negative root.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- supporting theorem checks do not automatically imply machine claim promotion;
- `V=W⊕S` does not imply shell invariance;
- D is algebraic, not unitary/isometric;
- the D-transport predecessor correction may not be dropped;
- `ker A` is not the predecessor-size compressed-operator kernel;
- no `A^-1` at zero;
- `Re S0<0` and `Re sigma0<0` are not branch exclusion;
- a canonical `1/(-lam)` kernel pole is classification, not contradiction;
- #129 does not prove source-moment, overlap, `alpha` or `Gamma` sign/nonzeroness;
- generic structural countermodels do not refute the actual canonical source matrix;
- root uniqueness remains weaker than root exclusion;
- no source-normalization, promoted-binding, negative-root exclusion or RH change is implied by #127-#129.

Detailed current post-green implications: `research/RHRC/RESEARCH_LEADS_POST_129_DELTA.md`.

**RH remains OPEN.**