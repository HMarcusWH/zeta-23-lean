# RHRC formal audit — theorem authority through PR #131; control authority through PR #117

> **RH remains OPEN.**

## Current authority split

```text
live main after #131 = 436d524d0cdeb5986d76dcbb988f771d19836c55
live main tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
theorem-bearing merged through = PR #131
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. The exact #131 theorem head passed both authoritative workflows before merge, and the validated theorem tree is identical to the merged-main tree.

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

with solution independence, zero predecessor coordinate of `T u0`, exact identity `<T u0,u0>=S0`, exact predecessor-fibre complete square, and at the forced negative explicit root `Re S0 < 0`.

This is not regular-branch exclusion.

## PR #127 — FIRST-BAD-RIGIDITY-E4-A3a

**PROVED — special zero-shift shell response:** for the decoupled zero-shift trial vector, the specific image `T u0` is exactly its shell part. The canonical response scalar `sigma0` satisfies

```text
sigma0 • c = T u0
S0 = star(sigma0) * <c,c>.
```

**Not proved:** shell invariance of the full operator or that `u0` is an eigenvector.

## PR #128 — FIRST-BAD-RIGIDITY-E4-A3b

**PROVED — regular branch:** at the same forced negative explicit root, `Re sigma0 < 0`.

**PROVED — canonical kernel coordinate:** the predecessor kernel coordinate vanishes exactly on `range A`; for the safe shifted resolvent,

```text
(-lam) • K(R_lam b) = K(b).
```

For the cubic coupling `b=Bc`, define `k=K(b)`. The decoupled branch has `k=0`; the resonant branch has `k!=0` and the exact divided `1/(-lam)` kernel-pole formula for `lam<0`.

**Not proved:** exclusion of either branch.

## PR #129 — FIRST-BAD-RIGIDITY-E4-A3c

**PROVED — source-explicit cubic defect:** the cubic parity-defect coefficient is exactly the actual canonical quadratic source moment.

**PROVED — exact cross-parity transport:**

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

The predecessor correction in the D-transported cubic shell is retained; D is never upgraded to unitary/isometric.

**PROVED — global ExceptionalZero endpoint:** a hypothetical off-line zero is forced to one global-first-bad finite state carrying the source-explicit parity certificate at the same negative explicit root.

**Not proved:** useful sign/nonzeroness of `alpha`, `Gamma`, overlap or source moment; branch exclusion; negative-root exclusion; RH.

## PR #131 — FIRST-BAD-RIGIDITY-E4-A4a

Exact theorem head: `b0026683bcbf233afa947c7f15b57bcc4ddf31e3`.  
Merged main: `436d524d0cdeb5986d76dcbb988f771d19836c55`.  
Validated/merged tree: `5ad51fd877d51348f1af474b2864eb4ab3e0617a`.  
RHRC #854: SUCCESS. Permansson #627: SUCCESS.

**PROVED — exact production source decomposition:**

```text
canonicalSourceMatrix
  = canonicalPoleMatrix
    - canonicalArchMatrix
    - canonicalPrimeMatrix.
```

The canonical archimedean channel is reduced safely through the corrected direct source normalization. The index-independent scalar correction is separated as a scalar identity and is annihilated by the active quadratic-normal observable.

**PROVED — reduced arch split:**

```text
reducedCanonicalArchMatrix
  = reducedCanonicalArchDiagonalMatrix
    + reducedCanonicalArchOffDiagonalMatrix.
```

**PROVED — prime atomization:** the finite prime channel is an exact von-Mangoldt weighted finite sum of existing elementary `sourceMatrix` atoms at source coordinates `1 - log q / L`.

**PROVED — pole factorization and parity cancellation:** the pole matrix has an exact rank-two profile factorization into even and odd profiles; the odd profile pairs to zero with every even boundary-flat input, leaving one surviving even-profile contribution in the active moment.

**PROVED — A4a endpoint:**

```text
cubicDefectFunctional L K v
  = explicitCanonicalSourceMoment L K v
```

for `0<L`, `2<=K`, and `v` in the exact even Euclidean boundary-flat sector, where

```text
explicitCanonicalSourceMoment
  = poleEven
    - reducedArchDiagonal
    - reducedArchOffDiagonal
    - finitePrimeAtomSum.
```

**Not proved:** any useful sign/nonzeroness of the explicit source moment, overlap, `Gamma`, or `alpha`; regular/resonant exclusion; negative-root exclusion; RH.

**Post-green derived warning:** the explicit source moment is linear in `v`. Therefore universal strict positivity/nonnegativity of the raw moment over the whole vector space cannot be the A4b mechanism; `v -> -v` reverses it. A useful constraint must be tied to the canonically oriented trial vector and/or composed with overlap/root/branch data.

## PR #117 — latest control-plane authority

**CI-VERIFIED CONTROL INFRASTRUCTURE:** Control-v2 hardening, typed deformation-budget steps, horizon-certificate requirement, decision-commutation checks, archaeology-path binding, deterministic routing transparency, theorem/control anchor separation.

PRs #118/#119/#121/#122/#124/#125/#127/#128/#129/#131 changed theorem state but did not change Control-v2 semantics. Therefore the separate control-plane anchor remains #117.

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
exact canonical source-moment decomposition                             PROVED / #131

universal raw source-moment positivity                                  NOT A VIABLE TARGET / linearity
useful compositional source/overlap constraint                          OPEN
regular branch source-specific exclusion                               OPEN
resonant branch source-specific exclusion                              OPEN
negative-root exclusion                                                 OPEN
explicit terminal RH bridge                                             OPEN
RH                                                                       OPEN
```

## Current research frontier

### E4-A4b — regular-branch canonical-source test

A4a is closed. The next theorem should compose the #131 explicit pole/arch/prime source formula directly into the #129 cross-parity root interface and then ask what source-sensitive invariant can constrain the canonical first-bad trial vector.

Highest-leverage first tranche:

1. source-expanded root transfer;
2. named linearity/negation/scalar-covariance lemmas for the explicit source moment;
3. the elementary one-parameter `sourceMatrix omega` quadratic-normal observable;
4. exact endpoint zeros at `omega=0,1`;
5. only then a source-specific factorization/sign/real-part theorem on the canonically oriented regular state.

### E4-A4c — resonant source test

Still open. Combine the exact kernel pole, predecessor nonnegativity and the same source-expanded parity equation.

### E4-B / E3-C / E3-B3

Remain parallel. Shifted-nullity and monotonicity may constrain the state but must not displace source-sensitive A4 unless they add genuinely new information. At most one negative root remains weaker than no negative root.

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
- #129/#131 do not prove source-moment, overlap, `alpha` or `Gamma` sign/nonzeroness;
- universal raw source-moment positivity is incompatible with the linear source observable except in a degenerate zero-functional sense;
- generic structural countermodels do not refute the actual canonical source matrix;
- root uniqueness remains weaker than root exclusion;
- no source-normalization, promoted-binding, negative-root exclusion or RH change is implied by #127-#131.

Detailed current post-green implications: `research/RHRC/RESEARCH_LEADS_POST_131_DELTA.md`.

**RH remains OPEN.**