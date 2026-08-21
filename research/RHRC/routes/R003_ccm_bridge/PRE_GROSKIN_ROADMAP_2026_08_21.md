# R003 — CCM / explicit-formula / zero-side aperture bridge

Status: **DISCOVERY**. RH remains open.

The finite CCM matrix is theorem-authoritative in `Zeta23.CCM`. PR #30 proved its exact finite
index-displacement identity in Lean, and PR #31 closed the analytic kernel foundation for positive
aperture: continuity, compact support, integrability, and real-valuedness are compiler-checked.

The remaining bridge is deliberately split into two different mathematical obligations:

1. **deterministic RHS identity** — prove the literature explicit-formula RHS evaluated on the CCM
   kernel equals the formal finite CCM matrix up to the scalar shift;
2. **explicit-formula regularity extension** — prove that the actual zeta zero-side sum equals that
   literature RHS for the continuous, compactly supported, piecewise-smooth CCM kernel.

These arrows must not be conflated:

```text
formal CCM matrix M
    |
    |  R003_CCM_RHS_IDENTITY
    v
EF.literatureRHS(K)
    ^
    |  R003_KERNEL_EF_EXTENSION
    |
actual zeta zero-side matrix G
```

Only when both arrows are proved may `R003_CCM_BRIDGE` be promoted.

## Locked objects

- **CCM matrix**: `Zeta23.CCM.finiteMatrix L N`, with source-level wrapper
  `finiteMatrixOfLambda lam N` using the exact conversion `L = 2 log lam`.
- **Index operator**: `Zeta23.CCM.indexMatrix N`.
- **Formal finite displacement theorem**:
  `Zeta23.CCM.finiteMatrix_displacement` and
  `Zeta23.CCM.rank_finiteMatrix_displacement_le_two`.
- **CCM test kernel**:
  `Zeta23.CCM.kernel n m L y = qBasis n m |y| L` on `|y| <= L`, zero outside.
- **Deterministic target object**: `EF.literatureRHS (kernel n m L)`; this is not yet called a
  zero-side Gram matrix because `kernel` is not an admissible `C_c²` test for the current `EF_lit`
  theorem, and off-line zeros give complex `gammaOf` values.

All bridge theorems in this route are stated for **positive aperture `0 < L`**.

## Exact finite displacement result closed

For positive aperture `L`, the formal CCM entry satisfies

```text
(n-m) M_nm = g_n - g_m,
```

with

```text
g_n = poleSeq n L + alphaL n L + primeSeq n L.
```

Consequently, on the centered finite grid,

```text
[D,M] = g 1^T - 1 g^T,
rank([D,M]) <= 2.
```

This is compiler-checked Lean mathematics for the actual formal CCM matrix, not merely a
Python/SymPy identity. It is registered as `R004_CCM_DISPLACEMENT_FORMAL`.

## Kernel foundation closed

PR #31 proved in Lean, for `0 < L`:

```text
qBasis_continuous
qBasis_aperture_eq_zero
kernel_support_subset
kernel_hasCompactSupport
kernel_continuous
kernel_integrable
kernel_im
```

Thus the CCM kernel is a real-valued element of `C_c(ℝ)` supported in `[-L,L]`.

### Exact regularity diagnosis

The remaining regularity seam is **not only the `|y|` cusp at zero**. The kernel is continuous but
has derivative jumps at all three interfaces

```text
y = -L, 0, +L.
```

For every Fourier pair `n,m` and `L > 0`, the one-sided basis derivative satisfies

```text
qBasis'(0) = -2/L,
qBasis'(L) = -2/L.
```

Because `kernel(y) = qBasis(|y|)` inside the aperture and is zero outside, its one-sided derivatives
are therefore

```text
K'(-L-) = 0,       K'(-L+) = +2/L,
K'(0-)  = +2/L,    K'(0+)  = -2/L,
K'(+L-) = -2/L,    K'(+L+) = 0.
```

Any integration-by-parts proof of transform decay must carry the boundary contributions from these
three derivative jumps. It is invalid to integrate only across the two smooth half-intervals and
silently discard the `±L` endpoint terms.

The regularization step smooths all three corners simultaneously; it is not merely a repair of the
origin cusp.

## Reuse the existing App-A machinery

Do **not** re-prove the generic explicit-formula normalization. `Zeta23/ExplicitFormula.lean`
already provides the reusable infrastructure:

```text
EF.prime_summand_eq_zero
EF.prime_term
EF.pole_term
EF.gamma_term
EF.literatureRHS_eq_integral_nu
EF.weilTest_contDiff
EF.weilTest_hasCompactSupport
EF.paperFT_weilTest
```

The CCM formalization should specialize those theorems wherever possible rather than rebuild
support truncation, Fourier inversion, Fubini, pole-weight transforms, or App-A channel assembly.

## Deterministic scalar-shift target

The literature RHS is

```text
RHS(K) = PoleLit(K) - PrimeLit(K) + ArchLit(K).
```

The working candidate, supported by finite diagnostics but not yet theorem-authoritative, is

```text
RHS(K_nm) = 2*M_nm + 4*cCorrection(L)*delta_nm.
```

Equivalently, after exact pole and prime matching, the central analytic identity is

```text
ArchLit(n,m,L) + 2*archComponent(n,m,L)
  = 4*cCorrection(L)*delta_nm.
```

This is deterministic analysis and can be proved before the non-`C_c²` regularity seam is solved.

## Transform control moves forward

Transform decay is needed before regularization. The deterministic archimedean analysis already
needs the real-axis facts

```text
|paperFT(K)(r)| <= C / (1 + r^2)
paperFT(K) in L^1(ℝ)
paperFT(K) * mu in L^1(ℝ).
```

The later zero-side limit additionally needs the strip version

```text
|paperFT(K)(z)| <= C / (1 + |z|^2),   |Im z| <= 1/2.
```

### Transform proof spike A — closed form

Formalize the already-derived closed transform, prove the apparent poles are removable, and obtain
real-axis and strip bounds from the rational expression.

### Transform proof spike B — piecewise integration by parts

Work on the two interior smooth pieces `[-L,0]` and `[0,L]`, but explicitly preserve all boundary
terms. The first integration by parts uses `K(±L)=0`; the `K(0)` contributions cancel between the two
pieces. The second integration by parts produces finite boundary terms from the one-sided derivative
values at `-L`, `0`, and `+L`, plus integrals of the piecewise second derivative.

The proof obligation is therefore to formalize, for the explicit `qBasis` pieces:

```text
qBasis'(0) = -2/L
qBasis'(L) = -2/L
piecewise K'' is integrable on [-L,0] and [0,L]
```

and then derive `O(|z|^-2)`. For the strip bound, the same calculation carries an extra bounded
factor `exp(L/2)` from `|Im z| <= 1/2`. For small `|z|`, use the trivial compact-support/L1 bound;
for large `|z|`, use the twice-integrated formula. This yields the desired
`C/(1+|z|^2)` form without pretending the derivative jumps vanish.

Keep whichever spike is materially smaller in Lean. The closed-form and integration-by-parts paths
are alternatives, not cumulative requirements.

## Exact prime channel — specialize, do not rebuild

`EF.prime_summand_eq_zero` already proves that a test supported in `[-L,L]` has no literature prime
contribution above `floor(exp L)`. The CCM-specific proof only needs to:

1. provide the kernel support bound;
2. use kernel evenness;
3. identify `kernel(log k)` with `qBasis(log k)` inside the aperture;
4. remove the `k=1` term (`Λ(1)=0`);
5. identify the finite result with `2 * primeComponent`.

Target:

```text
PrimeLit(K_nm) = 2*primeComponent(n,m,L).
```

No PNT or new arithmetic estimate enters this step.

## Exact pole channel — choose the shorter specialization

`EF.pole_term` already owns the generic inversion/Fubini/pole-weight calculation. Compare two CCM
proof spikes:

- direct evaluation of `paperFT K (±i/2)` from the explicit basis; or
- specialization of `EF.pole_term` followed by evaluation against `PiX`.

Keep whichever produces the smaller formal proof. Target:

```text
paperFT(K_nm)(i/2) + paperFT(K_nm)(-i/2)
  = 2*poleComponent(n,m,L).
```

## Archimedean identity

After pole and prime channels are formally closed, prove

```text
ArchLit(n,m,L) + 2*archComponent(n,m,L)
  = 4*cCorrection(L)*delta_nm.
```

Split immediately.

### Off diagonal

For `n != m`, `K_nm(0)=0`:

```text
ArchLit(n,m,L) = -2*archComponent(n,m,L).
```

### Diagonal

For `n = m`, `K_nn(0)=2`:

```text
ArchLit(n,n,L) + 2*archComponent(n,n,L)
  = 4*cCorrection(L).
```

The diagonal theorem must prove cancellation of all index-dependent terms. Numerical scalar-shift
agreement is discovery evidence only and may not be used as a proof premise.

Use `EF.gamma_term` and `EF.literatureRHS_eq_integral_nu` where they reduce normalization work.
The `gammaBracket` / `mu` normalization is already owned by App A.

## Regularity adapter: explicit C² mollifier

The existing `EF_lit` theorem remains unchanged. Extend it downstream with a concrete compactly
supported `C²` approximate identity.

Use

```text
eta(x) = (35/32) * (1-x^2)^3   for |x| <= 1,
         0                      otherwise.
```

At `x = ±1`, the function and its first two derivatives vanish, and

```text
integral_{-1}^1 (1-x^2)^3 dx = 32/35,
```

so `eta` is exactly normalized. Scale by

```text
eta_eps(x) = eps^-1 * eta(x/eps),   eps > 0.
```

Define

```text
K_eps := EF.weilTest eta_eps K.
```

For the real-even CCM kernel, prove `EF.tilde K = K`; then reuse

```text
EF.weilTest_contDiff
EF.weilTest_hasCompactSupport
EF.paperFT_weilTest
```

to obtain `K_eps in C_c²` and the transform multiplier formula. This convolution smooths the origin
and both aperture endpoints at once.

## Limits needed for the adapter

Use channel-specific limits; do not require a global uniform approximate-identity theorem unless it
turns out to be shorter in Lean.

### Prime channel

For `eps <= 1`, all `K_eps` are supported in `[-L-1,L+1]`, so every prime term lies in one fixed
finite set. Pointwise convergence at those finitely many `±log n` values is enough.

### Pole channel

Use fixed-point transform convergence at `z = ±i/2`.

### Archimedean channel

For real `r`, nonnegativity and normalization of `eta_eps` give

```text
|paperFT(eta_eps)(r)| <= 1,
```

hence

```text
|paperFT(K_eps)(r)| <= |paperFT(K)(r)|.
```

The real-axis `paperFT(K)*mu` integrability established during deterministic analysis is the
majorant for dominated convergence.

### Zero side

For zeta zeros, `|Im gammaOf(rho)| <= 1/2`. For `eps <= 1`, prove

```text
|paperFT(eta_eps)(gammaOf rho)| <= exp(1/2),
```

and therefore

```text
|paperFT(K_eps)(gammaOf rho)|
  <= exp(1/2) * |paperFT(K)(gammaOf rho)|.
```

Combine the strip `O(|z|^-2)` bound with the existing weighted zero-count summability. No uniform
control of second derivatives of `K_eps` is required.

Endpoint theorem:

```text
sum_rho m_rho * paperFT(K)(gammaOf rho)
  = EF.literatureRHS(K).
```

## Naming discipline

Before RH, do not call

```text
sum_rho m_rho * paperFT(K_nm)(gammaOf rho)
```

a `Gram` matrix: off-line zeros make `gammaOf rho` complex and positivity has not been established.
Use `zeroSideEntry` / `zeroSideMatrix` (or `weilZeroEntry` / `weilZeroMatrix`). Reserve `Gram`
terminology for a theorem that establishes an actual Gram interpretation under suitable on-line
hypotheses.

## Corrected implementation sequence after this roadmap PR

PR #32 is this architecture/governance correction. The mathematical implementation resumes at
**PR #33**.

### PR #33 — transform control + exact easy channels

Create:

```text
Zeta23/CCM/KernelTransform.lean
Zeta23/CCM/WeilRHS.lean
```

First formalize the interface derivative facts needed by the fallback integration-by-parts route:

```text
qBasis_deriv_zero
qBasis_deriv_aperture
```

or equivalent `HasDerivAt` statements proving the common value `-2/L`.

Then deliver:

```text
real-axis O(r^-2) transform bound
paperFT(K) in L^1
exact prime channel
exact pole channel
deterministic rhsEntry / rhsMatrix objects
```

If the closed-form route wins, the derivative lemmas remain useful regularity documentation but the
transform proof need not use them.

### PR #34 — exact archimedean scalar shift

Create:

```text
Zeta23/CCM/ArchimedeanBridge.lean
Zeta23/CCM/RHSBridge.lean
```

Deliver:

```text
paperFT(K)*mu in L^1
ArchLit + 2*archComponent = 4*cCorrection(L)*delta_nm
rhsMatrix = 2*finiteMatrix + 4*cCorrection(L)*I
[D,rhsMatrix] = 2*(g1^T - 1g^T)
rank([D,rhsMatrix]) <= 2
```

Only then promote `R003_CCM_RHS_IDENTITY`.

### PR #35 — explicit-formula regularity adapter

Create:

```text
Zeta23/CCM/Mollifier.lean
Zeta23/CCM/Regularization.lean
```

Deliver the strip transform bound if not already available, the explicit polynomial `C²` mollifier,
`weilTest` smoothing, channel-by-channel limits, and

```text
zero-side sum(K) = EF.literatureRHS(K).
```

Only then promote `R003_KERNEL_EF_EXTENSION`.

### PR #36 — final finite zero-side assembly

Create:

```text
Zeta23/CCM/WeilBridge.lean
```

Define `zeroSideEntry` / `zeroSideMatrix`, then prove

```text
zeroSideMatrix = rhsMatrix
zeroSideMatrix = 2*finiteMatrix + 4*cCorrection(L)*I
[D,zeroSideMatrix] = 2*(g1^T - 1g^T)
rank([D,zeroSideMatrix]) <= 2
```

Only then promote `R003_CCM_BRIDGE` and `R003_WEIL_DISPLACEMENT`.

## Closed-form transform — discovery evidence

With `a = 2πm/L`, `b = 2πn/L`, the diagnostic derivation gives

```text
n != m:
  h(r) = (2/(π(n-m))) (1-cos(rL))
         * [a/(a^2-r^2) - b/(b^2-r^2)]

n = m:
  h(r) = (2/L) (1-cos(rL))
         * [1/(b+r)^2 + 1/(b-r)^2].
```

The apparent poles are removable. This remains discovery guidance until formalized.

## Numerical scalar-shift diagnostic

`confirm_closed_form.py`, `mp.dps = 20`:

| lambda | c_raw | offdiag systematic | corrected c | `4*cCorrection(L)` | abs diff | diag spread |
|---|---:|---:|---:|---:|---:|---:|
| 2 | 1.076281434379 | 2.48e-07 | 1.076281186271 | 1.076281186271 | 5.6e-15 | 4.5e-09 |
| 3 | 1.408303228758 | -1.05e-07 | 1.408303333375 | 1.408303333375 | 1.3e-15 | 1.1e-09 |
| 5 | 1.616560903218 | 4.93e-08 | 1.616560853940 | 1.616560853940 | 2.2e-16 | 3.6e-10 |
| 7 | 1.681430174226 | -5.57e-08 | 1.681430229916 | 1.681430229916 | 2.2e-16 | 2.1e-10 |

This is discovery evidence only. The corrected machine-precision agreement is not theorem
authority and is not used as a proof premise.

## Proof-search ladder

| step | statement | status |
|---|---|---|
| J1-D-formal | exact `[D,M] = g1^T - 1g^T`, rank <= 2 for formal CCM matrix | **PROVED IN LEAN** |
| K0 | continuity/compact support/integrability/real-valuedness of CCM kernel | **PROVED IN LEAN** |
| K1 | derivative/interface data at `-L,0,+L` used by piecewise transform analysis | OPEN |
| T0 | real-axis `O(r^-2)` transform control and Fourier integrability | OPEN |
| B0 | exact pole-channel identity | OPEN |
| B1 | exact prime-channel identity | OPEN |
| B2 | deterministic reduction to the archimedean channel | OPEN until B0+B1 are Lean-closed |
| B3 | exact archimedean scalar-shift identity | OPEN |
| B4 | `RHSMatrix = 2*M + 4*cCorrection(L)*I` | OPEN |
| E0 | strip `O(|z|^-2)` transform control for `|Im z| <= 1/2` | OPEN |
| E1 | extend zeta `EF_lit` from `C_c²` approximants to the CCM kernel | OPEN |
| J5 | actual zero-side matrix `G = 2*M + 4*cCorrection(L)*I` | OPEN |
| J5-D | exact `[D,G] = 2(g1^T - 1g^T)`, rank <= 2 | OPEN |
| J6 | finite-to-infinite operator/normalization seam | OPEN |

## Claim boundary

- `R004_CCM_DISPLACEMENT_FORMAL`: PROVED_UNCONDITIONAL.
- `R003_CCM_RHS_IDENTITY`: OPEN.
- `R003_KERNEL_EF_EXTENSION`: OPEN.
- `R003_CCM_BRIDGE`: OPEN and depends on both claims above.
- `R003_WEIL_DISPLACEMENT`: OPEN.
- RH: OPEN.

No finite-to-infinite theorem, RH implication, new prime-side upper bound, or zero-side positivity
theorem is claimed.

## Reproduction

```bash
pip install -r research/RHRC/routes/R003_ccm_bridge/requirements.txt
python research/RHRC/routes/R003_ccm_bridge/check_diagonal_shift.py --lambdas 2 3 5 --ns -3 -2 -1 0 1 2 3
python research/RHRC/routes/R003_ccm_bridge/confirm_closed_form.py
```
