# PR #35 — finite Guinand--Weil dictionary objects

Status: **implementation started; ready for review; no RHRC claim promotion**.

Base: merged PR #34 at `756d074c325a555de2afb1ef8306c4dc0bb793e2`.

## Objective

Formalize the exact finite dictionary on top of the theorem-authoritative elementary source matrix, while using the inherited `Zeta23.paperFT` convention as the canonical internal transform from the start.

Target architecture:

```text
paper even-sector vector v
  -> symmetric centered coefficients u
  -> K_u(omega) = <u, sourceMatrix(omega) u>
  -> compact physical-space test k_{u,L}(y)
  -> g_{u,L}(z) = Zeta23.paperFT(k_{u,L})(z)
```

Then prove equivalence with the paper/reference representation

```text
u -> T_v -> Volterra K_v -> ghat_v -> g_v.
```

No explicit formula is invoked in this PR.

## Preserved external oracle

PR #35 physically preserves the finite dictionary subset of the pinned Groskin verification script as

```text
research/RHRC/external/connes_cvs/finite_dictionary_reference.py
```

Pinned source:

```text
repository: HMarcusWH/connes-cvs-
commit:     5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c
source:     papers/2_guinand_weil_dictionary_tail_order/scripts/verify_dictionary_threeroute.py
blob:       90576ea92835fff2f9dd2e3aa63ad99829bd17e5
license:    MIT
```

The local adapter preserves only `v/u`, `T`, `K`, `K_quad`, `ghat`, `g`, `g_quad`, and finite regression guards. Zero-side and archimedean-tail routines are intentionally excluded.

External Python remains an oracle/falsifier only and must not enter the Lean import graph.

The first Codex review found four oracle/API issues, all now repaired and regression-guarded:

- non-real transform inputs preserve their imaginary part (real projection occurs only on the real axis);
- importing the oracle does not mutate the caller's global `mpmath` precision;
- the constructor enforces the paper domain `c > 1`;
- the constructor enforces `N >= 0` and exactly `N+1` coefficients.

`check_finite_dictionary_reference.py` exercises those guards and the closed-form-vs-quadrature dictionary identities in CI. These checks remain diagnostic only.

## Lean work packages

### D1 — full-grid source contraction

In `Zeta23/CCM/FiniteDictionary.lean` define

```text
sourceContract N u omega
K_u(omega) := sourceContract N u omega.
```

Initial theorem targets:

```text
K_u(0) = 0
K_u(1-y/L) = sum_{i,j} conj(u_i) qBasis(i,j,y,L) u_j.
```

The second theorem should be a direct lift of PR #34's exact convention bridge, not a new trigonometric derivation.

### D2 — reversal-even paper embedding

For `v : Fin (N+1) -> R`, define centered coefficients

```text
u_0    = v_0
u_{+k} = v_k/sqrt(2)
u_{-k} = v_k/sqrt(2).
```

Prove reversal symmetry and norm preservation.

### D3 — endpoint normalization

Prove the elementary source identities at `omega = 1` and hence

```text
K_u(1) = 2 * sum_i |u_i|^2.
```

For normalized paper vectors, the physical dictionary test therefore satisfies

```text
k_{v,L}(0) = 1.
```

Also retain `K_u(0)=0`, giving endpoint vanishing at `|y|=L`.

### D4 — compact physical-space test

Define

```text
k_{u,L}(y) = 1/2 * K_u(1-|y|/L)    if |y| <= L
           = 0                       otherwise.
```

Prove:

```text
k(-y) = k(y)
support(k) subset [-L,L]
k(+/-L) = 0
Continuous k                     for L > 0.
```

Do not claim `C^2`; the raw test has the interface-regularity issue deferred to PR #36.

### D5 — canonical transform

Define

```text
g_{u,L}(z) := Zeta23.paperFT(k_{u,L})(z).
```

Prove the even-test cosine representation

```text
g_{u,L}(z) = int_0^L K_u(1-y/L) cos(z y) dy
```

with exact inherited normalization.

### D6 — trigonometric / Volterra representation

Define

```text
T_v(t) = sum_m u_m exp(2*pi*i*m*t)
KVolterra_v(omega) = 2 * int_0^omega T_v(t) T_v(omega-t) dt
```

and prove

```text
K_u(omega) = KVolterra_v(omega)
```

for the real reversal-even coefficient family used by the paper.

This representation is downstream of the source contraction so integral algebra cannot block the core dictionary object.

### D7 — Groskin Fourier-convention bridge

With `Delta = L/(2*pi)`, define the paper-side compact weight

```text
ghat_v(xi) = pi*K_v(1-|xi|/Delta)   if |xi| <= Delta
           = 0                       otherwise
```

and prove the exact convention map to the physical test / inherited transform. No manual `2*pi` factors should remain undocumented after this theorem.

## Deliberate non-scope

PR #35 does not prove or promote:

- `EF_lit` applicability to the raw dictionary test;
- a zeta zero-side sum;
- the formal `Q_inf` normalization bridge;
- the `2N+1` source quotient;
- positivity;
- RH;
- finite-to-infinite convergence.

Open claims remain:

```text
R003_CCM_RHS_IDENTITY
R003_KERNEL_EF_EXTENSION
R003_CCM_BRIDGE
R003_WEIL_DISPLACEMENT
C_RH
```

## Merge gate

Require exact-head:

```text
lake build Zeta23.CCM.FiniteDictionary
lake build Zeta23.CCM
lake build Zeta23.ExceptionalZero
python research/RHRC/tools/run_suite.py
python research/RHRC/routes/R003_ccm_bridge/compare_ccm_normalizations.py --output /tmp/CCM_NORMALIZATION_AUDIT.json
python research/RHRC/routes/R003_ccm_bridge/check_finite_dictionary_reference.py
```

plus the external-reference firewall and forbidden-placeholder gate.

The finite-dictionary Python regression compares the preserved external closed-form and integral representations and exercises API/domain guards, but such checks remain diagnostic only.
