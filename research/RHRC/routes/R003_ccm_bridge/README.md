# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **DISCOVERY**. RH remains **OPEN**.

This file is the active route SSOT. It supersedes the earlier transform-first ordering and records the theorem boundary after PRs #35–#37 and the current PR #38 residual-gluing work.

## Authority and proof-status discipline

Authority hierarchy:

```text
Lean / exact comparator theorem checks   mathematical authority
RHRC receipts                            provenance / governance
external connes-cvs Python               oracle / falsifier only
finite numerics                          diagnostic only
```

Nothing promotes itself. Green CI does not imply an explicit-formula theorem, a finite bridge does not imply a finite-to-infinite theorem, and none of the finite CCM results are RH evidence by themselves.

## Current theorem boundary

The fork-owned finite CCM/source/dictionary machinery is theorem-authoritative in `Zeta23.CCM`.

Compiler-checked facts include:

- the formal finite CCM matrix `finiteMatrix L N`;
- generic divided-difference/source calculus and rank-at-most-two index displacement;
- the exact source/physical-coordinate dictionary bridge;
- the finite dictionary test

```text
k_{u,L}(y) = 1/2 K_u(1-|y|/L)   for |y| <= L,
           = 0                    otherwise;
```

- `sourceMatrix(1) = 2I` and `K_u(1) = 2*coefficientMass(u)`;
- compact support, continuity, endpoint values and evenness of the raw dictionary;
- for real `u`, the exact rank-one seam decomposition

```text
k_{u,L}(y) = sigma(u)^2 * tau_L(y) + r_{u,L}(y),
sigma(u) = sum_i u_i,
tau_L(y) = max(0, 1-|y|/L);
```

- exact first-order seam factorization

```text
K'_u(0) = K'_u(1) = 2 * sigma(u)^2;
```

- first and second residual branch jets at `-L`, `0`, and `L`;
- in PR #38, the smooth residual is globally glued into a `C_c^2` test for every real `u` and `L>0`, with a complex-valued wrapper satisfying exactly the `ContDiff ℝ 2` and `HasCompactSupport` hypotheses used by `EF_lit`.

The raw dictionary itself is not claimed to be globally `C^1`: its universal tent channel carries the first-derivative seam. The residual is the smooth part; the tent is the remaining nonsmooth part.

## Normalization lock

The external Groskin / Connes–van Suijlekom / CCM reference implementation remains outside the Lean theorem dependency graph. It is an oracle/falsifier only.

The frozen source audit distinguishes:

```text
M         fork-owned formal CCM matrix
Q_inf     cutoff-free finite Guinand–Weil / CvS matrix
WeilGram  older doubled explicit-formula diagnostic normalization
```

The source audit target is

```text
Q_inf = M + 2*cCorrection(L)*I,
```

while the older diagnostic used

```text
WeilGram = 2*M + 4*cCorrection(L)*I = 2*Q_inf.
```

**Do not import the old factor two into the production dictionary theorem.** The production dictionary contains an explicit factor `1/2`. The deterministic theorem must therefore be proved channel by channel in Lean with the neutral target

```text
dictionaryMatrix(L,N) := M(L,N) + 2*cCorrection(L)*I.
```

Also keep the two low-rank objects separate:

```text
I = identity matrix                 scalar normalization channel
J = 1 1^T                           rank-one coefficient-sum seam channel
```

`I != J`. The first-order seam theorem concerns `J`; the finite Guinand–Weil normalization concerns `I`.

## Milestones

```text
M2a finite dictionary core             REACHED
M2b finite topology / normalization    REACHED
M2c analytic seam isolation            REACHED
M2d admissible dictionary family       OPEN
M2e deterministic finite RHS identity  OPEN
M2f exact zero-side / CCM bridge       OPEN
```

PR #38 closes the **residual** `C_c^2` obligation inside M2d. M2d itself remains open until the canonical tent has a theorem-authoritative transform/decay package and a justified zeta explicit-formula extension.

## Active implementation sequence

### PR #35 — finite Guinand–Weil dictionary core

**MERGED.** Delivered `sourceContract`, the exact source/qBasis contraction bridge, `dictionaryTest`, and `dictionaryTransform = Zeta23.paperFT(dictionaryTest)`.

### PR #36 — finite dictionary topology / normalization

**MERGED.** Delivered the reusable quadratic form convention, `sourceMatrix(1)=2I`, coefficient mass, endpoint/center identities, evenness, compact support and continuity.

### PR #37 — analytic seam isolation

**MERGED.** Delivered the exact coefficient-sum seam channel, tent-plus-residual decomposition, residual first-order endpoint/center jets, source/residual second-order calculus, outer residual second-derivative vanishing, and center second-derivative agreement.

No explicit formula, zero-side bridge or RH claim was obtained.

### PR #38 — global residual `C_c^2` closure

**CURRENT PR.** Scope is deliberately narrow.

Targets now implemented in Lean:

```text
contDiff_two_dictionaryResidualReal

dictionaryResidualReal_hasCompactSupport

contDiff_two_dictionaryResidualTest

dictionaryResidualTest_hasCompactSupport

dictionaryResidualTest_admissible
```

The complex wrapper `dictionaryResidualTest` is exactly the smooth residual in the codomain expected by the inherited explicit-formula interface.

Non-claims:

- no tent transform theorem;
- no explicit-formula extension for the tent;
- no deterministic RHS identity;
- no zero-side matrix bridge;
- no restriction `sum u_i = 0`;
- no `C^3` claim;
- no RH evidence or RH claim.

### PR #39 — canonical tent transform + strip decay

Formalize the universal tent

```text
tau_L(y) = max(0, 1-|y|/L)
```

and its `paperFT` exactly. Mathematical target:

```text
hat(tau_L)(z) = 2*(1-cos(L*z))/(L*z^2)      z != 0,
hat(tau_L)(0) = L.
```

Prefer the strip estimate in the existing zero-summability geometry:

```text
|hat(tau_L)(z)| <= C_L / (1 + Complex.normSq z)
```

for `|Im z| <= 1/2`.

Then derive absolute zeta zero-side summability from the already-proved inherited `zero_sum_inv_sq`. Do **not** introduce a duplicate weighted-zero-summability hypothesis.

No explicit-formula identity is claimed in #39.

### PR #40 — deterministic dictionary RHS / normalization theorem

**No zeros in this PR.** Define the neutral object

```text
dictionaryMatrix(L,N) := finiteMatrix(L,N) + 2*cCorrection(L)*I
```

and prove, for real `u`, channel by channel,

```text
literatureRHS(dictionaryTest_full(u,L))
  = quadraticForm(dictionaryMatrix(L,N), ofReal(u)).
```

where `dictionaryTest_full` denotes the full tent-plus-residual dictionary, not the smooth residual wrapper introduced in #38.

Acceptance checks:

```text
pole RHS  = quadratic pole channel
prime RHS = - quadratic primeComponent
arch RHS  = - quadratic archComponent + 2*cCorrection(L)*coefficientMass(u)
```

Prime-side factor-two smoke test:

```text
k(log n) + k(-log n) = 2*k(log n),
k(log n) = 1/2 * quadratic qBasis(log n,L).
```

Any sign/factor/diagonal mismatch stops the PR and reopens the normalization audit.

### PR #41 — tent-specific zeta explicit-formula extension

Use the inherited concrete zeta theorem `EF_lit_zetaZeroConfig`; do not add a new explicit-formula assumption.

The residual component already satisfies the current `EF_lit` regularity hypotheses by #38. The remaining work is the canonical tent:

1. construct a bounded `C_c^2` approximation family for the tent;
2. prove pole convergence;
3. prove prime convergence with a common finite prime support;
4. prove archimedean dominated convergence;
5. prove zero-side limit exchange using #39 decay plus inherited `zero_sum_inv_sq`.

A generic theorem `EF_lit Z -> EF_tent Z` is not the default target because `EF_lit` alone does not encode the uniform domination needed for the limit exchange. Prefer a zeta-specific theorem, or explicitly parameterize any generic version by the required zero-count/summability assumption.

### PR #42 — exact zero-side finite matrix bridge

Combine #40 and #41 to obtain the quadratic zero-side identity. Define `zeroSideMatrix`, not `Gram`, and recover the matrix identity by **real polarization** unless complex polarization becomes genuinely necessary.

Target normalization:

```text
zeroSideMatrix(L,N) = finiteMatrix(L,N) + 2*cCorrection(L)*I.
```

Only after this exact identity is compiled may the scalar-shift displacement theorem be transferred to the actual zero-side matrix.

### PR #43 — finite source quotient / information-loss API

Formalize exactly what fixed finite CCM data can and cannot see. Record the `2N+1` source moments and make information loss explicit rather than implicit.

### PR #44 — prime-cutoff / von Mangoldt flow

Formalize the prime-power event law, with normalization fixed by the production matrix conventions. Expected rank-one jump channel:

```text
Delta Q'_N(log q)
  = -2*Lambda(q)/(sqrt(q)*log q) * J.
```

This is distinct from the generic static rank-two Loewner displacement chassis.

### PR #45 — parity + extremal spectral API

Formalize reversal parity, the even/odd decomposition, and uniform-channel annihilation for reversal-odd real vectors. Do not infer that the uniform channel is an “RH mode,” and do not globally assert an extremal ordering before proving it.

### PR #46 — finite characteristic / XiHat API

Formalize the finite pole-cancelled characteristic entire function, removable nodes, exact interpolation, parity, and conditional real-root statements.

### PR #47 — barycentric eigenvector equation

Derive the exact arithmetic interpolation/eigenvector identity with all scales and signs fixed by Lean.

After #47: **HARD FREEZE.** Do not automatically invent #48. Run the finite-to-infinite route-selection gate.

## Finite-to-infinite firewall

Even after the exact finite bridge and finite spectral engine are complete, RH remains open. The actual hard wall must still be attacked by a theorem of the form

```text
normalized finite characteristic objects
  -> local uniform convergence to a nonzero Xi object
  -> sufficient real-root transfer,
```

or by a genuinely weaker finite obstruction theorem that forces an off-critical zero to violate a proved finite spectral property.

Every post-#47 route must state:

1. the exact missing theorem;
2. why it is weaker than RH rather than RH rewritten;
3. which already-formal finite structure attacks it;
4. a cheap falsifier / negative control;
5. the smallest theorem that would materially advance the route.

## Standing dumbassery gates

- `I != J`.
- Green CI != explicit-formula admissibility.
- Residual `C_c^2` != tent admissibility.
- Tent transform decay != explicit-formula limit exchange.
- Finite bridge != finite-to-infinite convergence.
- Real-`u` seam theorem != an arbitrary complex-coefficient theorem.
- Do not restrict to `sum u_i = 0` to erase the seam for the full bridge.
- Do not side-quest into `C^3`.
- Do not call an unconditional zero-side object `Gram` before positivity.
- Do not turn an external numerical/source oracle into theorem authority.
- Do not smuggle normalization in from the old doubled `WeilGram` diagnostic.
- Do not call the all-ones channel an RH mode.
- RH remains OPEN until an exact theorem chain proves it.

## Immediate next step

Finish and merge **PR #38** only after the exact theorem head and governance checks are green. Then begin **PR #39** with the canonical tent transform and strip-decay package. Do not invoke a new explicit-formula assumption and do not start the deterministic RHS work before the tent normalization surface is fixed.
