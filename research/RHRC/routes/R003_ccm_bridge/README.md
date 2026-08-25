# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **ACTIVE / PARTIAL CLOSURE**. RH remains **OPEN**.

This file is the active route SSOT. It records the theorem boundary after the deterministic dictionary-RHS completion in PR #42. Lean and the RHRC claim registry remain the authority for theorem status; this route document records sequencing and non-claim discipline.

## Authority and proof-status discipline

Authority hierarchy:

```text
Lean / exact comparator theorem checks   mathematical authority
RHRC claim registry + receipts           provenance / governance
external connes-cvs Python               oracle / falsifier only
finite numerics                          diagnostic only
```

Nothing promotes itself. Green CI does not imply an explicit-formula theorem, a deterministic RHS identity does not imply a zero-side bridge, a finite bridge does not imply a finite-to-infinite theorem, and none of the finite CCM results are RH evidence by themselves.

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

- exact first-order seam factorization `K'_u(0) = K'_u(1) = 2*sigma(u)^2`;
- first and second residual branch jets at `-L`, `0`, and `L`;
- the smooth residual is globally glued into a complex-valued `C_c^2` test for every real `u` and `L>0` (`R003_RESIDUAL_C2`);
- the canonical tent has compact support, exact native-`paperFT` transform, strip decay, and multiplicity-weighted zero-side absolute summability (`R003_TENT_ANALYTICS`);
- the deterministic literature explicit-formula RHS of the **full real dictionary** is exactly the production quadratic form (`R003_CCM_RHS_IDENTITY`):

```text
literatureRHS(dictionaryTest N (ofReal u) L)
  = quadraticForm(dictionaryMatrix(L,N), ofReal u),

dictionaryMatrix(L,N)
  = finiteMatrix(L,N) + 2*cCorrection(L)*I.
```

The deterministic identity is zero-free and was proved channel by channel: pole, prime, and archimedean. The prime channel truncates the raw prime `tsum` to common finite support **before** any coefficient-sum reordering. The archimedean channel includes the diagonal scalar correction `2*cCorrection(L)` and requires no `sum_i u_i = 0` restriction.

The raw dictionary itself is not claimed to be globally `C^1`: its universal tent channel carries the first-derivative seam. The residual is the smooth part; the tent is the remaining nonsmooth part. **Tent transform/decay/summability is not the tent explicit-formula extension.**

## Normalization lock

The external Groskin / Connes–van Suijlekom / CCM reference implementation remains outside the Lean theorem dependency graph. It is an oracle/falsifier only.

The frozen source audit distinguishes:

```text
M         fork-owned formal CCM matrix
Q_inf     cutoff-free finite Guinand–Weil / CvS matrix
WeilGram  older doubled explicit-formula diagnostic normalization
```

The production target is

```text
Q_inf = M + 2*cCorrection(L)*I,
```

while the older diagnostic used

```text
WeilGram = 2*M + 4*cCorrection(L)*I = 2*Q_inf.
```

**Do not import the old factor two into the production dictionary theorem.** The production dictionary contains an explicit factor `1/2`, and the compiled deterministic theorem targets

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
M2d admissible full dictionary family  OPEN
M2e deterministic finite RHS identity  REACHED
M2f exact zero-side / CCM bridge       OPEN
```

`M2d` remains open because the canonical nonsmooth tent still needs a justified zeta explicit-formula extension. `M2e` is now compiler-proved independently of zeros. `M2f` cannot be promoted until the full dictionary zero-side explicit-formula identity is compiled.

## Implemented chronology

### PR #35 — finite Guinand–Weil dictionary core

**MERGED.** Delivered `sourceContract`, the exact source/qBasis contraction bridge, `dictionaryTest`, and `dictionaryTransform = Zeta23.paperFT(dictionaryTest)`.

### PR #36 — finite dictionary topology / normalization

**MERGED.** Delivered the reusable quadratic-form convention, `sourceMatrix(1)=2I`, coefficient mass, endpoint/center identities, evenness, compact support, and continuity.

### PR #37 — analytic seam isolation

**MERGED.** Delivered the exact coefficient-sum seam channel, tent-plus-residual decomposition, residual endpoint/center jets, second-order calculus, and center second-derivative agreement.

### PR #38 — global residual `C_c^2` closure

**MERGED.** Compiler-checked `dictionaryResidualTest_admissible` and the supporting global residual regularity/compact-support theorems. This is the smooth residual only, not the nonsmooth tent.

### PR #39 — canonical tent transform + strip decay + zero summability

**MERGED.** Compiler-checked `dictionaryTent_analytic_package`, including the exact transform, multiplied quadratic strip bound, and concrete zeta zero-side absolute summability. This did **not** prove the tent explicit-formula limit passage.

### PR #40 — unrelated repository work

PR #40 was not the deterministic R003 step anticipated by an older version of this route document. Do not use the obsolete numbering as proof-state authority.

### PR #41 — deterministic RHS foundation

**MERGED.** Began the zero-free deterministic RHS/normalization program and established the initial production normalization surface, but did not yet prove the full advertised dictionary identity.

### PR #42 — deterministic dictionary RHS completion

**CURRENT CLOSURE PR.** Proves and RHRC-binds

```text
Zeta23.CCM.literatureRHS_dictionaryTest_eq_quadraticForm
```

for real coefficients and `L>0`, with

```text
dictionaryMatrix(L,N) = finiteMatrix(L,N) + 2*cCorrection(L)*I.
```

The theorem is compiler-bound in `ClaimBindings.lean`; its theorem-level axiom audit reports only

```text
[propext, Classical.choice, Quot.sound].
```

No project-added axiom or `sorry` is introduced. `R003_CCM_RHS_IDENTITY` is `PROVED_UNCONDITIONAL`; the tent EF extension, kernel EF extension, zero-side bridge, positivity, finite-to-infinite closure, and RH remain open.

## Next theorem sequence — no fabricated PR numbers

Future work is named by theorem obligation until an actual PR exists.

### A. Tent-specific zeta explicit-formula extension

Target claim: `R003_TENT_EF_EXTENSION`.

Use the inherited concrete zeta theorem `Zeta23.WeilEF.EF_lit_zeta`; do not add a new explicit-formula assumption. The residual component already satisfies the inherited regularity hypotheses. The remaining work is the canonical tent:

1. construct a bounded `C_c^2` approximation family;
2. prove pole convergence;
3. prove prime convergence with a common finite prime support;
4. prove archimedean dominated convergence;
5. prove zero-side limit exchange using the compiled tent decay/summability and inherited weighted zero summability.

A generic theorem `EF_lit Z -> EF_tent Z` is not the default target because `EF_lit` alone does not encode the uniform domination needed for the limit exchange.

### B. Full dictionary kernel explicit-formula extension

Target claim: `R003_KERNEL_EF_EXTENSION`.

Combine the already-admissible smooth residual with the tent-specific extension to identify the concrete zeta zero-side sum of `dictionaryTransform` with `literatureRHS` of the full dictionary. Do not re-prove the deterministic RHS algebra here; consume `R003_CCM_RHS_IDENTITY`.

### C. Exact zero-side finite matrix bridge

Target claim: `R003_CCM_BRIDGE`.

Combine `R003_KERNEL_EF_EXTENSION` with `R003_CCM_RHS_IDENTITY` and recover the matrix identity by **real polarization** unless complex polarization becomes genuinely necessary.

Target normalization:

```text
zeroSideMatrix(L,N) = finiteMatrix(L,N) + 2*cCorrection(L)*I.
```

Call the unconditional object `zeroSideMatrix`, not `Gram`, until positivity is proved. Only after this exact identity is compiled may the scalar-shift displacement theorem be transferred to the actual zero-side matrix.

### D. Finite structural engine

After the exact zero-side bridge, continue the already-motivated finite structural work—information-loss/source quotient, prime-cutoff/von Mangoldt flow, parity/extremal spectral structure, finite characteristic objects, and barycentric/eigenvector identities—without inventing PR numbers in advance.

### E. Finite-to-infinite route-selection gate

Do not automatically continue from finite structure to an RH claim. Run the route-selection gate once the finite engine is mature.

## Finite-to-infinite firewall

Even after the exact finite bridge and finite spectral engine are complete, RH remains open. The hard wall must still be attacked by a theorem such as

```text
normalized finite characteristic objects
  -> local uniform convergence to a nonzero Xi object
  -> sufficient real-root transfer,
```

or by a genuinely weaker finite obstruction theorem forcing an off-critical zero to violate a proved finite spectral property.

Every finite-to-infinite route must state:

1. the exact missing theorem;
2. why it is weaker than RH rather than RH rewritten;
3. which already-formal finite structure attacks it;
4. a cheap falsifier / negative control;
5. the smallest theorem that would materially advance the route.

## Standing dumbassery gates

- `I != J`.
- Green CI != explicit-formula admissibility.
- Residual `C_c^2` != tent admissibility.
- Tent transform decay/summability != explicit-formula limit exchange.
- Deterministic RHS identity != zero-side bridge.
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

Close PR #42 only after its cleanup head re-passes the exact RHRC, normalization, `Zeta23.CCM`, `Zeta23.ExceptionalZero`, theorem-axiom, and no-placeholder gates. Then attack `R003_TENT_EF_EXTENSION`; after that, prove `R003_KERNEL_EF_EXTENSION`, and only then construct the exact zero-side finite matrix bridge.
