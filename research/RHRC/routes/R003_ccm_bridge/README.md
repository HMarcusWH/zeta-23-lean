# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **ACTIVE / PARTIAL CLOSURE**. RH remains **OPEN**.

This file is the active route SSOT for R003. Lean and the RHRC claim registry are theorem authority; this route document records sequencing, architecture decisions, and claim boundaries.

## Authority and proof-status discipline

Authority hierarchy:

```text
Lean / exact comparator theorem checks   mathematical authority
RHRC claim registry + receipts           provenance / governance
external connes-cvs Python               oracle / falsifier only
finite numerics                          diagnostic only
```

Nothing promotes itself. Green CI does not imply a tent explicit-formula theorem, a deterministic RHS identity does not imply a zero-side bridge, a finite bridge does not imply a finite-to-infinite theorem, and none of the finite CCM results are RH evidence by themselves.

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
- exact first-order seam factorization and the first/second residual branch jets;
- the residual is globally `C_c^2` for every real `u` and `L>0` (`R003_RESIDUAL_C2`);
- the canonical tent has exact `paperFT`, critical-strip quadratic decay, and concrete zeta zero-side absolute summability (`R003_TENT_ANALYTICS`);
- the deterministic literature explicit-formula RHS of the full real dictionary is exactly the production quadratic form (`R003_CCM_RHS_IDENTITY`);
- the zero-sum dictionary case is already a concrete zeta explicit-formula theorem:
  `Zeta23.CCM.zeroSum_dictionaryTest_zero_sum_eq_quadraticForm`;
- smooth-core polarization on the coefficient-sum-zero hyperplane is compiler-proved:
  `Zeta23.CCM.smoothCoreZeroPolarization_eq_realMatrixPairing`;
- Route M M0–M3 is compiler-proved as a local adapter around the literal tent:
  `Zeta23.CCM.dictionaryTent_mollifier_architecture_package`.

The deterministic RHS identity remains zero-free and was proved channel by channel. The prime channel truncates the raw prime `tsum` to common finite support **before** coefficient-sum reordering. The archimedean channel includes the diagonal scalar correction `2*cCorrection(L)` and requires no `sum_i u_i = 0` restriction.

The raw dictionary itself is not globally `C^1`: its universal tent channel carries the first-derivative seam. The residual is the smooth part; the tent is the remaining nonsmooth part.

**Tent transform/decay/summability + mollifier architecture is still not the tent explicit-formula extension.**

## Route-M architecture now proved

For `L>0`, the canonical mollifier family has:

1. normalized shrinking positive radius `1/(n+1)`;
2. `C²` mollified tents;
3. compact support;
4. pointwise convergence to the literal existing `dictionaryTent`;
5. exact complex-frequency factorization
   ```text
   paperFT(mollified tent)(z)
     = mollifierTransform(n,z) * paperFT(literal tent)(z);
   ```
6. a uniform critical-strip bound on the mollifier transform;
7. inherited uniform quadratic strip decay;
8. one common physical support envelope independent of `n`:
   ```text
   support(dictionaryTentMollified L n) ⊆ [-(L+1), L+1].
   ```

The neutral helper `Zeta23.paperFT_mul_convolution_eq_of_continuous_compactSupport` obtains complex-frequency convolution factorization by exponential tilting and the existing real Fourier convolution theorem. No central `WeilEF` interface was weakened or rewritten.

This closes the **M0–M3 architecture gate only**.

## Route-G disposition

The direct-tent Guinand–Weil spike (Route G) produced useful local-only evidence, but it required broad surgery around the central `ContDiff ℝ 2` explicit-formula interface and is **REJECTED as the production architecture**.

Its status must remain truthful:

- the original scratch source was not recoverable from live repository history;
- no reconstructed source may be presented as the original compiler object;
- the archival evidence branch is `archive/t1-route-g-evidence-20260828`;
- Route M is now the production route.

The successful M2 factorization is especially important here: it shows that the feared need for a new complex Fourier / direct nonsmooth EF interface did not materialize.

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

**Do not import the old factor two into the production dictionary theorem.**

Also keep the two low-rank objects separate:

```text
I = identity matrix                 scalar normalization channel
J = 1 1^T                           rank-one coefficient-sum seam channel
```

`I != J`.

## Milestones

```text
M2a finite dictionary core                 REACHED
M2b finite topology / normalization        REACHED
M2c analytic seam isolation                REACHED
M2d-0 tent transform/decay/summability     REACHED
M2d-1 Route-M M0-M3 adapter architecture   REACHED
M2d-2 literal tent explicit formula M4-M8  OPEN
M2e deterministic finite RHS identity      REACHED
H0 zero-sum concrete zeta EF bridge        REACHED
H1 smooth-core polarization                 REACHED
H2a codim-one matrix completion             OPEN
H2b actual zero-side matrix / rank<=2 gap   OPEN
H2+ displacement-collapse attempt           OPEN
V0/V1 finite off-line visibility            OPEN
full finite zero-side bridge                 OPEN
finite-to-infinite closure                   OPEN
```

`R003_TENT_EF_EXTENSION` remains OPEN. M0–M3 prove that mollification is a viable adapter into the inherited `C²` EF machinery; they do not perform the limit passage.

## Implemented chronology relevant to the live frontier

### PR #35–#39 — dictionary core, residual, and tent analytics

**MERGED.** These PRs built the finite dictionary, seam decomposition, globally `C_c^2` residual, exact tent transform/decay, and concrete zero-side tent summability.

### PR #41–#42 — deterministic RHS normalization and completion

**MERGED.** The production theorem is

```text
Zeta23.CCM.literatureRHS_dictionaryTest_eq_quadraticForm
```

with

```text
dictionaryMatrix(L,N) = finiteMatrix(L,N) + 2*cCorrection(L)*I.
```

### Subsequent H0/H1 work

The repository now also proves the zero-sum concrete zeta EF identity and smooth-core polarization. These facts materially change the route: the full tent EF extension is no longer the only useful next move.

### PR #53 — Route-M canonical tent mollifier architecture

**CURRENT CLOSURE PR.** M0–M3 compiler-close the mollification adapter. The promoted endpoint is

```text
Zeta23.CCM.dictionaryTent_mollifier_architecture_package
```

and its theorem-level axiom audit reports only

```text
[propext, Classical.choice, Quot.sound].
```

This is **not** `R003_TENT_EF_EXTENSION`.

### PR #54 — countable two-translate detector consequences

**MERGED.** Tail negativity and the explicit countable-bank critical-line criterion are now formal theorems in `TwoTranslateCountableCriterion.lean`.

These are useful structural facts but the countable-bank positivity statement remains RH-equivalent. The X-lane is therefore **STOPPED as an attack route**: do not create an X4.7 that merely repackages the same RH-strength burden.

## Next theorem sequence

The next production sequence is no longer “finish tent EF first at all costs.”

### H2a — codimension-one matrix completion

Prove the finite linear-algebra theorem:

If a symmetric matrix `A` satisfies

```text
uᵀ A v = 0
```

for all real `u,v` in the coefficient-sum-zero hyperplane `1⊥`, then there exists a vector `a` such that

```text
A = 1 aᵀ + a 1ᵀ,
```

hence `rank A <= 2`.

Preferred proof: pivot at coordinate 0, test `e_i-e_0` and `e_j-e_0`, derive the entry identity, then package the representation before the rank wrapper.

### H2b — actual zero-side matrix, legally

Do **not** treat `dictionaryTransform` as linear in coefficients; it is quadratic.

Safe route:

1. use the exact tent+residual decomposition to prove arbitrary-real-`u` zero-side summability;
2. define the zero-side quadratic functional `Q_Z(u)`;
3. polarize `Q_Z` to a symmetric bilinear form `B_Z(u,v)`;
4. define the finite `zeroSideMatrix` from basis values/polarization;
5. use H1 on `1⊥`;
6. set
   ```text
   A = zeroSideMatrix - dictionaryMatrix;
   ```
7. apply H2a to obtain
   ```text
   A = 1 aᵀ + a 1ᵀ
   ```
   and rank at most two.

Use the name `zeroSideMatrix`, not `Gram`, until positivity is actually proved.

### H2+ — bounded collapse attempt

Test whether parity/reflection and any **legally proved** zero-side displacement identity force the rank-two discrepancy from H2b to collapse further.

Do not assume displacement inheritance. If no cheap proof exists, stop and retain the honest rank-at-most-two discrepancy theorem.

### V0/V1 — finite visibility

Then test the smallest exact finite visibility problem.

For `N=1`, use explicit coefficient-sum-zero probes and an off-critical zero `ρ`, write the visible transform vector as `v=x+iy`, and investigate

```text
GramDet(x,y) = ||x||² ||y||² - <x,y>².
```

First perform symbolic/adversarial degeneracy checks. Only if they survive should this become a Lean theorem target.

If visibility is obtained, the pair block has the already-known signed form

```text
B_ρ = c (x xᵀ - y yᵀ),   c > 0,
```

with explicit negative direction. Immediately run the finite-family moustache test before treating any positivity statement as a plausible weaker target.

## Deferred Route-M completion: M4–M8

Finish the literal tent EF only when it becomes load-bearing.

Remaining stages:

- **M4** pole evaluations converge;
- **M5** prime channel: common finite truncation **first**, then termwise limit;
- **M6** archimedean dominated convergence;
- **M7** varying-family zero-side DCT/Tannery; fixed-test `ZeroSumLimit` is not enough;
- **M8** apply `EF_lit_zeta` to each mollified test, pass all channels separately, assemble the literal tent EF.

Only M8 can promote `R003_TENT_EF_EXTENSION`.

## Downstream finite-to-infinite program

After H2/V work clarifies the finite obstruction space, revisit the hard finite-to-infinite routes.

### Bombieri branch

The hard issue is not finite negativity but whether the negative eigenvalue can collapse to zero as `N→∞`. Any route must attack that limit directly and should compose with the now-formal tail-complete detector bank rather than re-prove detector selection.

### Connes / FTI branch

A genuine RH-closing chain still needs something like:

```text
normalization map
  -> controlled finite ground state / minimizer
  -> strong approximation of the analytic proxy
  -> local-uniform Fourier convergence to Xi
  -> real-zero transfer (e.g. Hurwitz)
```

The hard points remain the spectral/minimizer control and the finite-to-infinite passage.

## Standing dumbassery gates

- `I != J`.
- Green CI != tent explicit-formula admissibility.
- Residual `C_c^2` != tent admissibility.
- Tent transform decay/summability != explicit-formula limit exchange.
- Mollifier M0–M3 architecture != M4–M8 EF limit passage.
- Deterministic RHS identity != zero-side bridge.
- H1 on `1⊥` != full matrix equality.
- `dictionaryTransform` is quadratic in coefficients, not linear.
- Real-`u` seam theorem != arbitrary complex-coefficient theorem.
- Do not erase the full bridge by imposing `sum u_i = 0`.
- Do not side-quest into `C^3`.
- Do not call an unconditional zero-side object `Gram` before positivity.
- R002 off-line pair block is `c(xxᵀ-yyᵀ)`, not a Hermitian outer product.
- Common translation cancels exactly in the Weil form; amplification needs relative translation/nontrivial deformation.
- Finite negative inertia does not imply infinite negativity; a finite negative eigenvalue may tend to zero.
- No finite dictionary completeness assumption.
- Rank-two displacement is generic divided-difference structure, not RH evidence.
- X4 / universal countable-bank positivity is RH-strength.
- Numerics are only EXPERIMENTAL SIGNAL.
- Run the moustache test before universal positivity/boundedness/subexponentiality claims.
- LOCAL-COMPILED != LIVE.
- Yielded output != green; completed compiler/process gates are authority.
- RH remains OPEN until an exact theorem chain proves it.

## Immediate next step

After PR #53 itself re-passes the promoted claim binding, RHRC registry, normalization, `Zeta23.CCM`, `Zeta23.ExceptionalZero`, theorem-axiom, and no-placeholder gates, merge it.

Then start **H2a codimension-one matrix completion**, followed by **H2b actual zero-side matrix construction**. Do not automatically spend the next PR on M4–M8 unless H2/V work makes the literal tent EF extension load-bearing.
