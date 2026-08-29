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
  `Zeta23.CCM.dictionaryTent_mollifier_architecture_package`;
- fixed-complex-frequency mollifier convergence is compiler-proved:
  `Zeta23.CCM.dictionaryTentMollifierTransform_tendsto_one` and
  `Zeta23.CCM.paperFT_dictionaryTentMollified_tendsto`;
- Route-M M4 pole convergence and M5 truncate-first prime convergence are compiler-proved:
  `Zeta23.CCM.dictionaryTent_pole_prime_limit_package`;
- Route-M M7 varying-family zero-side convergence is compiler-proved by Tannery:
  `Zeta23.CCM.dictionaryTent_zero_sum_mollified_tendsto`.

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

M0–M3 close the adapter architecture. M3.5 proves the normalized mollifier transform tends to one at every fixed complex frequency, M4–M5 separately close the pole and prime limit channels, M6 closes the archimedean dominated-convergence channel, and M7 closes the varying-family zero-side limit by Tannery using the existing literal-tent zero-side summability theorem. The literal-tent explicit formula is still open because M8 assembly remains.

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
M2d-1.5 fixed-frequency mollifier limit     REACHED
M2d-2 M4 pole limit                         REACHED
M2d-3 M5 prime truncate-first limit         REACHED
M2d-4 M6 archimedean DCT                    REACHED
M2d-5 M7 varying-family zero-side DCT       REACHED
M2d-6 M8 literal tent EF assembly           OPEN
M2e deterministic finite RHS identity      REACHED
H0 zero-sum concrete zeta EF bridge        REACHED
H1 smooth-core polarization                 REACHED
H2a codim-one matrix completion             REACHED
H2b actual zero-side matrix / rank<=2 gap   REACHED
H2+ literal-tent defect / rank<=1 collapse   REACHED
V0/V1 finite off-line visibility            OPEN
full finite zero-side bridge                 OPEN
finite-to-infinite closure                   OPEN
```

`R003_TENT_EF_EXTENSION` remains OPEN. M0–M3 prove the adapter, M3.5 proves fixed-frequency transform convergence, M4–M5 prove the pole/prime channel limits, M6 proves the archimedean dominated-convergence limit, and M7 proves the varying-family zero-side dominated convergence/Tannery limit. Only M8 assembly remains open.

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

**MERGED.** M0–M3 compiler-close the mollification adapter. The promoted endpoint is

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

### PR #55 — H2a codimension-one matrix completion

**MERGED.** The pure finite-dimensional theorem now proves that a symmetric complex matrix whose real pairing vanishes on the coefficient-sum-zero hyperplane has the canonical form

```text
A = 1 aᵀ + a 1ᵀ
```

with explicit pivot witness `a_i = A_i0 - A_00/2`, hence rank at most two. The minimum pivoted-basis-difference interface is also formalized and is the interface consumed by H2b.

### PR #56 — H2b actual zero-side matrix and seam localization

**MERGED.** The finite zeta zero-side matrix is now constructed entrywise only after absolute summability is proved. The production endpoints are

```text
Zeta23.CCM.dictionaryTransform_zero_sum_summable
Zeta23.CCM.dictionarySpectralMatrix_zero_entry_summable
Zeta23.CCM.zeroSideMatrix_basisDiff_pairing_eq_smoothCoreZeroPolarization
Zeta23.CCM.zeroSideDiscrepancy_eq_completion
Zeta23.CCM.rank_zeroSideDiscrepancy_le_two
```

and establish, for the actual zeta-dependent finite zero-side matrix,

```text
zeroSideMatrix - dictionaryMatrix = 1 aᵀ + a 1ᵀ
rank (zeroSideMatrix - dictionaryMatrix) <= 2.
```

This does **not** prove the discrepancy vanishes. `R003_CCM_BRIDGE`, the literal tent EF extension M4–M8, finite-to-infinite closure, and RH all remain OPEN.

### PR #57 — H2+ collapse to the literal-tent defect

**MERGED.** Smooth diagonal differences remove the common nonsmooth tent seam and lie in the inherited `C_c^2` explicit-formula class. Combining that diagonal rigidity with H2b forces the full actual discrepancy to be one scalar multiple of the all-ones matrix:

```text
zeroSideDiscrepancy = dictionaryTentDefect(hs,L) • J
rank zeroSideDiscrepancy <= 1
```

with

```text
dictionaryTentDefect(hs,L)
  = literal tent zero side - literatureRHS(literal tent).
```

The production endpoints are

```text
Zeta23.CCM.zeroSideDiscrepancy_diagonal_eq_center
Zeta23.CCM.zeroSideDiscrepancy_eq_tentDefect_smul_ones
Zeta23.CCM.rank_zeroSideDiscrepancy_le_one
Zeta23.CCM.zeroSideMatrix_eq_dictionaryMatrix_iff_tentDefect_eq_zero
```

The defect definition has no finite-size parameter `N`. Thus the finite matrix problem is now reduced, for every `N`, to the same literal-tent scalar obstruction. This does **not** prove that obstruction vanishes.

No reflection theorem or zero-side displacement inheritance is used. `R003_TENT_EF_EXTENSION`, `R003_CCM_BRIDGE`, finite-to-infinite closure, and RH remain OPEN.

### PR #58 — Route-M M3.5, M4 and M5

**MERGED.** The fixed-frequency and first two channel limit passages are compiler-checked.

Production endpoints:

```text
Zeta23.CCM.dictionaryTentMollifierTransform_tendsto_one
Zeta23.CCM.paperFT_dictionaryTentMollified_tendsto
Zeta23.CCM.dictionaryPoleRHS_dictionaryTentMollified_tendsto
Zeta23.CCM.dictionaryPrimeRHS_dictionaryTentMollified_tendsto
Zeta23.CCM.dictionaryTent_pole_prime_limit_package
```

The generic truncate-first theorem

```text
Zeta23.CCM.dictionaryPrimeRHS_eq_finset
```

is now upstream in `DictionaryDeterministicRHS.lean` and reused by the finite dictionary and Route M. For the mollified family the common support envelope is `[-(L+1), L+1]`, so the common finite prime range is controlled by `exp(L+1)`; truncating prematurely at `exp L` would be invalid.

Axiom audits for the new endpoint theorems report only

```text
[propext, Classical.choice, Quot.sound].
```

No explicit-formula hypothesis is used in M3.5–M5. `R003_TENT_EF_EXTENSION`, `R003_CCM_BRIDGE`, finite-to-infinite closure, and RH remain OPEN.

### PR #59 — Route-M M7 zero-side Tannery limit

**MERGED.** The varying-family zero-side limit is compiler-checked.

Production endpoints:

```text
Zeta23.CCM.dictionaryTent_zero_sum_mollified_tendsto_gen
Zeta23.CCM.dictionaryTent_zero_sum_mollified_tendsto
```

For each fixed zero, M3.5 supplies transform convergence. The exact M2 factorization and the unconditional closed-strip bound give
```text
‖dictionaryTentMollifierTransform n (gammaOf rho)‖ <= exp(1/2),
```
so every mollified zero summand is dominated by `exp(1/2)` times the norm of the corresponding literal-tent zero summand. The existing literal-tent zero series is already summable; pinned Mathlib's `tendsto_tsum_of_dominated_convergence` then performs the limit/`tsum` exchange.

No new zero counting, reflection pairing, critical-line assumption, or explicit-formula assumption is introduced. This closes M7 only. `R003_TENT_EF_EXTENSION`, `R003_CCM_BRIDGE`, finite-to-infinite closure, and RH remain OPEN.

### PR #60 — Route-M M6 archimedean dominated-convergence limit

**CURRENT CLOSURE PR.** The archimedean varying-family limit is compiler-checked.

Production endpoint:

```text
Zeta23.CCM.dictionaryArchRHS_dictionaryTentMollified_tendsto
```

The proof first establishes real-axis integrability of the literal tent transform, then square-root-weighted integrability using the inherited `mu - mu 0` growth bound, then integrability of the full literal-tent gamma-density integrand. The exact mollifier factorization and the unconditional real-axis specialization of the `exp(1/2)` strip bound provide the fixed integrable dominator consumed by pinned Mathlib's `tendsto_integral_of_dominated_convergence`.

The theorem-level axiom audit reports only

```text
[propext, Classical.choice, Quot.sound].
```

No explicit-formula identity, zero-side theorem, critical-line assumption, or new gamma asymptotic is introduced. This closes M6 only. `R003_TENT_EF_EXTENSION`, `R003_CCM_BRIDGE`, finite-to-infinite closure, and RH remain OPEN.

## Current theorem sequence

The next production sequence is no longer “finish tent EF first at all costs.”

### H2a — codimension-one matrix completion — REACHED

PR #55 proves the finite linear-algebra theorem:

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

### H2b — actual zero-side matrix, legally — REACHED

PR #56 implements the legal route without treating `dictionaryTransform` as linear in coefficients.

What is now formal:

1. exact tent+residual decomposition gives arbitrary-real-`u` zero-side absolute summability;
2. finite quadratic polarization gives entrywise spectral-matrix summability;
3. `zeroSideMatrix` is defined entrywise from those absolutely convergent zero sums;
4. pivoted basis-difference pairings agree with the H1 smooth-core polarization;
5. for
   ```text
   A = zeroSideMatrix - dictionaryMatrix;
   ```
   H2a gives
   ```text
   A = 1 aᵀ + a 1ᵀ
   ```
   and rank at most two.

No unrestricted complex-coefficient bridge, positivity, or full matrix equality is claimed. Use the name `zeroSideMatrix`, not `Gram`, until positivity is actually proved.

### H2+ — literal-tent scalar collapse — REACHED

PR #57 proves the stronger production form

```text
A = zeroSideMatrix - dictionaryMatrix
  = dictionaryTentDefect(hs,L) • J,
```

hence `rank A <= 1`.

The key route is not displacement: all diagonal basis tests share the same literal tent seam, and subtracting the centered zero-frequency diagonal leaves an already-proved smooth residual. The inherited `C_c^2` explicit formula therefore makes every diagonal discrepancy equal; H2b then forces the completion vector to be constant.

The exact finite bridge is now equivalent to

```text
dictionaryTentDefect(hs,L) = 0.
```

Reflection is superseded for this collapse. Do not infer zero-side displacement inheritance from the deterministic matrix.

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

## Active Route-M completion: M8

PR #57 makes the literal tent EF load-bearing: killing the single `dictionaryTentDefect(hs,L)` scalar closes the finite zero-side matrix bridge for every finite dictionary size.

PR #58 removes the fixed-frequency, pole and prime limit obligations, PR #59 removes the varying-family zero-side limit obligation, and PR #60 removes the archimedean dominated-convergence obligation. The remaining stage is:

- **M8** apply `EF_lit_zeta` to each mollified test, pass all channels separately, and assemble the literal tent EF.

M6 and M7 are now closed with fixed domination arguments: M6 uses an integrable literal-tent gamma-density majorant, while M7 uses the already-summable literal-tent zero series. No new gamma asymptotic or weighted zero-counting machinery was needed.

Only M8 can promote `R003_TENT_EF_EXTENSION`.

## Downstream finite-to-infinite program

After the literal-tent defect is settled and the full finite bridge closes, revisit the hard finite-to-infinite routes.

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

PR #60 compiler-closes M6 archimedean dominated convergence, completing the four separate Route-M limit channels M4–M7. Keep the claim firewall unchanged: no RHRC claim is promoted before M8 assembly.

The active mathematical target remains

```text
dictionaryTentDefect(hs,L) = 0
```

for every positive aperture `L`.

Highest-information next move: perform **M8 assembly** of the literal-tent explicit formula from the already-closed pole, prime, archimedean, and zero-side channel limits. Only after the exact M8 theorem compiles should the tent defect be discharged and the finite bridge consumed.

Do not promote `R003_TENT_EF_EXTENSION` or `R003_CCM_BRIDGE` before the exact final M8 theorem compiles.
