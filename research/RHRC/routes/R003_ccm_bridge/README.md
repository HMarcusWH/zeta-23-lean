# R003 — CCM / finite Guinand–Weil / zero-side bridge

Status: **FINITE CLOSURE REACHED / D0 + G0 SETTLED / G1-A REACHED / G1-B0 SOURCE-NORMALIZATION FIREWALL REACHED / SOURCE CONSISTENCY NEXT**. RH remains **OPEN**.

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
  `Zeta23.CCM.dictionaryTent_zero_sum_mollified_tendsto`;
- PR #64's historical raw-kernel reconciliation is theorem-authoritative:
  `rawKernelZeroSideMatrix = 2*zeroSideMatrix = 2*finiteMatrix + 4*cCorrection(L)*I`;
- D0-C / PR #65 independently defines the cutoff-free CCM/CvS source convention and proves
  `zeroSideMatrix = cutoffFreeMatrix = finiteMatrix + 2*cCorrection(L)*I` on the full centered `2N+1` basis;
- PR #65 also theorem-locks the source parameter map `c = lambda^2`, equivalently `log c = 2*log lambda` for positive `lambda`.

The deterministic RHS identity remains zero-free and was proved channel by channel. The prime channel truncates the raw prime `tsum` to common finite support **before** coefficient-sum reordering. The archimedean channel includes the diagonal scalar correction `2*cCorrection(L)` and requires no `sum_i u_i = 0` restriction.

The raw dictionary itself is not globally `C^1`: its universal tent channel carries the first-derivative seam. The residual is the smooth part; the tent is the remaining nonsmooth part.

**Tent transform/decay/summability and M0–M7 alone were not the tent explicit-formula extension. PR #61 now completes M8 and compiler-proves the literal-tent explicit formula.**

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

M0–M3 close the adapter architecture. M3.5 proves the normalized mollifier transform tends to one at every fixed complex frequency, M4–M5 separately close the pole and prime limit channels, M6 closes the archimedean dominated-convergence channel, and M7 closes the varying-family zero-side limit by Tannery using the existing literal-tent zero-side summability theorem. PR #61 now completes M8 by composing those already-closed channels with `EF_lit_zeta` on the smooth mollified family and uniqueness of limits. Route M M0–M8 is therefore complete.

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
M2d-6 M8 literal tent EF assembly           REACHED
M2e deterministic finite RHS identity      REACHED
H0 zero-sum concrete zeta EF bridge        REACHED
H1 smooth-core polarization                 REACHED
H2a codim-one matrix completion             REACHED
H2b actual zero-side matrix / rank<=2 gap   REACHED
H2+ literal-tent defect / rank<=1 collapse   REACHED
full finite zero-side bridge                 REACHED
full real dictionary EF extension             REACHED
actual zero-side displacement                 REACHED
R003 finite theorem program                   REACHED
V0/V1 finite off-line visibility              OPEN
finite-to-infinite closure                    OPEN
```

`R003_TENT_EF_EXTENSION` and `R003_CCM_BRIDGE` are REACHED. PR #63 closes the two remaining theorem-level R003 obligations downstream of that bridge: the full arbitrary-real finite-dictionary explicit-formula identity and the actual production zero-side displacement identity/rank bound. Finite visibility, masking, negative persistence, finite-to-infinite closure, and RH remain OPEN.

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

**MERGED.** The archimedean varying-family limit is compiler-checked.

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

### PR #61 — Route-M M8 literal-tent EF assembly

**MERGED.** Permanent main merge: `7362cecb1988604d32d26d59b8a1d82b1e4ea4d5`. Its Git tree `be24e0d0b43224117ddeb01378f4a868210e1323` is exactly the same tree as the final CI-tested synthetic merge `ead0e0ae902c6056726b7a68e84ac836018db013`.

Production endpoints:

```text
Zeta23.CCM.literatureRHS_dictionaryTentMollified_tendsto
Zeta23.CCM.dictionaryTent_zero_sum_eq_literatureRHS
Zeta23.CCM.dictionaryTent_explicitFormula
```

M8 applies `EF_lit_zeta` only to each smooth compactly supported mollified tent. PR #58 supplies pole and truncate-first prime convergence, PR #60 supplies archimedean dominated convergence, and PR #59 supplies zero-side Tannery convergence.

The mollified zero-side and literature-RHS sequences are exactly equal termwise; uniqueness of limits then gives the literal-tent explicit formula.

The first exact tested synthetic merge was

```text
77afd6a428f6e720221abdd40e8e6a9abe2c625a
```

and the new endpoints depend only on

```text
[propext, Classical.choice, Quot.sound].
```

No new zero-counting result, gamma asymptotic, mollifier estimate, regularity assumption, critical-line assumption, or direct nonsmooth application of `EF_lit_zeta` was introduced.

### PR #62 — exact finite zero-side CCM bridge

**MERGED.** Permanent main merge: `5288c90c0fa0175bed2428ed69682fa0e9b3aa1b`. Its Git tree `8bebadfa128d04d49cd850af8c2ea27d950bb017` is exactly the same tree as the final CI-tested synthetic merge `f498c2a69c34569bae952c1404e004150432fdc5`.

Production endpoints:

```text
Zeta23.CCM.dictionaryTentDefect_eq_zero
Zeta23.CCM.zeroSideDiscrepancy_eq_zero
Zeta23.CCM.zeroSideMatrix_eq_dictionaryMatrix
Zeta23.CCM.zeroSideMatrix_eq_finiteMatrix_add_correction
```

The proof consumes the post-#57/#61 compressed route directly:

```text
literal-tent zero side = literatureRHS(literal tent)   (#61 / M8)
                         ↓
dictionaryTentDefect(hs,L) = 0
                         ↓
zeroSideMatrix = dictionaryMatrix                      (#57 / H2+)
                         ↓
zeroSideMatrix = finiteMatrix + 2*cCorrection(L)*I
```

The first compiler checkpoint deliberately contained only the load-bearing defect-zero and exact-matrix-equality theorems. `lake build Zeta23.CCM` passed on that checkpoint before claim promotion was added.

This closes the same production bridge claim for every finite `N`; it does not by itself prove the arbitrary-real full kernel EF, zero-side displacement, positivity, finite-to-infinite persistence, or RH. The registry records the proof-route adaptation explicitly: the mathematical claim is unchanged, but `R003_KERNEL_EF_EXTENSION` is no longer a prerequisite because H2+ reduced the full finite discrepancy to the single N-independent tent defect.

### PR #63 — final R003 kernel EF and production displacement closure

**IMPLEMENTED IN THIS PR; theorem checkpoint green before claim promotion.**

The pre-promotion checkpoint head

```text
89ef51add8ac4f5987661e388bb59e45c989d5eb
```

passed `Build CCM formalization` with both new theorem files imported by `Zeta23.CCM`.

Production endpoints:

```text
Zeta23.CCM.dictionaryTransform_zero_sum_eq_quadraticForm_zeroSideMatrix
Zeta23.CCM.dictionaryTransform_zero_sum_eq_literatureRHS
Zeta23.CCM.dictionaryTransform_explicitFormula
Zeta23.CCM.zeroSideMatrix_displacement
Zeta23.CCM.rank_zeroSideMatrix_displacement_le_two
```

The kernel-EF proof direction is now the reverse of the original build plan:

```text
entrywise absolutely summable spectral zero side
                         ↓ finite contraction
quadraticForm(zeroSideMatrix,u)
                         ↓ #62
quadraticForm(dictionaryMatrix,u)
                         ↓ deterministic RHS identity
literatureRHS(dictionaryTest(u)).
```

Thus no new nonsmooth explicit-formula limit passage is needed for the full real dictionary once the exact basis matrix bridge is theorem-authoritative.

For displacement, PR #63 instantiates the already-proved generic transfer theorem with

```text
A = zeroSideMatrix
M = finiteMatrix
k = 1
c = 2*cCorrection(L).
```

The scalar correction disappears from the commutator, so the production zero-side displacement is exactly the formal CCM displacement with **no factor two**. At the #63 freeze this did not yet identify the older doubled R002 diagnostic raw-kernel convention.

### PR #64 — downstream historical raw-kernel reconciliation

**THEOREM CHECKPOINT GREEN before claim/document promotion.**

PR #64 consumes the already-proved production bridge rather than reopening any
explicit-formula channel. The historical R002-D test is exactly the unhalved
`kernel`, while `dictionaryBasisTest = 1/2 * kernel`. Lean therefore proves

```text
rawKernelZeroSideMatrix
  = 2 * zeroSideMatrix
  = 2 * finiteMatrix + 4*cCorrection(L)*I,
```

and correspondingly

```text
[indexMatrix, rawKernelZeroSideMatrix]
  = 2*(g 1^T - 1 g^T),
rank <= 2.
```

This closes the corrected historical normalization that the old numerical audit
predicted. The original statement `M = 1/2*WeilGram` **remains refuted as
stated**; #64 proves its diagonal-shift successor. The result concerns the
centered truncated-character `qBasis/kernel` convention only and does not
identify the general R002-A taper-grid `G̃(T)`.

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

The exact finite bridge was reduced to

```text
dictionaryTentDefect(hs,L) = 0.
```

PR #62 now consumes M8 to prove that scalar vanishes, hence the entire finite discrepancy vanishes and

```text
zeroSideMatrix hs N L = dictionaryMatrix L N
```

for every finite `N`. Reflection remains superseded for this collapse. PR #63 then proves the actual zero-side displacement downstream from this exact bridge by consuming the generic scalar-shift transfer theorem with production scale `k = 1`.

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

## Route-M completion — M0–M8 REACHED

PR #57 makes the literal tent EF load-bearing: killing the single `dictionaryTentDefect(hs,L)` scalar closes the finite zero-side matrix bridge for every finite dictionary size.

PR #58 closes the fixed-frequency, pole, and prime limit obligations; PR #59 closes the varying-family zero-side limit; PR #60 closes the archimedean dominated-convergence limit; and PR #61 composes those channels with the smooth inherited explicit formula to close M8.

Current R003 theorem state after the PR #65 D0-C representation checkpoint:

```text
PROVED:
  literal tent zero side = literatureRHS(literal tent)
  dictionaryTentDefect(hs,L) = 0
  zeroSideDiscrepancy hs N L = 0
  zeroSideMatrix hs N L = dictionaryMatrix L N
  zeroSideMatrix hs N L = finiteMatrix L N + 2*cCorrection(L)*I
  full real dictionary zero side = literatureRHS(dictionaryTest)
  [indexMatrix, zeroSideMatrix] = g 1^T - 1 g^T
  rank([indexMatrix, zeroSideMatrix]) <= 2
  rawKernelZeroSideMatrix = 2*zeroSideMatrix
  rawKernelZeroSideMatrix = 2*finiteMatrix + 4*cCorrection(L)*I
  cutoffFreeMatrix = finiteMatrix + 2*cCorrection(L)*I
  zeroSideMatrix = cutoffFreeMatrix
  cutoffFreeMatrixOfCutoff(lambda^2) = cutoffFreeMatrixOfLambda(lambda), lambda>0
  for every finite N and positive L where required
```

Route M M0–M8 remains complete. PR #62 cashes M8 out through H2+ into the exact finite CCM bridge. PR #63 then recovers the full real dictionary EF by finite contraction and transfers the formal CCM displacement onto the actual zero-side matrix. PR #64 reconciles the historical doubled raw-kernel convention. PR #65 removes the remaining finite cutoff-free source-convention ambiguity by proving an exact independently defined matrix map. The remaining hard work is no longer finite bridge construction or normalization; it is object correspondence beyond this finite source formula and the finite-to-infinite topology.

## Downstream finite-to-infinite program

With the literal-tent defect killed and the full finite bridge theorem now substantive-green, the next research work can consume the actual zero-side matrix directly. The hard finite-to-infinite routes remain open.

### Bombieri branch

D0-B now records that Bombieri's published finite matrices are zero-indexed height truncations `H(Gamma_N;t)`, not the deterministic centered CCM Fourier band. His exact finite inertia theorem therefore does not transfer directly to the canonical CCM matrix. The potentially useful future connection is operator-level duality between zero-coordinate truncation and test-function Galerkin restriction; revisit it only after G0/G1 supplies a named ambient form and restriction map.

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

## Immediate next step — D0 representation audit

PR #64 closes the historical raw-kernel normalization question and PR #65 closes D0-C at the finite source-formula level:

```text
zeroSideMatrix
  = cutoffFreeMatrix
  = finiteMatrix + 2*cCorrection(L)*I.
```

The project must not jump directly from this equality to a Hilbert-space Galerkin or finite-to-infinite claim.  The next moves are object-map audits:

1. **D0-R — R002 map-or-separate: SETTLED BY PR #66.** The hard-window truncated-character geometry underlying `qBasis` is a real specialization-level connection, but no generic production theorem identifies the smooth-taper R002 `Gz/G-tilde(T)` family with the canonical CCM finite object. The exact R002 decomposition `Gz = Az + Ez`, the current `lambda <= 1` validity envelope, carrier shift, dynamic dimension, and taper dependence remain distinct. Therefore R002 masking stays on the R002 side and is no longer a CCM critical-path bottleneck.
2. **D0-B — Bombieri correspondence: SETTLED AS DISTINCT TRUNCATIONS.** The 2000 memoir truncates the zero-index multiset `Gamma_N={gamma: |gamma|<=N}` and studies `H(Gamma_N;t)`, whose dimension is `#Gamma_N`. The CCM object instead truncates a deterministic centered Fourier-character dictionary `-N,...,N`, of dimension `2*N+1`. No direct equality, congruence, compression, or parameter map is established, and Bombieri's inertia theorem is therefore not transferred to CCM. See `D0_B_BOMBIERI_CORRESPONDENCE_2026_08_30.md` and `../../external/bombieri/SOURCE_MAP.md`.
3. **G0-A — localized Fourier basis map: REACHED IN PR #68.** The normalized hard-window character correlation is compiler-proved to equal the existing `qBasis` formula on the centered Fourier indices, and the production factor-two firewall `2*dictionaryBasisTest = kernel` is theorem-locked. See `G0_LOCALIZED_BASIS_MAP_2026_08_30.md`.
4. **G0-B — actual finite localized space: REACHED IN PR #69.** The full complex centered `Fin (2*N+1)` sector is realized as actual zero-extended compactly supported L2 functions. Their inherited symmetrized `EF.weilTest` autocorrelation is globally exactly `2*dictionaryTest`, with no reality/evenness/zero-sum/positivity/RH restriction, and the zero-shift endpoint is exactly `2*coefficientMass`. See `G0_B_LOCALIZED_FINITE_SPACE_SETTLEMENT_2026_08_31.md`.
5. **G1-A — additive source-functional restriction firewall: REACHED IN PR #70.** The repository additive half-correlation RHS is compiler-proved, on every actual full-complex localized finite vector, to equal `quadraticForm (cutoffFreeMatrix L N) u`. The factor-half comes directly from #69's global `correlation = 2*dictionaryTest`; the proof then consumes the existing arbitrary-complex deterministic RHS theorem and `dictionaryMatrix = cutoffFreeMatrix`. A lambda wrapper theorem locks `L = 2*log(lambda)`. This is not yet promoted as the external CCM `QW_lambda` restriction.
6. **G1-B0 — Section-4 source-normalization firewall: REACHED IN PR #71.** After the post-green source reread, the direct equation-(4.4) diagonal was corrected: substituting the source formula `q(U_n,U_n)(y)=2(1-y/L)cos(2*pi*n*y/L)` gives the `(cos-exp(-x/2))*rho + w(L)` primitive, and Lean now proves the resulting source equation-(4.4) matrix is exactly the independently audited `cutoffFreeMatrix`. Separately, the printed equation-(4.11) rewrite is theorem-locked as suspect: its algebraically forced correction is `exp(x/2) * cCorrectionIntegrand`. The open proposition `SourceEq411CorrectionIdentity` now refers only to that printed rewrite; it is not used to justify the production matrix.
7. **G1-B1A — finite kappa coordinate/source-sector bridge: IN PR #72.** Formalize `L=2*log(lambda)`, the source logarithmic coordinate and its explicit inverse, and theorem-lock the source equation-(3.21) convention `V_n=kappa(U_n)`. Distinguish formula-level source modes from the actual zero-extended `E_N` test vectors on `[lambda^-1,lambda]`, preserve arbitrary complex centered coefficients, and prove the localized kappa image is exactly that finite source vector. The multiplicative-Haar L2 isometry from Proposition 3.2(i) is not silently inferred.
8. **G1-B1B — kappa/PsiSharp/QW source correspondence: NEXT AFTER #72.** Port the remaining source-facing analytic interface, beginning with any still-needed `d*u`/L2-isometry infrastructure from Proposition 3.2(i), then theorem-lock Proposition 3.2(ii): `QW(kappa f,kappa g)=PsiSharp(F)`, `F(u)=q(f,g)(log u)`, specialized first to the existing finite Fourier sector. Only this step earns the phrase "actual localized Weil-form restriction".
9. **G2/G3 source-port / finite-to-infinite layer: OPEN.** After the actual `QW_lambda` finite restriction is theorem-locked through G1-B1B, port the exact form-core/Rayleigh-bottom theorem needed by the fixed-aperture route rather than re-proving a larger spectral theory from scratch.
10. Revisit prolate/Jacobi structure only after the source restriction topology is theorem-locked. The old small-commutator-to-eigenvector route remains falsified by spectral-gap collapse.

The full centered `2N+1` cutoff-free matrix is theorem-authoritative after PR #65. PR #66 also prevents the generic smooth-taper R002 windowed object from being silently substituted for it. The reversal-even `N+1` compression is still a separate map and must not be silently identified with the full object.

Rank-two displacement remains generic divided-difference structure, not RH evidence. No finite matrix equality implies positivity, form-core density, finite-to-infinite persistence, or RH.

RH remains **OPEN**.


## Source-normalization repair after PR #71

Primary-source equation (4.4) and the independent dictionary/zero-side routes now
agree on the same finite matrix:

```text
canonicalSourceMatrix
  = sourceEq44Matrix
  = cutoffFreeMatrix
  = dictionaryMatrix
  = zeroSideMatrix   (under the existing zeta seam hypotheses).
```

The old `cCorrection`, `gammaL`, `entry`, and `finiteMatrix` definitions
are frozen as the literal printed-(4.11)/(4.14) normalization.  They are not
redefined in place.  Lean theorem-locks

```text
canonicalSourceMatrix
  = legacyPrintedMatrix + 2*legacyPrintedCorrection(L)*I.
```

The corrected integrated equation-(4.11) rewrite uses
`sourceEq411DerivedCorrection`, obtained from the correction integrand
`(1-exp(-x/2))*rho(x)`.  The printed correction remains a historical source
transcription and must not be used to identify an ambient `QW_lambda`
restriction.

This is a semantic/source repair, not a withdrawal of the zero-side/dictionary
theorem chain.  RH remains OPEN.
