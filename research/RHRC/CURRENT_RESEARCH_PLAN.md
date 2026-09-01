# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. Live GitHub/compiler/CI defines formal validity. Machine registries define claim state on the checked ref. Historical post-green settlements remain frozen snapshots.

## Current authority snapshot

### Merged validation baseline

~~~text
main = 879eb6d356d8f62bbe0b9241596b15892498ea64
tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
merged through = PR #88
date = 2026-09-01
RH = OPEN
~~~

### Exact green WCONT-A theorem state

~~~text
PR #89 head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
base = 879eb6d356d8f62bbe0b9241596b15892498ea64
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
PR status at documentation time = OPEN / NOT MERGED
RH = OPEN
~~~

## One-screen theorem frontier

~~~text
DONE
  W2-A genuine W -> literatureRHS + pairwise summability
  W0 off-line zero -> compact C² pole-neutral negative W test
  W1 strict support collar: tsupport h subset (r,3r), L=4r
  W2-ZS concrete-zeta zero-side evenization
  direct diagonal W2-C:
    W(h,h) = localizedWeilAdditiveRHS(h,h)
  strict-aperture negative localized-additive witness
  G1-A finite additive restriction
  F0-B1A boundary-flat finite carrier:
    moments 0,1,2 = 0
    -> hard-window vector is global C²
    -> W(v,v) = quadraticForm(canonicalSourceMatrix) u
  F0-B1B exact three-mode projection:
    N>=1
    arbitrary u
    -> exact correction on centered modes -1,0,+1
    -> moments 0,1,2 vanish
    -> fixed-point + idempotence
    -> exact endpoint value/jet <-> moment formulas
  WCONT-A:
    fixed support envelope
    -> global weighted paperFT bound
    -> fixed inverse-square zeta-zero majorant
    -> quantitative genuine-W bound
    -> exact cross-term identity
    -> quantitative diagonal perturbation bound

NOW
  F0-B1C minimal WCONT-matched legal finite approximation

THEN
  explicit three-mode correction bounds
  projection-smallness in L1 + second-derivative L1
  strict-negative finite transfer
  F1 canonical finite negative obstruction

FALLBACK INTERNAL
  direct Fejer construction
  F0-B2 direct localized-additive continuity
  boundary-killer multiplication
  old analytic I0/I1/I2 -> W2-B route as independent cross-check

PARALLEL SOURCE
  S-GEOM exact L <-> lambda bridge
  S-IFACE / G1-B1B Haar-L²-kappa-q-PsiSharp-QW interface
  G1-final actual QW_lambda finite restriction
  S-NEG independent negative-QW theorem or exact sign-carrying composition
  G23 negative ambient QW -> finite negative source sector

POST-F1
  full Post-Green Research Pass first
  then reassess K0 parity
  K1 aperture flow / first singularity / prime events
  K2 kernel-displacement-resolvent rigidity
  K3 arithmetic crossing exclusion

RH OPEN
~~~

## 1. What F0-B1A and F0-B1B settled

F0-B1A theorem-locks the legal finite carrier. For positive L and centered coefficients u satisfying

~~~text
M0(u)=M1(u)=M2(u)=0,
~~~

the hard-window vector is global C² and

~~~text
zetaZeroConfig.W(v,v)
  = quadraticForm(canonicalSourceMatrix L N) u.
~~~

F0-B1B theorem-locks an exact projection into that carrier for N>=1:

~~~text
c_-1 = (M1-M2)/2
c_0  = M2-M0
c_+1 = -(M1+M2)/2.
~~~

Lean proves exact moment cancellation, fixed-point/idempotence, and exact endpoint value/first-jet/second-jet identities.

The correction itself is generally not boundary-flat. The complete projected vector is the legal global C² object.

## 2. What WCONT-A settled

**Formal status: PROVED on exact green PR #89 head; pending permanent merge at documentation time.**

Production surface:

~~~text
Zeta23.norm_paperFT_mul_one_add_normSq_le
Zeta23.ExceptionalZero.zeta_invSqZeroWeight_summable
Zeta23.ExceptionalZero.norm_zeta_Wsummand_le_commonSupport
Zeta23.ExceptionalZero.zeta_W_norm_le_commonSupport
Zeta23.ExceptionalZero.zeta_W_self_sub_self_eq_cross
Zeta23.ExceptionalZero.zeta_W_self_sub_self_norm_le_commonSupport
~~~

For one fixed support radius Lambda,

~~~text
||W(f,g)||
  <= exp(Lambda) * zetaInvSqZeroMass
     * (integral ||f|| + integral ||f''||)
     * integral ||g||.
~~~

The diagonal perturbation theorem reduces self-form continuity to

~~~text
integral ||p-h|| -> 0
integral ||(p-h)''|| -> 0,
~~~

with the second-leg L1 factor automatically bounded once the first function error tends to zero.

### Consequence

The primary route no longer needs a family dominated-convergence theorem. The exact approximation topology is fixed.

## 3. F0-B1C — current load-bearing theorem

**Status: ACTIVE / NEXT.**

Target only the minimal theorem needed by #88 + #89.

Preferred existential endpoint:

~~~text
h : compact C²
tsupport h subset strict interior of (0,L)

for every eps > 0
  exists N>=1 and u,
    BoundaryFlatCoefficients N u
    and, with p = localizedFiniteVector L N u,

    integral ||p-h|| < eps
    integral ||p''-h''|| < eps.
~~~

Equivalent sequential packaging is acceptable if easier in Lean.

The theorem should preserve one fixed aperture L. No support constant may depend on N.

## 4. Preferred construction lead — existing AddCircle Fourier span

Pinned Mathlib already contains a route-specific Fourier package in

~~~text
Mathlib/Analysis/Fourier/AddCircle.lean
~~~

with the exact positive-sign characters

~~~text
AddCircle.fourier n (x : AddCircle L)
  = exp(2*pi*i*n*x/L),
~~~

matching `localizedMode L n` up to the repository's fixed `1/sqrt L` normalization.

Load-bearing existing theorems include:

~~~text
AddCircle.span_fourier_closure_eq_top
AddCircle.fourierCoeff_eq_intervalIntegral
AddCircle.fourierCoeffOn_eq_integral
AddCircle.fourierCoeffOn_of_hasDerivAt
AddCircle.hasDerivAt_fourier
Finsupp.mem_span_range_iff_exists_finsupp
~~~

Therefore do **not** rebuild Stone-Weierstrass and do not start with Fejer.

Preferred F0-B1C construction:

1. use the W1 strict collar to regard h as a C² periodic function across the 0/L seam;
2. regard h'' as a continuous map on `AddCircle L`;
3. use `span_fourier_closure_eq_top` to choose a finite trigonometric polynomial r uniformly close to h'';
4. extract the finite span element as explicit coefficients `c : ℤ →₀ ℂ` via `Finsupp.mem_span_range_iff_exists_finsupp`;
5. prove `integral_0^L h'' = h'(L)-h'(0)=0`, then subtract the constant/mean mode, preserving finite support and increasing the uniform error by only a fixed factor;
6. integrate every nonzero Fourier mode of the mean-zero polynomial twice, using the exact frequency `2*pi*i*n/L`;
7. choose the constant mode of q to match the mean of h;
8. prove q'' equals the corrected polynomial exactly;
9. recover q' and q from q''-h'' by fixed-L periodic integration/Poincare estimates;
10. obtain endpoint q'', q', q residuals; the strict collar gives h(0)=h'(0)=h''(0)=0;
11. convert endpoint residuals to M0,M1,M2 with #88 and apply `boundaryFlatProject`;
12. prove the fixed three-mode correction is small in the WCONT-A norm.

### Why this is smaller than the previous Stone-Weierstrass lead

Mathlib has already proved that the finite span of the exact Fourier characters is uniformly dense. We only need the extraction/integration-back bridge into `localizedFiniteFunction`, not a new density theorem or a new separating star-subalgebra proof.

### Why L² Fourier convergence is not sufficient by itself

`AddCircle.hasSum_fourier_series_L2` is useful supporting infrastructure, but #88 needs the second endpoint jet q''(0) to be small. Point evaluation is not continuous in L². Uniform approximation of h'' directly supplies that endpoint control.

### Fast falsifiers

- converting the already-extracted finite `ℤ →₀ ℂ` support into the repository's centered `Fin (2*N+1)` coordinates is unexpectedly expensive;
- mean-zero removal is awkward under the exact continuous-map representation;
- the twice-integrated finite polynomial does not align cleanly with `localizedMode/centeredIndex`;
- fixed-L periodic integration estimates are harder than the boundary-killer fallback.

If these occur, compare direct Fejer and the boundary-killer route before expanding infrastructure.

## 5. Quantitative projection-smallness package

After raw approximation is available, prove only the fixed-L inequalities actually needed.

Coefficient bounds:

~~~text
|c_-1| <= (|M1|+|M2|)/2
|c_0|  <= |M0|+|M2|
|c_1|  <= (|M1|+|M2|)/2.
~~~

Because the correction uses only modes -1,0,+1, its interior function and second derivative have constants depending on L only, never N.

Endpoint/moment identities from #88 turn small raw endpoint jets into small correction coefficients.

Do not treat the correction's hard-window extension as independently C².

## 6. Strict sign transfer and F1

W1 supplies

~~~text
Re W(h,h) < 0.
~~~

WCONT-A supplies an explicit bound on

~~~text
||W(p,p)-W(h,h)||.
~~~

Therefore an approximation error small enough relative to the strict negative margin yields one finite legal p with

~~~text
Re W(p,p) < 0.
~~~

F0-B1A then gives

~~~text
Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

Preferred strengthened F1 endpoint:

~~~text
off-line zero
  -> exists L>0, N>=1, u,
       BoundaryFlatCoefficients N u
       and
       Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

Preserve the moment constraints for the post-F1 displacement/Krylov pass.

## 7. Source-faithful route remains parallel

OBS-015 remains permanent:

~~~text
source interface is not source negativity.
~~~

Nothing in WCONT-A proves ambient QW_lambda, PsiSharp, source negativity, G23, or a source-faithful F1.

## 8. Post-F1 rule

A green F1 is the next major dependency-graph event. Perform a full Post-Green Research Pass before K0-K3.

Revisit

~~~text
1^T u = 1^T D u = 1^T D²u = 0
~~~

against

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

The external roadmap version v2.0 remains reserved for green F1 or a comparably large theorem-state change.

Current post-green settlement:

research/RHRC/routes/R003_ccm_bridge/WCONT_A_POST_GREEN_F0B1C_FRONTIER_2026_09_01.md

Current delta ledger:

research/RHRC/RESEARCH_LEADS_POST_89_DELTA.md

RH remains OPEN.
