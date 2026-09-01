# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. Lean/compiler/CI plus the machine registries define formal truth. This file defines what the project should build next.

## Current merged validation baseline

~~~text
main = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
merged through = PR #86
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
PR #86 synthetic merge = a687d8142513b163b9755a18ddf9612901484cac
PR #86 merge = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
RHRC #605 = SUCCESS
Permansson #378 = SUCCESS
date = 2026-09-01
RH = OPEN
~~~

PR #86 theorem-locks F0-B1A: centered moments `0,1,2 = 0` define a nontrivial finite coefficient sector whose hard-window localized vectors are global C² tests, and on that carrier the genuine concrete-zeta diagonal Weil form is exactly the `canonicalSourceMatrix` quadratic form.

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
  explicit nonzero five-mode boundary-flat witness

NOW
  F0-B1B exact three-mode boundary-flat projection
  WCONT determine/prove the weakest common-support topology preserving W

THEN
  finite Fourier approximation in exactly that topology
  exact projection into the boundary-flat carrier
  strict-negative finite transfer
  F1 canonical finite negative obstruction

FALLBACK INTERNAL
  F0-B2 direct localized-additive continuity on the existing finite vectors
  old analytic I0/I1/I2 -> W2-B route as an independent cross-check

PARALLEL SOURCE
  S-GEOM exact L <-> lambda bridge
  S-IFACE / G1-B1B Haar-L²-kappa-q-PsiSharp-QW interface
  G1-final actual QW_lambda finite restriction
  S-NEG independent negative-QW theorem or exact sign-carrying composition
  G23 negative ambient QW -> finite negative source sector

POST-F1
  K0 parity
  K1 aperture flow / first singularity / prime events
  K2 kernel-displacement-resolvent rigidity
  K3 arithmetic crossing exclusion

RH OPEN
~~~

## 1. What PR #86 changed

Before #86, F0-B1 and F0-B2 were retained as co-primary bounded candidates because global C² legality of hard-window finite Fourier vectors was unresolved. That uncertainty is gone.

For every `L>0`, finite `N`, and `u : Fin (2*N+1) -> C` satisfying

~~~text
centeredMoment N 0 u = 0
centeredMoment N 1 u = 0
centeredMoment N 2 u = 0,
~~~

Lean proves

~~~text
ContDiff R 2 (localizedFiniteVector L N u)
~~~

and then composes PR #83 with G1-A to prove

~~~text
zetaZeroConfig.W(v,v)
  = quadraticForm(canonicalSourceMatrix L N) u.
~~~

Production claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

The legal carrier is nontrivial: the five-mode coefficients `[1/4,-1,3/2,-1,1/4]` satisfy all three moments and are nonzero.

Therefore F0-B1 is the primary internal route. F0-B2 remains a ready fallback, not a co-primary route.

## 2. F0-B1B — exact boundary-flat projection

**Status: NOW / OPEN.**

For `N>=1` and arbitrary coefficients `u`, write

~~~text
m0 = centeredMoment N 0 u
m1 = centeredMoment N 1 u
m2 = centeredMoment N 2 u.
~~~

The next bounded theorem should define a correction supported on centered modes `-1,0,+1`:

~~~text
c_-1 = (m1 - m2)/2
c_0  = m2 - m0
c_+1 = -(m1 + m2)/2.
~~~

Target algebra:

~~~text
M0(c) = -m0
M1(c) = -m1
M2(c) = -m2
~~~

so `boundaryFlatProject u = u + c` is boundary-flat.

Required production surface should include, subject to compiler-driven naming:

~~~text
boundaryFlatCorrection
boundaryFlatProject
boundaryFlatProject_boundaryFlat
boundaryFlatProject_eq_self_of_boundaryFlat
boundaryFlatProject_idempotent
~~~

Useful quantitative estimates should be added only if cheap:

~~~text
|c_-1| <= (|m1|+|m2|)/2
|c_0|  <= |m0|+|m2|
|c_1|  <= (|m1|+|m2|)/2
sum |c_j| <= |m0|+|m1|+2|m2|.
~~~

**N=0 firewall:** do not hide the degenerate one-mode sector. The production projection theorem should require `1 <= N` or an equivalent availability condition.

## 3. WCONT — topology before density

**Status: ACTIVE / LOAD-BEARING.**

Do not first formalize a large generic Fourier-density library. Determine the weakest topology actually required to preserve the strict negative W margin.

The repository already owns:

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
~~~

which supply the inverse-square summable zero weight and the compact-C² Fourier-decay mechanism. The first WCONT spike should test whether the following ingredients yield one family-level majorant:

~~~text
common compact support envelope
+ one uniform support radius
+ convergence/control of the function and second derivative
+ one uniform second-derivative integral bound.
~~~

Permanent firewall:

~~~text
Summable(Wsummand(p_N,p_N)) for every N
  does NOT imply
a uniform summable majorant in N.
~~~

A WCONT theorem must supply a family-level constant or another quantitative continuity argument.

Pinned Mathlib does not provide a ready-made Fejer theorem. Do not write “standard Fourier approximation” into a load-bearing proof without theoremizing the actual approximation mechanism.

## 4. Approximation after WCONT

Once WCONT fixes the required topology, choose the smallest approximation theorem matching it.

Candidate order:

1. raw finite Fourier approximation + exact three-mode projection;
2. strengthen witness regularity only if the topology actually requires it;
3. fixed boundary-killer multiplication as fallback;
4. formalize a Fejer/Cesaro layer only if cheaper routes fail.

The W1 collar is a major asset:

~~~text
tsupport h subset (L/4, 3L/4).
~~~

Hence the target vanishes on neighborhoods of both periodic endpoints. The approximation theorem should exploit this rather than solve a harder generic periodic-boundary problem.

## 5. F1 cash-out

Once boundary-flat finite `p_N` satisfy

~~~text
W(p_N,p_N) -> W(h,h)
Re W(h,h) < 0,
~~~

strictness yields one finite `N` with negative W. PR #86 immediately converts this into

~~~text
Re (quadraticForm (canonicalSourceMatrix L N) u_N) < 0.
~~~

A useful strengthened F1 endpoint would retain

~~~text
BoundaryFlatCoefficients N u_N.
~~~

If sign transfer and the finite obstruction composition are mathematically tiny once WCONT/approximation are green, they should close in the same theorem pass rather than creating an artificial implementation boundary.

## 6. Source-faithful parallel route

OBS-015 remains permanent:

~~~text
source interface is not source negativity.
~~~

The source lane is therefore:

~~~text
S-GEOM -> G1-B1A [PROVED] -> S-IFACE/G1-B1B -> G1-final

separately:
S-NEG or exact W/localized/QW sign composition

then:
G23 -> F1.
~~~

No theorem in PR #86 proves ambient `QW_lambda`, `PsiSharp`, a source sign theorem, or G23.

## 7. Post-F1 rule

Do not begin K0-K3 automatically when implementation reaches F1. A green F1 is the next major dependency-graph event and must trigger a full Post-Green Research Pass. The external roadmap version `v2.0` remains reserved for that event or an equivalently large theorem-state change.

Detailed #86 settlement:
`routes/R003_ccm_bridge/F0_B1A_POST_GREEN_PROJECTION_CONTINUITY_FRONTIER_2026_09_01.md`.

RH remains OPEN.
