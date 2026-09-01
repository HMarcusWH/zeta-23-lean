# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. Live GitHub/compiler/CI defines formal validity. Machine registries define claim state on the checked ref. This file defines what the project should build next.

## Current authority snapshot

### Merged validation baseline

~~~text
main = 1ad066f0a263725ea7b84447a637fcebda78e9ca
tree = 41f9febd6a02282e746714c2f62407fb51ac8b30
merged through = PR #87
date = 2026-09-01
RH = OPEN
~~~

### Exact green F0-B1B theorem state

~~~text
PR #88 theorem head = 5e943d8cd6825c3c649198c52d90d1ed5d8d8b47
base = 1ad066f0a263725ea7b84447a637fcebda78e9ca
synthetic merge = 9eb9281394684600b35a58ce2cb3c757d06379cc
synthetic merge tree = d10e7b1e575624ab39fb445297f43168b1867ed1
RHRC #609 = SUCCESS
Permansson #382 = SUCCESS
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
  explicit nonzero five-mode boundary-flat witness
  F0-B1B exact three-mode projection on green #88 head:
    N>=1
    arbitrary u
    -> exact correction on centered modes -1,0,+1
    -> moments 0,1,2 vanish
    -> fixed-point + idempotence
    -> exact endpoint value/jet <-> moment formulas

NOW
  WCONT-A quantitative common-support genuine-W bound
  target the weakest theorem needed for sign preservation

THEN
  quadratic W continuity corollary
  finite Fourier approximation in exactly that topology
  moment/endpoint residual control
  projection-smallness
  strict-negative finite transfer
  F1 canonical finite negative obstruction

FALLBACK INTERNAL
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

## 1. What F0-B1A already settled

PR #86 removed the hard-window legality uncertainty. For every L>0, finite N and u satisfying

~~~text
centeredMoment N 0 u = 0
centeredMoment N 1 u = 0
centeredMoment N 2 u = 0,
~~~

Lean proves

~~~text
ContDiff R 2 (localizedFiniteVector L N u)
~~~

and

~~~text
zetaZeroConfig.W(v,v)
  = quadraticForm(canonicalSourceMatrix L N) u.
~~~

Production claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

The legal carrier is nontrivial by the explicit five-mode vector [1/4,-1,3/2,-1,1/4].

## 2. What PR #88 changed — F0-B1B

**Formal status: PROVED on exact green theorem head; pending permanent merge at documentation time.**

For N>=1 and arbitrary coefficients u define m0,m1,m2 as centered moments 0,1,2. PR #88 defines:

~~~text
c_-1 = (m1 - m2)/2
c_0  = m2 - m0
c_+1 = -(m1 + m2)/2.
~~~

Lean proves

~~~text
M0(c) = -m0
M1(c) = -m1
M2(c) = -m2
~~~

and hence

~~~text
BoundaryFlatCoefficients N (boundaryFlatProject N hN u).
~~~

Production surface:

~~~text
boundaryFlatProject_boundaryFlat
boundaryFlatProject_eq_self_of_boundaryFlat
boundaryFlatProject_idempotent
~~~

The exact endpoint/moment dictionary is also theorem-locked:

~~~text
localizedFiniteFunction_zero_eq_centeredMoment_zero
localizedFiniteFirstJet_zero_eq_centeredMoment_one
localizedFiniteSecondJet_zero_eq_centeredMoment_two
~~~

Registered branch claim:

~~~text
R003_BOUNDARY_FLAT_PROJECTION
~~~

### What #88 does not prove

- no quantitative correction norm estimates;
- no density theorem;
- no W continuity theorem;
- no strict sign transfer;
- no F1;
- no source QW theorem;
- no finite-negative exclusion;
- no RH.

N=0 remains genuinely degenerate.

## 3. Post-green structural consequences

### PROVED

The correction is exactly supported on three reserved centered modes and the complete projected vector is boundary-flat.

### DERIVED

The legality repair changes only three coefficient coordinates, independent of N. The rank-at-most-three interpretation is not separately theoremized as a LinearMap/rank statement.

### DERIVED

Because the correction modes are fixed at -1,0,+1 for fixed L, quantitative smallness of m0,m1,m2 should imply quantitative smallness of the interior correction and its first two derivatives with constants depending on L but not on N.

The needed inequalities are not yet in Lean.

### Important caveat

The correction c=P(u)-u is generally not boundary-flat:

~~~text
Mk(c) = -Mk(u).
~~~

Its zero-extended hard-window realization is therefore not automatically a globally C² admissible test.

The complete projected vector is the theorem-backed legal object.

## 4. WCONT-A — quantitative bound before density

**Status: ACTIVE / LOAD-BEARING / NEXT THEOREM.**

Existing theorem-backed resources:

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
Zeta23.ExceptionalZero.zeta_W_literatureRHS_package
~~~

W2-A is asymmetric:

~~~text
f: C² + compact support
g: continuous + compact support.
~~~

That suggests the first WCONT theorem should exploit only one inverse-square-decaying Fourier factor.

### Candidate analytic estimate — OPEN / LEAD

For one fixed support envelope of radius Λ, seek a theorem of schematic form

~~~text
|paperFT f (gammaOf ρ)|
  <= C_Λ * (||f||_1 + ||f''||_1)
       / (1 + ||gammaOf ρ||^2)

|paperFT g (conj (gammaOf ρ))|
  <= C_Λ * ||g||_1
~~~

and hence

~~~text
|W(f,g)|
  <= K_Λ
     * (||f||_1 + ||f''||_1)
     * ||g||_1.
~~~

The exact norms, support hypotheses, constants and generic-vs-zeta specialization must be chosen by the proof.

### Why this is preferable

If e=p-h and W is expanded legally,

~~~text
W(p,p)-W(h,h)
  = W(e,p)+W(h,e),
~~~

then one quantitative bilinear estimate can reduce diagonal continuity to small first-leg error plus bounded second-leg L¹ control.

Cross-term linearity/conjugate-linearity and tsum rearrangements must be proved or explicitly justified.

Permanent firewall:

~~~text
Summable(Wsummand(p_N,p_N)) for every N
  does NOT imply
a uniform summable majorant in N.
~~~

## 5. Approximation after WCONT-A

Only after WCONT-A fixes the norm/topology should the finite approximation theorem be chosen.

Preferred sequence:

1. construct raw finite centered Fourier approximants q_N to the strict-collar W1 witness;
2. prove convergence in exactly the WCONT-A first-leg norm;
3. prove endpoint value/first jet/second jet residuals tend to zero;
4. convert endpoint residuals into M0/M1/M2 residuals using #88;
5. define p_N = boundaryFlatProject(q_N);
6. prove the fixed three-mode correction tends to zero in the selected topology;
7. conclude p_N remains an approximation of h and is exactly boundary-flat.

The W1 collar

~~~text
tsupport h subset (L/4,3L/4)
~~~

remains a major asset.

Pinned Mathlib does not provide a ready Fejer theorem that may simply be inserted into the proof.

### Boundary-killer fallback

If projection-smallness becomes disproportionately difficult, retain

~~~text
(1-cos(2πx/L))^2
~~~

as the fallback approximation architecture.

## 6. Strict sign transfer and F1

Once boundary-flat finite p_N satisfy

~~~text
W(p_N,p_N) -> W(h,h)
Re W(h,h) < 0,
~~~

strictness yields one finite N with negative W.

F0-B1A immediately converts this into

~~~text
Re (quadraticForm (canonicalSourceMatrix L N) u_N) < 0.
~~~

Preferred strengthened F1 endpoint:

~~~text
off-line zero
  -> exists L>0, N>=1, u,
       BoundaryFlatCoefficients N u
       and
       Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

## 7. Source-faithful parallel route

OBS-015 remains permanent:

~~~text
source interface is not source negativity.
~~~

The source lane remains:

~~~text
S-GEOM -> G1-B1A [PROVED] -> S-IFACE/G1-B1B -> G1-final

separately:
S-NEG or exact W/localized/QW sign composition

then:
G23 -> F1.
~~~

No theorem in PR #88 proves ambient QW_lambda, PsiSharp, source negativity or G23.

## 8. Post-F1 rule

A green F1 is the next major dependency-graph event and must trigger a full Post-Green Research Pass before K0-K3.

Revisit:

~~~text
1^T u = 1^T D u = 1^T D²u = 0
~~~

against

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

The external roadmap version v2.0 remains reserved for that event or an equivalently large theorem-state change.

Current post-green settlement:

research/RHRC/routes/R003_ccm_bridge/F0_B1B_POST_GREEN_WCONT_FRONTIER_2026_09_01.md

RH remains OPEN.
