# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. RH OPEN.**

## Current authority

### Merged main

~~~text
main = 1ad066f0a263725ea7b84447a637fcebda78e9ca
tree = 41f9febd6a02282e746714c2f62407fb51ac8b30
merged through = PR #87
RH = OPEN
~~~

### Exact green F0-B1B theorem candidate

~~~text
PR #88 head = 5e943d8cd6825c3c649198c52d90d1ed5d8d8b47
synthetic merge = 9eb9281394684600b35a58ce2cb3c757d06379cc
synthetic merge tree = d10e7b1e575624ab39fb445297f43168b1867ed1
RHRC #609 = SUCCESS
Permansson #382 = SUCCESS
status at documentation time = OPEN / NOT MERGED
RH = OPEN
~~~

Live GitHub/Lean/CI overrides this README if later state diverges.

## Closed internal theorem ladder

~~~text
off-line zero
  -> W0 one compact C² pole-neutral negative W test          [PROVED]
  -> W1 strict support collar, L=4r                          [PROVED]
  -> W2-ZS / direct diagonal bridge                          [PROVED]
       W(h,h)=localizedWeilAdditiveRHS(h,h)
  -> strict negative localized-additive witness              [PROVED]
  -> G1-A finite additive restriction                        [PROVED]
  -> F0-B1A boundary-flat legal finite carrier               [PROVED]
  -> F0-B1B exact boundary-flat projection                   [PROVED ON GREEN #88 HEAD]
~~~

F0-B1B gives arbitrary finite coefficients with N>=1 an exact -1,0,+1 correction, exact moment cancellation, fixed-point/idempotence and endpoint jet/moment identities.

Registered production claims on the #88 branch:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
R003_BOUNDARY_FLAT_PROJECTION
~~~

## F0-B1B exact theorem state

For m0,m1,m2 the centered moments of u:

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

Lean proves

~~~text
M0(c)=-m0
M1(c)=-m1
M2(c)=-m2
~~~

and

~~~text
BoundaryFlatCoefficients N (boundaryFlatProject N hN u).
~~~

It also proves:

~~~text
boundaryFlatProject_eq_self_of_boundaryFlat
boundaryFlatProject_idempotent
~~~

plus exact endpoint value/first-jet/second-jet formulas in terms of M0/M1/M2.

N=0 remains explicitly degenerate.

### Projection caveat

The correction c=P(u)-u is not generally boundary-flat. Therefore the zero-extended correction is not automatically an independent global-C² test.

The full projected finite vector is the legal object. No quantitative correction norm estimate is yet proved.

## Current internal frontier — WCONT-A

~~~text
WCONT-A quantitative genuine-W bound                    [NOW / OPEN]
  -> quadratic continuity                              [OPEN]
  -> matched finite approximation                      [OPEN]
  -> moment/endpoint residual control                  [OPEN]
  -> projection-smallness                              [OPEN]
  -> strict finite sign transfer                       [OPEN]
  -> F1 canonical finite negative obstruction          [OPEN]
~~~

F0-B2 direct localized-additive continuity and boundary-killer multiplication remain fallbacks.

### WCONT-A lead

W2-A already permits:

~~~text
first argument: C² + compact support
second argument: continuous + compact support.
~~~

Together with

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
~~~

this suggests one inverse-square-decaying Fourier leg may be enough.

Candidate theorem:

~~~text
|W(f,g)|
  <= K_Λ * (||f||_1 + ||f''||_1) * ||g||_1.
~~~

This is **LEAD / OPEN**, not a current theorem.

If proved, use cross terms to obtain diagonal continuity. Do not rely on per-approximant summability as a substitute for a uniform bound.

## Approximation target after WCONT-A

~~~text
strict-collar compact C² h
  -> raw finite Fourier q_N
  -> q_N -> h in WCONT-A topology
  -> endpoint jets of q_N -> 0
  -> M0,M1,M2 -> 0 by exact #88 formulas
  -> p_N = boundaryFlatProject(q_N)
  -> correction -> 0
  -> p_N -> h
  -> W(p_N,p_N) -> W(h,h)
  -> one finite negative p_N
  -> F0-B1A
  -> F1
~~~

Pinned Mathlib does not currently provide a ready load-bearing Fejer theorem.

## Source-faithful route remains parallel

OBS-015 is permanent:

~~~text
source interface is not source negativity.
~~~

~~~text
S-GEOM
  -> G1-B1A finite source sector                  [PROVED]
  -> S-IFACE/G1-B1B                              [OPEN]
  -> G1-final QW_lambda|E_N=canonicalSourceMatrix[OPEN]

separately:
S-NEG or exact sign-carrying W/localized/QW bridge[OPEN]

then:
G23 negative ambient QW -> finite negative sector [OPEN]
  -> F1                                           [OPEN]
~~~

## Canonical normalization firewall

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

PR #88 does not change this object map.

## Structural clue retained for post-F1

~~~text
1^T u = 0
1^T D u = 0
1^T D²u = 0

D M - M D = g 1^T - 1 g^T.
~~~

Possible simplification along u,Du,D²u is **LEAD / HYPOTHESIS** only. Preserve the constraints in a future F1 theorem.

## Historical settlements

- W1_POST_GREEN_ZERO_SIDE_EVENIZATION_2026_09_01.md
- W2_ZS_POST_GREEN_F0B_FRONTIER_2026_09_01.md
- F0_B1A_POST_GREEN_PROJECTION_CONTINUITY_FRONTIER_2026_09_01.md
- F0_B1B_POST_GREEN_WCONT_FRONTIER_2026_09_01.md

Historical settlement files remain frozen records; this README is the living R003 route SSOT below live GitHub/Lean/CI and machine registries.

RH remains OPEN.
