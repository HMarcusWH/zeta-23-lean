# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. RH OPEN.**

## Current authority

### Merged main

~~~text
main = 879eb6d356d8f62bbe0b9241596b15892498ea64
tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
merged through = PR #88
RH = OPEN
~~~

### Exact green WCONT-A theorem candidate

~~~text
PR #89 head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
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
  -> F0-B1B exact boundary-flat projection                   [PROVED / MERGED]
  -> WCONT-A quantitative genuine-W continuity package       [PROVED ON GREEN #89 HEAD]
~~~

WCONT-A gives:

~~~text
fixed support envelope
  -> global weighted paperFT estimate
  -> fixed inverse-square zeta-zero majorant
  -> quantitative W(f,g) bound
  -> exact summability-safe diagonal cross-term identity
  -> quantitative W(p,p)-W(h,h) bound.
~~~

Registered branch claim:

~~~text
R003_WEIL_COMMON_SUPPORT_BOUND
~~~

## Current internal frontier — F0-B1C

~~~text
F0-B1C WCONT-matched legal finite approximation       [NOW / OPEN]
  -> quantitative three-mode correction bounds       [OPEN]
  -> projection-smallness                             [OPEN]
  -> strict finite sign transfer                      [OPEN]
  -> F1 canonical finite negative obstruction         [OPEN]
~~~

### Exact approximation target

For the strict-collar W1 witness h, one fixed L should support boundary-flat finite p with

~~~text
integral ||p-h|| -> 0
integral ||p''-h''|| -> 0.
~~~

Endpoint value/first-jet/second-jet control is auxiliary data for the #88 projector, not an extra WCONT norm component.

## Preferred construction lead

Pinned Mathlib contains

~~~text
ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints.
~~~

High-priority route to test:

~~~text
periodic h''
  -> uniform finite trigonometric approximation r
  -> remove constant mode / enforce mean zero
  -> integrate twice in finite Fourier coefficients
  -> fix q constant mode by mean(h)
  -> recover q', q by periodic integration estimates
  -> endpoint jets small
  -> boundaryFlatProject
  -> WCONT-A
  -> negative finite vector.
~~~

This is **LEAD / HYPOTHESIS** only.

Direct Fejer remains the first fallback if the star-subalgebra or integration-back formalization is larger.

## Projection caveat

The correction c=P(u)-u is generally not boundary-flat. Its hard-window extension is not automatically global C².

Use the correction only inside quantitative coefficient/interior estimates. The complete projected vector is the legal W test.

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

## Structural clue retained for post-F1

A primary-route F1 witness should retain

~~~text
1^T u = 0
1^T D u = 0
1^T D²u = 0,
~~~

while the canonical matrix satisfies

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

Possible Krylov/displacement simplification remains **LEAD / HYPOTHESIS**.

## Historical settlements

- W1_POST_GREEN_ZERO_SIDE_EVENIZATION_2026_09_01.md
- W2_ZS_POST_GREEN_F0B_FRONTIER_2026_09_01.md
- F0_B1A_POST_GREEN_PROJECTION_CONTINUITY_FRONTIER_2026_09_01.md
- F0_B1B_POST_GREEN_WCONT_FRONTIER_2026_09_01.md
- WCONT_A_POST_GREEN_F0B1C_FRONTIER_2026_09_01.md

Historical settlement files remain frozen records.

RH remains OPEN.
