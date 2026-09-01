# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. RH OPEN.**

## Current merged authority

~~~text
main = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
merged through = PR #86
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
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
       moments 0,1,2 = 0
       -> hard-window vector global C²
       -> W(v,v)=quadraticForm(canonicalSourceMatrix)u
~~~

Registered #86 production claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

PR #86 also proves the legal sector is nontrivial through the explicit five-mode coefficients `[1/4,-1,3/2,-1,1/4]`.

## Current internal frontier

The primary internal route is now:

~~~text
F0-B1B exact three-mode boundary-flat projection       [NOW / OPEN]
  -> WCONT family-level quantitative continuity        [OPEN]
  -> finite approximation in the chosen topology      [OPEN]
  -> strict finite sign transfer                       [OPEN]
  -> F1 canonical finite negative obstruction          [OPEN]
~~~

F0-B2 direct localized-additive continuity remains a fallback. Its main previous advantage — avoiding the hard global-C² finite carrier problem — was removed by PR #86.

### F0-B1B target

For `N>=1` and moments `m0,m1,m2`, correct only centered modes `-1,0,+1`:

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

The next theorem should prove the correction cancels moments 0,1,2 exactly, define an idempotent/fixed-point projection onto `BoundaryFlatCoefficients`, and expose quantitative correction bounds if they are cheap.

`N=0` is a real degenerate case and must stay explicit.

### WCONT firewall

Per-family-member summability is insufficient. A successful WCONT theorem needs one uniform family majorant or another quantitative continuity argument.

Existing leverage:

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
~~~

These supply the inverse-square zero weight and compact-C² Fourier decay. Test whether common support plus a family-uniform second-derivative bound closes the zero-side dominated-convergence gate.

Do not formalize a generic Fejer/Cesaro library before the required W topology is known.

## Source-faithful route remains parallel

OBS-015 is permanent:

~~~text
source interface is not source negativity.
~~~

Source route:

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

No internal #86 theorem identifies ambient `QW_lambda` or proves source negativity.

## Canonical normalization firewall

The direct source finite matrix authority remains

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
~~~

Historical printed normalization remains

~~~text
legacyPrintedMatrix = finiteMatrix
~~~

with the theorem-locked scalar identity shift. No new #86 theorem changes this object map.

## Structural clue retained for post-F1

Boundary-flat moments translate to the coefficient annihilations

~~~text
1^T u = 0
1^T D u = 0
1^T D²u = 0
~~~

while the canonical matrix obeys

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

Possible simplification along the Krylov chain `u,Du,D²u` is **LEAD / HYPOTHESIS** only. Preserve the constraints in a future F1 theorem so this can be tested after F1 becomes real.

## Historical settlements

- `W1_POST_GREEN_ZERO_SIDE_EVENIZATION_2026_09_01.md`
- `W2_ZS_POST_GREEN_F0B_FRONTIER_2026_09_01.md`
- `F0_B1A_POST_GREEN_PROJECTION_CONTINUITY_FRONTIER_2026_09_01.md`

Historical settlement files remain frozen records; this README is the living R003 route SSOT below live GitHub/Lean/CI and machine registries.

RH remains OPEN.
