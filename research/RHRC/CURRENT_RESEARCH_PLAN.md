# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> Live GitHub/compiler/CI defines formal validity. Machine registries define permanent claim state on merged main. Historical settlements remain frozen snapshots.

## Current authority snapshot

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
date = 2026-09-02
RH = OPEN
~~~

### Exact #91 theorem state

~~~text
PR #91 final head = cf1c9b6536264deb8773fa8b0bb3650b07fcff40
merge = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
RHRC #660 = SUCCESS
Permansson #433 = SUCCESS
~~~

The headline theorem and its load-bearing helpers print only

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

## One-screen theorem frontier

~~~text
DONE
  W2-A genuine W -> literatureRHS + summability
  W0 off-line zero -> compact C² pole-neutral negative W test
  W1 strict support collar
  W2-ZS concrete-zeta zero-side evenization
  direct diagonal W2-C
  strict negative localized-additive witness
  G1-A finite additive restriction
  F0-B1A legal boundary-flat finite carrier
  F0-B1B exact three-mode projection
  WCONT-A quantitative genuine-W continuity
  F0-B1C-A raw uniform localized C² approximation

NOW
  F0-B1C-B quantitative projection stability / legal approximation

THEN
  strict finite sign transfer
  F1 canonical finite negative obstruction

FALLBACK INTERNAL
  boundary-killer multiplication
  F0-B2 direct localized-additive continuity
  direct Fejer only if the primary projection route breaks
  old analytic W2-B as cross-check

PARALLEL SOURCE
  S-GEOM / G1-B1A [proved]
  S-IFACE / G1-B1B
  G1-final
  S-NEG
  G23

POST-F1
  full Post-Green Research Pass
  then reassess K0-K3

RH OPEN
~~~

## 1. What #88, #89 and #91 jointly settle

### #88 — exact legalizer

For N>=1, boundaryFlatProject changes only modes -1,0,+1 and kills M0,M1,M2 exactly.

Endpoint identities theorem-lock

~~~text
q(0)   <-> M0
q'(0)  <-> M1
q''(0) <-> M2
~~~

up to explicit nonzero L-dependent scalars.

### #89 — exact W topology

On one fixed support envelope, WCONT-A controls the genuine diagonal Weil error by

~~~text
integral ||p-h||
integral ||(p-h)''||
~~~

plus bounded L1 factors of p and h.

No family dominated-convergence theorem is needed.

### #91 — exact raw approximation

For every strict-collar C² h and every epsilon>0 there are N>=1,u such that the formula-level q satisfies

~~~text
q(0)=0 exactly
sup_[0,L] ||q-h|| < epsilon
sup_[0,L] ||q'-h'|| < epsilon
sup_[0,L] ||q''-h''|| < epsilon.
~~~

This used the pinned root theorem span_fourier_closure_eq_top, explicit finite Finsupp extraction, zero-mode removal, twice integration and exact centered-coordinate reconstruction.

The raw Fourier approximation uncertainty is closed.

## 2. F0-B1C-B — current load-bearing theorem

**Status: OPEN / NOW.**

Target:

~~~text
h : C²
tsupport h subset strict interior of (0,L)
epsilon > 0

exists N>=1 and u,
  BoundaryFlatCoefficients N u
  and, with p = localizedFiniteVector L N u,

  integral ||p-h|| < epsilon
  integral ||p''-h''|| < epsilon.
~~~

The theorem must preserve one fixed aperture L.

The complete projected vector is the legal object.

## 3. Post-#91 quantitative compression

The next proof can exploit more structure than the pre-#91 plan assumed.

### Step A — exact M0 elimination

**DERIVED.**

#91 gives q(0)=0.

#88 gives

q(0)=(1/sqrt L) M0.

For L>0, sqrt L is nonzero, so

M0=0.

No approximate M0 estimate is needed.

### Step B — exact moment/jet conversion

Let b_L=i*2*pi/L.

#88 gives

~~~text
q'(0)  = b_L / sqrt(L) * M1
q''(0) = b_L^2 / sqrt(L) * M2.
~~~

Therefore

~~~text
|M1| = L^(3/2)/(2*pi)   * |q'(0)|
|M2| = L^(5/2)/(4*pi^2) * |q''(0)|.
~~~

### Step C — specialized correction

With M0=0,

~~~text
a_- = (M1-M2)/2
a_0 = M2
a_+ = -(M1+M2)/2.
~~~

Hence

~~~text
|a_-|+|a_0|+|a_+|
  <= |M1| + 2|M2|.
~~~

The coefficient sum is zero, so the correction does not disturb the anchored endpoint value.

### Step D — function correction bound

Each normalized mode has modulus 1/sqrt L. Therefore the intended theorem is

~~~text
integral_0^L |c(x)| dx
  <= L^2/(2*pi) |q'(0)|
   + L^3/(2*pi^2) |q''(0)|.
~~~

### Step E — second-jet correction bound

The zero mode has zero second jet. The +/-1 modes have frequency magnitude 2*pi/L.

Target:

~~~text
integral_0^L |c''(x)| dx
  <= 2*pi |q'(0)| + L |q''(0)|.
~~~

All constants depend only on fixed L, never N.

### Step F — projected approximation

For #91 epsilon-approximants and strict-collar h,

~~~text
|q'(0)| < epsilon
|q''(0)| < epsilon.
~~~

Therefore the expected combined bounds are

~~~text
integral_0^L |p-h|
  <= (L + L^2/(2*pi) + L^3/(2*pi^2)) epsilon

integral_0^L |p''-h''|
  <= (2L + 2*pi) epsilon.
~~~

These are **DERIVED / not yet formalized**.

## 4. The one remaining legal-function seam

Do not confuse formula-level second jets with the global derivative of a hard-window vector.

F0-B1C-B must explicitly use boundary-flatness to identify the complete projected hard-window vector as global C² and connect its global second derivative integral to the interior formula-level second jet.

This is the only analysis/legalization seam left inside F0-B1C.

OBS-016 makes this permanent.

## 5. Strict sign transfer

After F0-B1C-B, use W1:

~~~text
Re W(h,h) < 0
~~~

and WCONT-A:

~~~text
||W(p,p)-W(h,h)|| <= explicit error.
~~~

Choose the approximation tolerance so the error is smaller than the negative margin.

Then obtain one legal finite p with

~~~text
Re W(p,p) < 0.
~~~

No additional Fourier-density theorem should be introduced here.

## 6. F1

F0-B1A then converts the legal finite W value into

~~~text
Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

Preferred strengthened endpoint:

~~~text
off-line zero
  -> exists L>0, N>=1, u,
       BoundaryFlatCoefficients N u
       and
       Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

Retain the moment constraints for the post-F1 displacement/Krylov pass.

## 7. Source-faithful route

Unchanged.

OBS-015 remains binding:

~~~text
source interface is not source negativity.
~~~

Nothing in #91 proves ambient QW_lambda, G1-final, S-NEG or G23.

## 8. Fallback classification after #91

### Generic Stone-Weierstrass infrastructure

SUPERSEDED for F0-B1C-A.

### Direct Fejer

DORMANT FALLBACK.

### Boundary killer

READY FALLBACK, but now clearly more expensive than #88 projection.

### L2 Fourier only

INSUFFICIENT for the load-bearing endpoint second-jet coordinate.

### F0-B2

Fallback only.

## 9. Post-F1 clue

A primary-route F1 witness retains

~~~text
1^T u = 0
1^T D u = 0
1^T D^2 u = 0.
~~~

The canonical matrix satisfies

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

Potential Krylov/displacement simplification remains LEAD / HYPOTHESIS until F1 exists.

## 10. Highest-leverage next implementation

Do one focused F0-B1C-B PR.

Do not add generic Fourier infrastructure.

Do not add W machinery.

Do not touch the source route.

The PR should prove the specialized projection estimates and the final legal approximation existential theorem.

Then immediately run a Post-Green pass and decide whether sign transfer should be a separate PR or can be combined cleanly with F1.

## Current records

Latest delta:

research/RHRC/RESEARCH_LEADS_POST_91_DELTA.md

Latest settlement:

research/RHRC/routes/R003_ccm_bridge/F0_B1C_A_POST_GREEN_PROJECTION_STABILITY_FRONTIER_2026_09_02.md

**RH remains OPEN.**
