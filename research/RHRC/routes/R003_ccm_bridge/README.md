# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. RH OPEN.**

## Current authority

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
RH = OPEN
~~~

Recent exact green/merged packages:

~~~text
#88 F0-B1B
  head fe5fe1c75668e1265482db3119d256997e31f32a
  RHRC #617 / Permansson #390
  merge 879eb6d356d8f62bbe0b9241596b15892498ea64

#89 WCONT-A
  head 8680b379e695278d1688b02f3f01b075620c4b07
  RHRC #636 / Permansson #409
  merge f6e79fcf7b4daac7ed29bd90f24321229a9addd1

#91 F0-B1C-A
  head cf1c9b6536264deb8773fa8b0bb3650b07fcff40
  RHRC #660 / Permansson #433
  merge bab94aed54298de6fc6676808a0b0e46c2db6046
~~~

## Closed internal theorem ladder

~~~text
off-line zero
  -> W0 compact C² pole-neutral negative W test                 PROVED
  -> W1 strict support collar                                   PROVED
  -> W2-ZS / diagonal W bridge                                  PROVED
  -> strict negative localized-additive witness                 PROVED
  -> G1-A finite additive restriction                           PROVED
  -> F0-B1A legal boundary-flat finite carrier                  PROVED
  -> F0-B1B exact three-mode projection                         PROVED
  -> WCONT-A quantitative genuine-W continuity                  PROVED
  -> F0-B1C-A raw uniform localized C² approximation            PROVED
~~~

Current frontier:

~~~text
F0-B1C-B quantitative projection stability             NOW / OPEN
  -> strict finite sign transfer                        OPEN
  -> F1 canonical finite negative obstruction           OPEN
~~~

## F0-B1C-A production surface

Primary theorem:

~~~text
Zeta23.CCM.exists_localizedFinite_uniform_C2_approx
~~~

For a positive fixed aperture and a complex C² strict-collar target, it produces N>=1 and centered finite coefficients with

~~~text
q(0)=0
sup ||q-h|| < epsilon
sup ||q'-h'|| < epsilon
sup ||q''-h''|| < epsilon
~~~

on [0,L].

Production axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

The exact pinned Mathlib Fourier density declaration is span_fourier_closure_eq_top at root. Earlier AddCircle-qualified wording was an API-description error and is superseded.

## F0-B1C-B specialization

**DERIVED / not yet theorem-locked.**

#91 + #88 gives

~~~text
M0 = 0
~~~

exactly.

Thus the correction is

~~~text
a_- = (M1-M2)/2
a_0 = M2
a_+ = -(M1+M2)/2.
~~~

Endpoint identities yield

~~~text
|M1| = L^(3/2)/(2*pi)   |q'(0)|
|M2| = L^(5/2)/(4*pi^2) |q''(0)|.
~~~

The intended fixed-L estimates are

~~~text
integral_0^L |correction|
  <= L^2/(2*pi) |q'(0)|
   + L^3/(2*pi^2) |q''(0)|

integral_0^L |correction''|
  <= 2*pi |q'(0)| + L |q''(0)|.
~~~

No constant depends on N.

The final F0-B1C-B theorem should package these into a legal boundary-flat hard-window approximation in the WCONT topology.

## Projection / legality firewall

OBS-016:

Raw periodic finite formulas are not automatically globally C² after hard zero extension.

The correction by itself is generally not boundary-flat.

The legal object is

~~~text
localizedFiniteVector L N (boundaryFlatProject N hN u).
~~~

Use F0-B1A for global C² legality of that complete vector.

## WCONT-A

WCONT-A is permanently merged and gives the fixed support estimate needed after F0-B1C-B.

There is no longer a family dominated-convergence bottleneck on the primary route.

## Source-faithful route

OBS-015 is permanent:

~~~text
source interface is not source negativity.
~~~

~~~text
S-GEOM / G1-B1A                               PROVED
S-IFACE / G1-B1B                              OPEN
G1-final QW_lambda|E_N=canonicalSourceMatrix  OPEN
S-NEG                                         OPEN
G23                                           OPEN
~~~

Internal F0-B work does not promote any of these source claims.

## Canonical normalization firewall

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

## Fallback classification

- generic Stone-Weierstrass rebuild — superseded;
- direct Fejer — dormant fallback;
- boundary-killer multiplication — ready fallback;
- F0-B2 direct additive continuity — fallback;
- old analytic W2-B — cross-check only.

## Structural clue retained for post-F1

A projected F1 vector retains

~~~text
1^T u = 0
1^T D u = 0
1^T D^2 u = 0
~~~

while the canonical matrix satisfies

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

Possible Krylov/displacement simplification remains LEAD / HYPOTHESIS.

## Current post-green records

- F0_B1C_A_POST_GREEN_PROJECTION_STABILITY_FRONTIER_2026_09_02.md
- ../../RESEARCH_LEADS_POST_91_DELTA.md

Historical settlement files remain frozen.

**RH remains OPEN.**
