# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains theorem-backed research infrastructure and formally validated constraints relevant to the Riemann Hypothesis. Green supporting mathematics is progress, not a proof of RH.

## Current authority snapshot

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
RH = OPEN
~~~

PR #91 final hardened theorem head:

~~~text
cf1c9b6536264deb8773fa8b0bb3650b07fcff40
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
RHRC #660 = SUCCESS
Permansson #433 = SUCCESS
~~~

The final PR tree is exactly the permanent merge tree.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral h with Re W(h,h)<0                 PROVED
  -> strict aperture collar tsupport h ⊂ (0,L)                 PROVED
  -> concrete-zeta zero-side evenization                       PROVED
  -> W(h,h)=localizedWeilAdditiveRHS(h,h)                      PROVED
  -> finite additive restriction / canonical matrix            PROVED
  -> F0-B1A legal boundary-flat finite carrier                 PROVED
  -> F0-B1B exact -1,0,+1 boundary-flat projection             PROVED
  -> WCONT-A fixed-support genuine-W perturbation bound         PROVED
  -> F0-B1C-A raw localized uniform C² approximation            PROVED
  -> F0-B1C-B quantitative projection stability                OPEN / NOW
  -> strict finite sign transfer                               OPEN
  -> F1 canonical finite negative obstruction                  OPEN
  -> K0-K3 finite-negative exclusion                           OPEN
  -> RH                                                        OPEN
~~~

## F0-B1A + F0-B1B legality package

For positive L, centered coefficients satisfying

M0(u)=M1(u)=M2(u)=0

produce a hard-window localized finite vector that is globally C², compactly supported, and satisfies

W(v,v)=quadraticForm(canonicalSourceMatrix L N)u.

PR #88 proves an exact projection for N>=1, correcting only centered modes -1,0,+1:

c_-1=(M1-M2)/2,
c_0=M2-M0,
c_1=-(M1+M2)/2.

It also theorem-locks exact endpoint value/first-jet/second-jet identities for M0,M1,M2.

Production claims:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
R003_BOUNDARY_FLAT_PROJECTION
~~~

## WCONT-A

PR #89 is permanently merged.

For one fixed support radius Lambda,

||W(f,g)||
  <= exp(Lambda) * zetaInvSqZeroMass
     * (||f||_1 + ||f''||_1) * ||g||_1.

The exact diagonal cross-term identity and a quantitative self-form perturbation estimate are also proved with summability established before infinite-sum algebra.

Production claim:

~~~text
R003_WEIL_COMMON_SUPPORT_BOUND
~~~

The family dominated-convergence seam is therefore closed on the primary route.

## F0-B1C-A — raw finite approximation

PR #91 proves

~~~text
Zeta23.CCM.exists_localizedFinite_uniform_C2_approx
~~~

For every L>0, every complex-valued C² target with tsupport strictly inside (0,L), and every epsilon>0, there exist N>=1 and centered finite coefficients u such that the formula-level finite Fourier function q

- satisfies q(0)=0 exactly;
- approximates h uniformly on [0,L];
- approximates the first jet uniformly;
- approximates the second jet uniformly.

Final production axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

The proof uses the exact pinned Mathlib declarations span_fourier_closure_eq_top, fourier, fourierCoeff, and fourierCoeffOn, then explicitly transports finite integer support into the repository's normalized centered coordinates.

Production claim:

~~~text
R003_LOCALIZED_UNIFORM_C2_APPROXIMATION
~~~

### Firewall

This is a formula-level periodic approximation theorem. It does not make the raw hard-window zero extension globally C². The complete projected vector remains the legal W object.

## Immediate frontier — F0-B1C-B

Post-#91 composition with #88 yields a useful simplification.

**DERIVED / not yet separately formalized:**

Since q(0)=0 exactly and L>0,

M0(q)=0.

Thus projection-smallness needs only M1,M2. From the exact endpoint identities,

|M1| = L^(3/2)/(2*pi) * |q'(0)|,

|M2| = L^(5/2)/(4*pi^2) * |q''(0)|.

For the three-mode correction c, the next formalization target is

integral_0^L |c|
  <= L^2/(2*pi) * |q'(0)|
   + L^3/(2*pi^2) * |q''(0)|,

and

integral_0^L |c''|
  <= 2*pi*|q'(0)| + L*|q''(0)|.

These constants depend on fixed L, never on N.

The target F0-B1C-B theorem is therefore:

~~~text
strict-collar C² h
epsilon > 0
  -> exists N>=1,u
       BoundaryFlatCoefficients N u
       and legal p = localizedFiniteVector L N u
       with
       integral ||p-h|| < epsilon
       integral ||p''-h''|| < epsilon.
~~~

## Projection firewall

The correction boundaryFlatProject(u)-u is generally not itself boundary-flat. Its hard-window realization must not be treated as an independently admissible C² Weil test.

Use only the complete projected vector.

See OBS-016.

## Canonical finite object

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

Absolute spectral-sign claims must use the canonical object.

## Parallel source route

~~~text
S-GEOM -> G1-B1A                         PROVED
S-IFACE / G1-B1B                         OPEN
G1-final QW_lambda|E_N = canonical matrix OPEN

separate sign entry:
S-NEG or exact sign-carrying composition  OPEN

then:
G23                                      OPEN
~~~

OBS-015 remains binding: source interface is not source negativity.

## Fallback routes

- direct Fejer raw approximation — dormant after #91;
- boundary-killer multiplication — ready fallback;
- F0-B2 direct localized-additive continuity — fallback;
- old analytic W2-B route — independent cross-check only.

Generic Stone-Weierstrass infrastructure for F0-B1C-A is superseded by the exact pinned Fourier-span theorem already used in #91.

## Post-F1 boundary

A green F1 is the next major dependency-graph event. It must trigger a full Post-Green Research Pass before K0-K3.

The external roadmap version v2.0 remains reserved for green F1 or a comparably large theorem-state change.

## Current research control plane

Living:

- research/RHRC/README.md
- research/RHRC/CURRENT_RESEARCH_PLAN.md
- research/RHRC/RESEARCH_LEADS.md
- research/RHRC/CLAIM_REGISTRY.json
- research/RHRC/routes/ROUTE_REGISTRY.json
- research/RHRC/routes/R003_ccm_bridge/README.md

Latest delta:

- research/RHRC/RESEARCH_LEADS_POST_91_DELTA.md

Latest post-green settlement:

- research/RHRC/routes/R003_ccm_bridge/F0_B1C_A_POST_GREEN_PROJECTION_STABILITY_FRONTIER_2026_09_02.md

Historical settlements remain frozen records of earlier theorem states.

**RH remains OPEN.**
