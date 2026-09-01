# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

RHRC tracks theorem-backed progress, route boundaries, research leads and validation state for the HMWH Zeta23 fork.

Formal mathematical authority is:

1. live GitHub head / Lean compiler / CI;
2. exact checked theorem declarations;
3. merged main + machine registries on that ref;
4. active route README;
5. living research-control SSOTs;
6. current external handover;
7. historical settlements and older audits.

## Current authority snapshot

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
RH = OPEN
~~~

Recent theorem-bearing merges:

~~~text
#88 F0-B1B exact boundary-flat projection
#89 WCONT-A common-support quantitative W bound
#91 F0-B1C-A uniform raw localized C² approximation
~~~

## Current theorem-backed internal route

~~~text
W2-A pair bridge                                      PROVED
W0 negative compact C² pole-neutral W test           PROVED
W1 strict finite-aperture collar                     PROVED
W2-ZS / direct diagonal W identity                   PROVED
strict negative localized-additive witness           PROVED
G1-A finite additive restriction                     PROVED
F0-B1A boundary-flat legal finite carrier            PROVED
F0-B1B exact boundary-flat projection                PROVED
WCONT-A fixed-support quantitative genuine-W bound   PROVED
F0-B1C-A raw uniform localized C² approximation      PROVED

F0-B1C-B quantitative projection stability           OPEN / NOW
strict finite sign transfer                          OPEN
F1 canonical finite negative obstruction             OPEN
RH                                                    OPEN
~~~

Registered production claims include:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
R003_BOUNDARY_FLAT_PROJECTION
R003_WEIL_COMMON_SUPPORT_BOUND
R003_LOCALIZED_UNIFORM_C2_APPROXIMATION
~~~

## What #91 closed

PR #91 proves the previously load-bearing raw approximation bridge.

For strict-collar C² targets on one fixed positive aperture, finite centered localized Fourier functions approximate value, first jet and second jet uniformly on the closed aperture, with q(0)=0 exactly.

The pinned Mathlib finite Fourier density theorem used in production is the root declaration

~~~text
span_fourier_closure_eq_top
~~~

together with root declarations fourier, fourierCoeff and fourierCoeffOn.

The old AddCircle-qualified names in earlier living docs were stale API descriptions and have been corrected here.

## Current execution priority

1. Build F0-B1C-B, not another Fourier approximation layer.
2. Use q(0)=0 to theorem-lock M0=0 exactly.
3. Convert q'(0), q''(0) into explicit M1,M2 bounds.
4. Prove fixed-L, N-independent L1 bounds for the three-mode correction and its second jet.
5. Apply boundaryFlatProject and use F0-B1A for legal hard-window C² admissibility.
6. Produce one boundary-flat finite approximation in the exact WCONT topology.
7. Use W1 + WCONT-A to transfer strict negativity.
8. Cash out through F0-B1A to strengthened boundary-flat F1.
9. Stop for a full Post-Green Research Pass before K0-K3.

## Post-#91 derived simplification

**DERIVED / not yet separately formalized.**

#91 gives q(0)=0 exactly. #88 gives

q(0)=(1/sqrt L) M0.

For L>0,

M0=0.

Thus the correction simplifies to

~~~text
c_-1 = (M1-M2)/2
c_0  = M2
c_+1 = -(M1+M2)/2.
~~~

The exact endpoint identities imply

~~~text
|M1| = L^(3/2)/(2*pi) * |q'(0)|
|M2| = L^(5/2)/(4*pi^2) * |q''(0)|.
~~~

The next formalization target is

~~~text
integral_0^L |correction|
  <= L^2/(2*pi) |q'(0)|
   + L^3/(2*pi^2) |q''(0)|

integral_0^L |correction''|
  <= 2*pi |q'(0)| + L |q''(0)|.
~~~

These are not yet registry claims.

## WCONT-A firewall

The accepted theorem is quantitative and family-independent:

~~~text
||W(f,g)||
  <= exp(Lambda) * zetaInvSqZeroMass
     * (||f||_1 + ||f''||_1) * ||g||_1.
~~~

Do not replace it by the weaker statement that every approximant has a summable W series.

## Approximation / legality firewall

OBS-016 is now explicit.

Raw periodic finite formulas are not automatically legal after hard zero extension.

The legal object is the complete projected hard-window vector

~~~text
localizedFiniteVector L N (boundaryFlatProject N hN u).
~~~

The correction alone is not automatically boundary-flat.

## Source route

OBS-015 remains binding:

~~~text
source interface is not source negativity.
~~~

Internal F0-B work does not silently promote G1-final, S-NEG, G23 or ambient source QW claims.

## Canonical normalization

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

## Current research records

Living:

- CURRENT_RESEARCH_PLAN.md
- RESEARCH_LEADS.md
- CLAIM_REGISTRY.json
- routes/ROUTE_REGISTRY.json
- routes/R003_ccm_bridge/README.md

Latest delta:

- RESEARCH_LEADS_POST_91_DELTA.md

Latest post-green settlement:

- routes/R003_ccm_bridge/F0_B1C_A_POST_GREEN_PROJECTION_STABILITY_FRONTIER_2026_09_02.md

Historical settlement and delta files remain frozen.

**RH remains OPEN.**
