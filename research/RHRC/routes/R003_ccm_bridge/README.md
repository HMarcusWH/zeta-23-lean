# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. INTERNAL F1 PROVED. RH OPEN.**

## Current authority

~~~text
main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
merged through = PR #94
RH = OPEN
~~~

Recent exact green/merged packages:

~~~text
#91 F0-B1C-A
  head cf1c9b6536264deb8773fa8b0bb3650b07fcff40
  RHRC #660 / Permansson #433
  merge bab94aed54298de6fc6676808a0b0e46c2db6046

#93 F0-B1C-B
  head 309c23f438be6e9b74383f1c164381ea68fef8a5
  RHRC #665 / Permansson #438
  merge c07d0f819b51fc85b18505e23fa061a6663e289d
  tree 13c21db23ecdd5b4ed5bab9d39740ad09ede0c8e

#94 strict finite sign transfer + F1
  head d357c1511dba8678eb3a3a10944596c33a65fa11
  RHRC #667 / Permansson #440
  merge 8b54a72767c2703351990e2a67354511e9c9b83a
  tree 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
~~~

## Closed internal theorem ladder

~~~text
off-line zero
  -> W0 compact C² negative W test                              PROVED
  -> W1 strict support collar                                   PROVED
  -> W2-ZS / diagonal W bridge                                  PROVED
  -> G1-A finite additive restriction                           PROVED
  -> F0-B1A legal boundary-flat finite carrier                  PROVED
  -> F0-B1B exact projection                                    PROVED
  -> WCONT-A quantitative W continuity                          PROVED
  -> F0-B1C-A raw uniform localized C² approximation            PROVED
  -> F0-B1C-B legal boundary-flat WCONT approximation           PROVED
  -> strict finite negative W transfer                          PROVED
  -> F1 canonical finite negative obstruction                   PROVED
~~~

Current frontier: **K0-F1 constrained canonical sector**.

## F1 production surface

`Zeta23.ExceptionalZero.exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero` proves that an off-line zero forces L>0,N>=1,u with BoundaryFlatCoefficients N u and negative real quadratic form for canonicalSourceMatrix.

## Post-F1 structural state

BoundaryFlatCoefficients gives M0=M1=M2=0. The canonical displacement theorem gives [D,M]=g1^T-1g^T. The annihilations 1^T u=1^T Du=1^T D²u=0 are DERIVED and will be theorem-locked in K0-F1.

Do not assume D preserves the full boundary-flat sector.

## Source-faithful route

OBS-015 remains permanent. S-GEOM/G1-B1A is proved; S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain open as an independent cross-check route.

## Canonical normalization firewall

canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix. legacyPrintedMatrix = finiteMatrix.

## Dead-route firewall

DR-010 remains dead. The exact constrained D/M/g route is distinct from the fitted small-commutator route.

## Current post-green records

- F1_POST_GREEN_FINITE_WALL_RESET_2026_09_02.md
- ../../RESEARCH_LEADS_POST_94_DELTA.md

Earlier settlement files remain frozen.

**RH remains OPEN.**
