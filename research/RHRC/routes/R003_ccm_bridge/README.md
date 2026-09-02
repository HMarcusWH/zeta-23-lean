# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. INTERNAL F1 + K0-F1 PROVED. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #96 merge 3712746a144d630ee41b89527b098e392822f2c6
theorem tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
theorem-bearing merged through = PR #96
live GitHub main = authoritative
RH = OPEN
~~~

Recent exact green/merged packages:

~~~text
#93 F0-B1C-B
  head 309c23f438be6e9b74383f1c164381ea68fef8a5
  RHRC #665 / Permansson #438
  merge c07d0f819b51fc85b18505e23fa061a6663e289d

#94 strict finite sign transfer + F1
  head d357c1511dba8678eb3a3a10944596c33a65fa11
  RHRC #667 / Permansson #440
  merge 8b54a72767c2703351990e2a67354511e9c9b83a

#96 constrained canonical finite wall
  head d628b7332e908701e85ef8ea33309e2bf548f2e5
  synthetic merge 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
  RHRC #679 / Permansson #452
  merge 3712746a144d630ee41b89527b098e392822f2c6
  tree 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
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
  -> K0-F1 constrained subspace/moment flag                     PROVED
  -> canonical Hermitianity                                     PROVED
  -> one-channel displacement on u,Du,D²u                       PROVED
  -> unit constrained negative witness                          PROVED
~~~

Current frontier: **Euclidean/Hilbert constrained compression**.

## K0-F1 production surface

PR #96 proves:

~~~text
u ∈ boundaryFlatSubspace N
  <-> BoundaryFlatCoefficients N u

M_k(Du)=M_{k+1}(u)

u,Du,D²u descend through the three-moment flag

canonicalSourceMatrixᴴ = canonicalSourceMatrix

[D,M]v = -1 * displacementPairing(v)
for every v with M0(v)=0
~~~

The last identity is specialized to u, Du and D²u.

The normalized F1 endpoint is:

`Zeta23.ExceptionalZero.exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero`.

## Next spectral bridge

The next primary package must use the Hilbert type

`EuclideanSpace ℂ (Fin (2*N+1))`

and `Matrix.toEuclideanLin`.

The raw function-space norm-one witness from #96 is not itself the Rayleigh-sphere theorem. See OBS-017.

Target:

~~~text
off-line zero
  -> negative Rayleigh direction in the Euclidean constrained sector
  -> negative eigenvalue of the compressed self-adjoint canonical operator.
~~~

A constrained eigenvector is not automatically a full eigenvector of M.

## Active derived leads

Not yet formalized:

~~~text
codim V₂ = 3 for N>=1
nonzero F1 witness -> N>=2
first 4×4 M-weighted Krylov block is real Hankel
~~~

## Source-faithful route

OBS-015 remains permanent. S-GEOM/G1-B1A is proved; S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain open as an independent cross-check route.

## Canonical normalization firewall

canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix. legacyPrintedMatrix = finiteMatrix.

## Dead-route firewall

DR-010 remains dead. The exact constrained D/M/g route is theorem-backed and distinct from the fitted small-commutator route.

## Current post-green records

- K0F1_POST_GREEN_CONSTRAINED_FINITE_WALL_RESET_2026_09_02.md
- ../../RESEARCH_LEADS_POST_96_DELTA.md

Earlier settlement files remain frozen.

**RH remains OPEN.**
