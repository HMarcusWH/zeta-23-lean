# RHRC formal audit — merged through F1

> **RH remains OPEN.**

## Current merged authority

~~~text
main = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
merged through = PR #94
date = 2026-09-02
~~~

## Recent exact validation chain

### PR #91 — F0-B1C-A

~~~text
head = cf1c9b6536264deb8773fa8b0bb3650b07fcff40
merge = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
RHRC #660 = SUCCESS
Permansson #433 = SUCCESS
~~~

### PR #93 — F0-B1C-B

~~~text
head = 309c23f438be6e9b74383f1c164381ea68fef8a5
merge = c07d0f819b51fc85b18505e23fa061a6663e289d
tree = 13c21db23ecdd5b4ed5bab9d39740ad09ede0c8e
RHRC #665 = SUCCESS
Permansson #438 = SUCCESS
~~~

Primary theorem: `Zeta23.CCM.exists_boundaryFlatFinite_WCONT_approx`.

### PR #94 — strict sign transfer + F1

~~~text
head = d357c1511dba8678eb3a3a10944596c33a65fa11
merge = 8b54a72767c2703351990e2a67354511e9c9b83a
tree = 0fca10d1904d85bd33763cc6728e22c1c5b9ef5d
RHRC #667 = SUCCESS
Permansson #440 = SUCCESS
~~~

RHRC #667 passed CCM build, ExceptionalZero build, forbidden-placeholder rejection, RHRC regression and the canonical/legacy normalization firewall.

Promoted theorem surfaces depend only on

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

## Current formal theorem state

~~~text
W2-A pair bridge                                      PROVED
W0 compact C² negative W witness                      PROVED
W1 strict-aperture collar                             PROVED
W2-ZS / direct diagonal W bridge                      PROVED
G1-A finite additive restriction                      PROVED
F0-B1A boundary-flat legal finite carrier             PROVED
F0-B1B exact boundary-flat projection                 PROVED
WCONT-A fixed-support genuine-W bound                 PROVED
F0-B1C-A raw uniform localized C² approximation       PROVED
F0-B1C-B legal boundary-flat WCONT approximation      PROVED
strict finite sign transfer                           PROVED
F1 canonical finite negative obstruction              PROVED

K0-F1 constrained canonical sector                    OPEN / NOW
constrained compression / minimizer                   OPEN
finite-wall impossibility                             OPEN
RH                                                    OPEN
~~~

## Exact F1 state

~~~text
off-line zeta zero
  -> exists L>0, N>=1, u,
       BoundaryFlatCoefficients N u
       and Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

This is one-way and does not prove canonical positivity or RH.

## Post-F1 derived state

Boundary-flatness gives M0=M1=M2=0.

With D=indexMatrix N, this DERIVES 1^T u=1^T Du=1^T D²u=0.

Separately PROVED:

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

The constrained collapse is a K0-F1 target, not yet a production theorem.

## Permanent semantic firewalls

1. RH remains OPEN.
2. `canonicalSourceMatrix` is sign-authoritative.
3. `finiteMatrix` is legacy printed normalization.
4. OBS-015 remains binding.
5. OBS-016 remains a generic legality warning; #93 proves the primary-route escape.
6. DR-010 remains falsified.
7. Low displacement rank alone does not imply positivity or RH.

**RH remains OPEN.**
