# RHRC formal audit — merged through K0-F1 / PR #96

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #96 merge 3712746a144d630ee41b89527b098e392822f2c6
theorem tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
theorem-bearing merged through = PR #96
live GitHub main = authoritative
date = 2026-09-02
~~~

## Recent exact validation chain

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

### PR #96 — constrained canonical finite-wall package

~~~text
head = d628b7332e908701e85ef8ea33309e2bf548f2e5
synthetic merge = 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
merge = 3712746a144d630ee41b89527b098e392822f2c6
tree = 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
RHRC #679 = SUCCESS
Permansson #452 = SUCCESS
~~~

RHRC #679 passed:

~~~text
claim/regression suite
R003 cutoff-free normalization lock
finite dictionary external-oracle guards
source normalization firewall
R004 scalar-shift audit
external-reference dependency rejection
CCM build
ExceptionalZero build
forbidden-placeholder rejection
~~~

Permansson #452 passed theorem build plus placeholder/extra-axiom rejection.

The promoted #96 theorem surfaces depend only on

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

The validated synthetic merge tree equals the merged main tree.

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
K0-F1 constrained subspace/moment flag                PROVED
canonical Hermitianity                                PROVED
one-channel displacement on u,Du,D²u                  PROVED
unit constrained negative canonical witness           PROVED

Euclidean/PiLp₂ constrained transport                 OPEN / NOW
exact codim(V₂)=3                                     DERIVED / OPEN FORMALIZATION
F1 witness N>=2                                       DERIVED / OPEN FORMALIZATION
compressed negative canonical eigenmode               OPEN
finite-wall impossibility                             OPEN
RH                                                    OPEN
~~~

## Exact #96 endpoint

Lean proves:

~~~text
off-line zeta zero
  -> exists L>0, N>=1, u,
       u ∈ boundaryFlatSubspace N
       and ‖u‖ = 1
       and Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

This is one-way and does not prove canonical positivity or RH.

The norm is the raw function-space norm, not the Euclidean/PiLp₂ norm required by Rayleigh theory.

## Exact constrained displacement state

For zero-moment v:

~~~text
[D,M] v = -1 * displacementPairing(v).
~~~

For boundary-flat u this holds for v=u, Du and D²u.

The proof uses the exact canonical displacement identity and the theoremized moment flag. It does not use fitted generators, small-commutator limits or spectral gaps.

## Permanent semantic firewalls

1. RH remains OPEN.
2. `canonicalSourceMatrix` is sign-authoritative.
3. `finiteMatrix` is legacy printed normalization.
4. OBS-015 remains binding.
5. OBS-016 remains a generic legality warning; #93 proves the primary-route escape.
6. OBS-017 forbids treating raw function-space norm one as Euclidean Rayleigh normalization.
7. DR-010 remains falsified.
8. One-channel/low-rank displacement alone does not imply positivity or RH.

**RH remains OPEN.**
