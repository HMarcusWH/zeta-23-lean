# HMWH Zeta23 fork — current audit entry point

> **Claim firewall: RH remains OPEN.**

This file records the current high-level validation state. Detailed theorem truth is determined by the merged Lean declarations, compiler/CI and machine registries.

## Current merged baseline

~~~text
main = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
merged through = PR #86
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
PR #86 synthetic merge = a687d8142513b163b9755a18ddf9612901484cac
PR #86 permanent merge = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
RHRC #605 = SUCCESS
Permansson #378 = SUCCESS
RH = OPEN
~~~

## Exact #86 validation

The final #86 theorem head passed:

- CCM formalization build;
- ExceptionalZero build;
- no-placeholder/no-project-axiom gate;
- RHRC claim and route registry lint;
- RHRC regression suite;
- R003 source-normalization firewall;
- R004 scalar-shift audit;
- external-oracle guard;
- independent Permansson verification.

The production theorem axiom surfaces contain only:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No `sorryAx` survived the final green build.

## Formal theorem state through PR #86

### W2-A

**PROVED / REGISTERED.**

The genuine concrete-zeta pair form is summability-safe and equals the literature explicit-formula RHS of the inherited `weilTest` on the exact admissible class.

### W0

**PROVED / REGISTERED.**

An off-line zero yields one compact C² pole-neutral physical test with strictly negative genuine W self-value.

### W1

**PROVED / REGISTERED.**

The negative test can be recentered into a strict interior aperture with `L=4r` and `tsupport h subset (r,3r) subset (0,L)` while preserving the two Fourier pole zeros and strict negativity.

### W2-ZS / direct diagonal W2-C

**PROVED / REGISTERED.**

For every compact C² concrete-zeta test:

~~~text
W(h,h)=localizedWeilAdditiveRHS(h,h).
~~~

The old analytic W2-B proof route remains OPEN / DORMANT as an independent cross-check.

### Strict negative localized-additive witness

**PROVED / REGISTERED.**

W1 + W2-ZS gives a strict-collar compact C² test with negative localized additive RHS.

### G1-A

**PROVED / REGISTERED.**

On the existing finite localized vectors, the repository additive RHS equals the cutoff-free/canonical finite quadratic form.

### F0-B1A — boundary-flat finite Weil restriction

**PROVED / REGISTERED.**

For positive `L`, finite `N` and arbitrary complex coefficients satisfying centered moments 0,1,2=0:

~~~text
localizedFiniteVector L N u is global C²
and compactly supported,

W(v,v)
  = localizedWeilAdditiveRHS(v,v)
  = quadraticForm(canonicalSourceMatrix L N) u.
~~~

Production claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

The carrier is nontrivial by the proved five-mode witness `[1/4,-1,3/2,-1,1/4]`.

## Current open frontier

~~~text
F0-B1B exact three-mode boundary-flat projection       OPEN / NOW
WCONT family-level common-support W continuity         OPEN
finite approximation in selected topology             OPEN
strict finite sign transfer                            OPEN
F1 canonical finite negative obstruction              OPEN
K0-K3                                                  OPEN
RH                                                     OPEN
~~~

F0-B2 direct localized-additive continuity remains a fallback, not the primary path.

## Normalization firewall

Canonical direct-source authority remains:

~~~text
canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix.
~~~

Historical `finiteMatrix` remains the printed-normalization object. The exact scalar shift is theorem-locked. PR #86 does not alter this map.

## Source-sign firewall

OBS-015 remains binding:

~~~text
source interface is not source negativity.
~~~

G1-B1A finite source transport is proved, but Haar/L²/PsiSharp/QW interface, G1-final, source negativity and G23 remain OPEN.

## Continuity firewall

Per-approximant summability must never be upgraded to family-level dominated convergence. The next WCONT work should test reuse of the existing inverse-square zero weight with one uniform approximation-family constant.

## Current post-green settlement

`research/RHRC/routes/R003_ccm_bridge/F0_B1A_POST_GREEN_PROJECTION_CONTINUITY_FRONTIER_2026_09_01.md`

**RH remains OPEN.**
