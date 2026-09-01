# HMWH Zeta23 fork — research boundary and provenance

> **RH remains OPEN.**

This fork is an active Lean-backed RH research program. Its purpose is to shrink the admissible counterexample space through theorem-backed explicit-formula, finite-matrix, approximation and rigidity constraints while maintaining a strict claim firewall.

## Authority snapshot

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
RH = OPEN
~~~

Recent permanent theorem packages:

~~~text
#88 F0-B1B exact boundary-flat projection
#89 WCONT-A quantitative genuine-W continuity
#91 F0-B1C-A raw uniform localized C² approximation
~~~

## Canonical finite object

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

The two normalizations differ by a theorem-locked scalar identity shift. Absolute spectral-sign claims do not transfer through that shift automatically.

## Current internal theorem-backed route

~~~text
W2-A   genuine W / literature-RHS pair bridge
W0     one compact C² pole-neutral negative W test
W1     strict finite-aperture support collar
W2-ZS  concrete-zeta zero-side evenization
W2-C   diagonal W = localized additive RHS
G1-A   finite localized-additive restriction
F0-B1A boundary-flat legal finite carrier
        + genuine W = canonical finite quadratic form
F0-B1B exact -1,0,+1 projection
        + fixed-point/idempotence
        + endpoint jet/moment identities
WCONT-A fixed-support genuine-W bound
        + fixed inverse-square zero majorant
        + exact cross-term identity
        + diagonal perturbation estimate
F0-B1C-A uniform raw finite Fourier approximation
        + exact q(0)=0 anchor
        + uniform q,q',q'' approximation
~~~

The primary frontier is now

~~~text
F0-B1C-B quantitative projection stability
  -> strict finite sign transfer
  -> F1 canonical finite negative obstruction.
~~~

## What #91 changes

The Fourier-density question is no longer open on the primary route.

Pinned Mathlib's exact root declaration span_fourier_closure_eq_top was sufficient, together with explicit Finsupp extraction, zero-mode removal, twice integration and centered-coordinate reconstruction.

**DERIVED:** because #91 anchors q(0)=0, #88 gives M0=0 exactly. The next projection theorem only needs quantitative M1,M2 control.

Expected correction constants depend on fixed L, not N.

## Research boundary rules

- Compiler/CI evidence is authoritative.
- Merged-main truth must track exact merge state and tree.
- Green infrastructure is not RH.
- Numerical signals are not theorem claims.
- Source interface does not imply source negativity.
- Raw formula-level approximation does not imply legal hard-window C² admissibility.
- The three-mode correction alone is not a legal W test.
- WCONT-A, not per-approximant summability, is the accepted family-level continuity seam.
- Historical failed/superseded routes may be revisited only when a named premise changes.

## Source-faithful route

OBS-015 remains binding.

The Haar/L²/PsiSharp/QW interface, actual QW_lambda|E_N restriction, source sign entry and G23 remain OPEN.

## Boundary-flat structural clue

A future F1 witness produced by this route retains

1^T u = 0,
1^T D u = 0,
1^T D^2 u = 0,

while the canonical matrix satisfies

D M - M D = g 1^T - 1 g^T.

Possible post-F1 Krylov/displacement simplification remains a **LEAD / HYPOTHESIS**.

## Current post-green settlement

research/RHRC/routes/R003_ccm_bridge/F0_B1C_A_POST_GREEN_PROJECTION_STABILITY_FRONTIER_2026_09_02.md

The next major external roadmap version remains reserved for green F1 or an equivalently large dependency-graph event.

**RH remains OPEN.**
