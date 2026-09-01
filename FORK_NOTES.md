# HMWH Zeta23 fork — research boundary and provenance

> **RH remains OPEN.**

The fork is an active Lean-backed RH research program, not a solved-conjecture branch. Its purpose is to shrink the admissible counterexample space through formally validated detector, explicit-formula, finite-matrix and rigidity constraints while keeping a strict claim firewall.

## Authority snapshot

### Merged main

~~~text
main = 879eb6d356d8f62bbe0b9241596b15892498ea64
tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
merged through = PR #88
RH = OPEN
~~~

### Green theorem candidate

~~~text
PR #89 head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
status = OPEN / NOT MERGED at documentation time
~~~

## Current canonical finite object

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.

legacyPrintedMatrix = finiteMatrix.
~~~

The scalar identity correction between the canonical and historical printed normalization remains theorem-locked.

## Internal theorem-backed route

~~~text
W2-A   genuine W / literature-RHS pair bridge
W0     one compact C² pole-neutral negative W test
W1     strict finite-aperture support collar
W2-ZS  concrete-zeta zero-side evenization
W2-C   diagonal W = localized additive RHS
G1-A   finite localized-additive restriction
F0-B1A boundary-flat legal finite carrier
        + exact genuine W = canonical finite quadratic form
F0-B1B exact three-mode projection into that carrier
        + fixed-point/idempotence
        + endpoint jet/moment identities
WCONT-A quantitative common-support genuine-W bound
        + fixed inverse-square zero majorant
        + exact cross-term identity
        + diagonal perturbation bound
~~~

F0-B1B is merged. WCONT-A is proved on exact green PR #89 head. The current primary frontier is

~~~text
F0-B1C WCONT-matched finite approximation
  -> projection-smallness
  -> strict finite sign transfer
  -> F1 canonical finite negative obstruction.
~~~

F0-B2 direct localized-additive continuity and boundary-killer multiplication remain fallbacks.

## Why #88 changes the approximation problem

The legality correction uses only centered modes -1,0,+1. Its algebra is controlled entirely by the three centered moments M0,M1,M2. The exact endpoint identities now show those moments are scalar-equivalent to the value/first-jet/second-jet of the unwindowed finite trigonometric polynomial at the endpoint.

**DERIVED / not separately formalized:** the correction changes only three coefficient coordinates, independent of N.

Do not upgrade that observation into a norm estimate until the inequalities are proved.

## Source-faithful route

OBS-015 remains binding:

~~~text
source interface is not source negativity.
~~~

The multiplicative Haar/L²/PsiSharp/QW interface, actual QW_lambda|E_N restriction, source sign entry and G23 remain open.

## Boundary-flat structural clue

A future F1 vector on the projected carrier retains

~~~text
1^T u = 0
1^T D u = 0
1^T D² u = 0,
~~~

while the canonical matrix has

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

Possible post-F1 Krylov/displacement simplification is a **LEAD / HYPOTHESIS** only.

## Research boundary rules

- Compiler/CI evidence is authoritative for formal validity.
- Exact checked theorem heads may be PROVED before merge, but merged-main claims must state merge status correctly.
- Machine registries on a PR branch become permanent only when that branch is merged.
- Green support infrastructure is not RH.
- Numerical signals are not theorem claims.
- Source interface does not imply source negativity.
- Per-member summability is not uniform dominated convergence; WCONT-A now supplies the required explicit family-independent majorant.
- The #88 correction alone is not automatically a globally admissible hard-window test.
- Historical failed/obsolete routes remain useful only when a named blocking premise changes.

## Current post-green settlement

research/RHRC/routes/R003_ccm_bridge/WCONT_A_POST_GREEN_F0B1C_FRONTIER_2026_09_01.md

The next major roadmap version remains reserved for a green F1 or an equivalently large dependency-graph event.

**RH remains OPEN.**
