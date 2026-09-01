# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains formalized research infrastructure and theorem-backed constraints relevant to the Riemann Hypothesis. Compiler/CI validity of supporting results must never be upgraded into a claim that RH is proved.

## Authority snapshot

### Current merged baseline

~~~text
main = 879eb6d356d8f62bbe0b9241596b15892498ea64
tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
merged through = PR #88
RH = OPEN
~~~

### Current green promotion candidate

~~~text
PR #89 = WCONT-A quantitative common-support genuine-W bound
theorem head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
PR state at documentation time = OPEN / NOT MERGED
RH = OPEN
~~~

Live GitHub/Lean/CI is authoritative if this file becomes stale. The distinction between merged main and a green unmerged theorem head is intentional.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> one compact C² pole-neutral test with Re W(h,h)<0          [PROVED]
  -> strict aperture collar, L=4r                              [PROVED]
  -> concrete-zeta zero-side evenization                       [PROVED]
  -> W(h,h)=localizedWeilAdditiveRHS(h,h)                     [PROVED]
  -> strict negative localized-additive witness                [PROVED]
  -> finite additive restriction / canonical matrix            [PROVED]
  -> F0-B1A boundary-flat finite carrier                       [PROVED]
       moments 0,1,2 = 0
       -> hard-window vector is global C²
       -> W(v,v)=quadraticForm(canonicalSourceMatrix)u
  -> F0-B1B exact three-mode boundary-flat projection          [PROVED / MERGED]
       arbitrary u, N>=1
       -> exact correction on modes -1,0,+1
       -> moments 0,1,2 vanish
       -> fixed-point + idempotence
       -> exact endpoint value/jet <-> moment identities
  -> WCONT-A quantitative genuine-W bound                      [PROVED ON GREEN #89 HEAD]
       fixed support envelope
       -> explicit inverse-square zero majorant
       -> exact cross-term identity
       -> quantitative diagonal perturbation bound
  -> F0-B1C matched finite approximation + projection-smallness[OPEN / NEXT]
  -> strict finite sign transfer                               [OPEN]
  -> F1 canonical finite negative obstruction                  [OPEN]
  -> K0-K3 finite-negative exclusion                           [OPEN]
  -> RH                                                        [OPEN]
~~~

## F0-B1A + F0-B1B finite legality package

PR #86 theorem-locks the legal finite carrier. For positive L and centered coefficients u satisfying

~~~text
M0(u)=M1(u)=M2(u)=0,
~~~

the hard-window vector is global C² and

~~~text
zetaZeroConfig.W(v,v)
  = quadraticForm(canonicalSourceMatrix L N) u.
~~~

Production claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

PR #88 theorem-locks an exact algebraic projection into that carrier for N>=1. If m0,m1,m2 are the three centered moments, the correction supported on centered modes -1,0,+1 is

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

Lean proves

~~~text
M0(c) = -m0
M1(c) = -m1
M2(c) = -m2
~~~

and therefore boundaryFlatProject N hN u is boundary-flat. It also proves that boundary-flat vectors are fixed and that the projection is idempotent.

Primary theorem:

~~~text
Zeta23.CCM.boundaryFlatProject_boundaryFlat
~~~

Supporting production surface:

~~~text
Zeta23.CCM.boundaryFlatProject_eq_self_of_boundaryFlat
Zeta23.CCM.boundaryFlatProject_idempotent
Zeta23.CCM.localizedFiniteFunction_zero_eq_centeredMoment_zero
Zeta23.CCM.localizedFiniteFirstJet_zero_eq_centeredMoment_one
Zeta23.CCM.localizedFiniteSecondJet_zero_eq_centeredMoment_two
~~~

The production axiom surface is

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no sorryAx.

The N=0 sector is genuinely degenerate and is explicitly excluded from the three-mode projection by 1 <= N.

## Immediate internal frontier — F0-B1C

WCONT-A is now theorem-backed on exact green PR #89 head. The family-level zero-side continuity seam is closed by

~~~text
Zeta23.ExceptionalZero.zeta_W_norm_le_commonSupport
Zeta23.ExceptionalZero.zeta_W_self_sub_self_eq_cross
Zeta23.ExceptionalZero.zeta_W_self_sub_self_norm_le_commonSupport
~~~

For one fixed support radius, the self-form error is controlled by the two first-leg quantities

~~~text
integral ||p-h||
integral ||(p-h)''||.
~~~

Therefore the next load-bearing theorem is not another Weil-form theorem. It is **F0-B1C**: construct boundary-flat finite localized vectors in one fixed aperture with those two errors tending to zero.

Endpoint value/first-jet/second-jet control remains necessary only to make the exact #88 three-mode projection quantitatively small.

A high-priority lead is to use pinned Mathlib's RCLike Stone-Weierstrass theorem to approximate the periodic second derivative first, enforce zero mean, and integrate twice into the finite Fourier sector. This is a LEAD, not yet a repository theorem.

## Projection-smallness firewall

The correction c=P(u)-u is generally **not itself boundary-flat**. Its hard-window realization must not automatically be treated as an independently global-C² admissible Weil test.

The safe object is the complete projected vector

~~~text
localizedFiniteVector L N (boundaryFlatProject N hN u),
~~~

which is boundary-flat and therefore legal by F0-B1A.

PR #88 does not yet prove quantitative norm bounds for the correction.

## Canonical finite object

The direct source finite matrix authority remains

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
~~~

The historical printed-normalization object remains separate:

~~~text
legacyPrintedMatrix = finiteMatrix.
~~~

No file should relabel finiteMatrix as the canonical source matrix.

## Parallel source route

~~~text
S-GEOM -> G1-B1A [PROVED] -> S-IFACE/G1-B1B -> G1-final

separate sign entry:
S-NEG or exact W/localized-additive/QW sign composition

then:
G23 -> F1.
~~~

OBS-015: **source interface is not source negativity.**

## Current route priority

~~~text
PRIMARY INTERNAL
  F0-B1C WCONT-matched finite approximation
  -> quantitative three-mode projection stability
  -> strict sign transfer
  -> F1

FALLBACK INTERNAL
  F0-B2 direct localized-additive continuity
  boundary-killer multiplication
  old analytic W2-B route as independent cross-check

PARALLEL SOURCE
  S-GEOM / S-IFACE / G1-final / S-NEG / G23
~~~

Pinned Mathlib does not currently supply a ready Fejer theorem. Do not hide a load-bearing density argument behind “standard Fourier approximation.”

## Post-F1 boundary

A green F1 is the next major dependency-graph event. It must trigger a full Post-Green Research Pass before K0-K3 are implemented. The external handover version v2.0 remains reserved for green F1 or an equivalently large theorem-state change.

## Research control plane

See:

- research/RHRC/README.md
- research/RHRC/CURRENT_RESEARCH_PLAN.md
- research/RHRC/RESEARCH_LEADS.md
- research/RHRC/RESEARCH_LEADS_POST_88_DELTA.md
- research/RHRC/RESEARCH_LEADS_POST_89_DELTA.md
- research/RHRC/CLAIM_REGISTRY.json
- research/RHRC/routes/ROUTE_REGISTRY.json
- research/RHRC/routes/R003_ccm_bridge/README.md
- research/RHRC/routes/R003_ccm_bridge/F0_B1B_POST_GREEN_WCONT_FRONTIER_2026_09_01.md
- research/RHRC/routes/R003_ccm_bridge/WCONT_A_POST_GREEN_F0B1C_FRONTIER_2026_09_01.md

Historical post-green settlements remain frozen records of earlier theorem states.

Formal status labels are intentionally strict: PROVED / DERIVED / LEAD-HYPOTHESIS / EXPERIMENTAL SIGNAL / OPEN.

**RH remains OPEN.**
