# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**
>
> This repository contains formalized research infrastructure and theorem-backed constraints relevant to the Riemann Hypothesis. Compiler/CI validity of supporting results must never be upgraded into a claim that RH is proved.

## Current merged baseline

~~~text
main = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
merged through = PR #86
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
RHRC #605 = SUCCESS
Permansson #378 = SUCCESS
RH = OPEN
~~~

Live GitHub/Lean/CI is authoritative if this file becomes stale.

## Current RH-directed theorem ladder

The shortest internal CCM route now has the following theorem-backed front end:

~~~text
off-line zeta zero
  -> one compact C² pole-neutral test with Re W(h,h)<0       [PROVED]
  -> strict aperture collar, L=4r                           [PROVED]
  -> concrete-zeta zero-side evenization                     [PROVED]
  -> W(h,h)=localizedWeilAdditiveRHS(h,h)                   [PROVED]
  -> strict negative localized-additive witness              [PROVED]
  -> finite additive restriction / canonical matrix          [PROVED]
  -> boundary-flat finite carrier                            [PROVED]
       centered moments 0,1,2 = 0
       -> hard-window vector is global C²
       -> W(v,v)=quadraticForm(canonicalSourceMatrix)u
  -> exact projection / approximation / W continuity         [OPEN]
  -> F1 canonical finite negative obstruction                [OPEN]
  -> K0-K3 finite-negative exclusion                         [OPEN]
  -> RH                                                       [OPEN]
~~~

## PR #86 — F0-B1A

PR #86 theorem-locks a nontrivial finite sector on which the genuine concrete-zeta Weil form is already the canonical finite CCM quadratic form.

Production theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
~~~

Supporting legality theorem:

~~~text
Zeta23.CCM.contDiff_localizedFiniteVector_of_boundaryFlat
~~~

Boundary-flat coefficients satisfy

~~~text
sum u_n = 0
sum n*u_n = 0
sum n^2*u_n = 0.
~~~

The legal sector is nonzero: Lean proves the five-mode vector `[1/4,-1,3/2,-1,1/4]` satisfies the constraints and is not zero.

Registered claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

Axiom surface for the production results is the normal project surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

The no-placeholder/no-project-axiom gate passed.

## Immediate internal frontier

The next mathematical package is **F0-B1B exact boundary-flat projection**.

For `N>=1`, if `m0,m1,m2` are the three centered moments of an arbitrary coefficient vector, the candidate correction on modes `-1,0,+1` is

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

The next theorem should prove this cancels all three moments exactly and define a fixed-point/idempotent projection onto the #86 legal carrier.

Then the load-bearing analytic gate is **WCONT**: prove a family-level common-support continuity theorem for W strong enough to preserve the existing strict negative margin.

Permanent warning:

~~~text
per-approximant Summable
  does not imply
one summable majorant for the approximation family.
~~~

The repository already contains inverse-square zero-summability machinery (`zero_sum_inv_sq_gen`, `EF_zero_sum_summable_gen`) that should be tested before building new zero-density theory.

## Canonical finite object

The direct source finite matrix authority remains

~~~text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
~~~

The historical printed-normalization object is retained separately:

~~~text
legacyPrintedMatrix = finiteMatrix.
~~~

The theorem-locked scalar identity shift between the two does not change the displacement commutator. No file should relabel `finiteMatrix` as the canonical source matrix.

## Parallel source route

The source-faithful route remains active, but source interface and source sign are separate obligations.

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
  F0-B1B projection
  -> WCONT
  -> finite approximation/sign transfer
  -> F1

FALLBACK INTERNAL
  F0-B2 direct localized-additive continuity
  old analytic W2-B route as independent cross-check

PARALLEL SOURCE
  S-GEOM / S-IFACE / G1-final / S-NEG / G23
~~~

Pinned Mathlib does not currently supply a ready Fejer theorem. Do not hide a load-bearing density argument behind “standard Fourier approximation”; formalize only the approximation theorem required by the selected W topology.

## Post-F1 boundary

A green F1 is the next major dependency-graph event. It must trigger a full Post-Green Research Pass before K0-K3 are implemented. The external handover version `v2.0` is reserved for green F1 or an equivalently large theorem-state change.

## Research control plane

See:

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/routes/ROUTE_REGISTRY.json`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/routes/R003_ccm_bridge/F0_B1A_POST_GREEN_PROJECTION_CONTINUITY_FRONTIER_2026_09_01.md`

Formal status labels are intentionally strict: PROVED / DERIVED / LEAD-HYPOTHESIS / EXPERIMENTAL SIGNAL / OPEN.

**RH remains OPEN.**
