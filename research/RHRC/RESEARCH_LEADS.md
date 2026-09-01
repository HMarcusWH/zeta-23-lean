# RHRC living research leads ledger

> **Claim firewall: RH remains OPEN.**
>
> This file is the living research inventory. Lean/compiler/CI plus the machine registries remain theorem authority. Research status never upgrades formal status.

## Current review baseline

~~~text
main = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
merged through = PR #86
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
PR #86 merge = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
date = 2026-09-01
RH = OPEN
~~~

## Status vocabulary

Research: `ACTIVE`, `TESTING`, `READY`, `BLOCKED`, `DORMANT`, `PROMOTED`, `SUPERSEDED`, `REFUTED`, `QUARANTINED`.

Formal: `PROVED`, `DERIVED`, `LEAD / HYPOTHESIS`, `EXPERIMENTAL SIGNAL`, `OPEN`, `RH-EQUIVALENT`.

## A. Promoted internal front-end

### L-W2-01 — genuine W / literature-RHS pair bridge

**Research:** PROMOTED  
**Formal:** PROVED  
**Claim:** `R003_WEIL_PAIR_LITERATURE_BRIDGE`

PR #77 theorem-locks pairwise summability and `W(f,g)=literatureRHS(weilTest f g)` on the exact admissible class.

### L-W0-01 — one negative physical Weil test

**Research:** PROMOTED  
**Formal:** PROVED  
**Claim:** `R003_NEGATIVE_WEIL_TEST_CONTRACTION`

Every off-line concrete zeta zero yields one compact C² pole-neutral test with strictly negative genuine W self-value.

### L-W1-01 — strict aperture recentering

**Research:** PROMOTED  
**Formal:** PROVED  
**Claim:** `R003_STRICT_APERTURE_NEGATIVE_WEIL_TEST`

The negative test can be chosen with `L=4r` and `tsupport h subset Ioo r (3*r) subset Ioo 0 L`. This positive collar is now a primary approximation asset.

### L-W2-03 — concrete-zeta zero-side evenization

**Research:** PROMOTED  
**Formal:** PROVED  
**Claim:** `R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE`

For every compact C² test, genuine diagonal W equals the existing localized additive RHS. Old analytic W2-B remains DORMANT as an independent cross-check; proving the endpoint by W2-ZS did not prove the historical analytic route.

### L-W2-05 — strict-aperture negative localized-additive witness

**Research:** PROMOTED  
**Formal:** PROVED  
**Claim:** `R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS`

This is the theorem-backed F0 input.

## B. Finite-obstruction fork after PR #86

### L-F0B1-01 — boundary-flat finite Fourier route

**Research:** PROMOTED / PRIMARY ROUTE  
**Formal:** PARTIALLY PROVED

PR #86 proves F0-B1A:

~~~text
centered moments 0,1,2 = 0
  -> localizedFiniteVector is global C²
  -> genuine W = canonicalSourceMatrix quadratic form.
~~~

Claim: `R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION`.

The legal carrier is nontrivial. The remaining F0-B1 burden is projection + approximation + family-level W continuity. The previous question “can hard-window finite vectors be made legally C²?” is CLOSED.

### L-F0B1B-01 — exact three-mode boundary-flat projection

**Research:** ACTIVE / NEXT THEOREM  
**Formal:** OPEN

For `N>=1`, let

~~~text
m0 = M0(u)
m1 = M1(u)
m2 = M2(u).
~~~

Candidate correction on centered modes `-1,0,+1`:

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

Target:

~~~text
M0(c)=-m0
M1(c)=-m1
M2(c)=-m2
=> BoundaryFlatCoefficients N (u+c).
~~~

Desirable companion properties:

~~~text
project fixes boundary-flat inputs
project is idempotent
correction norm is explicitly controlled by |m0|,|m1|,|m2|.
~~~

**Falsifier:** repository centered-index bookkeeping must make the three selected coordinates exactly `-1,0,+1`; do not prove an abstract formula and silently assume coordinate positions.

**N=0 firewall:** the one-mode sector is degenerate.

### L-WCONT-01 — family-level continuity topology for W

**Research:** ACTIVE / LOAD-BEARING  
**Formal:** OPEN

Target a quantitative common-support theorem strong enough to preserve a fixed strict negative margin.

Existing reusable infrastructure:

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
~~~

These already provide the inverse-square summable zero weight and a compact-C² transform-decay mechanism. New hypothesis to test:

~~~text
common support envelope
+ uniform support radius
+ family-uniform second-derivative integral bound
+ suitable convergence
=> one zero-side majorant independent of N.
~~~

Permanent warning:

~~~text
per-N Summable != family-level dominated convergence.
~~~

Do not move strict negativity through a limit until the uniform constant is theorem-backed.

### L-F0B1C-01 — finite approximation matched to WCONT

**Research:** READY AFTER WCONT  
**Formal:** OPEN

Do not precommit to full uniform C² density. First learn what WCONT actually needs, then prove only that approximation theorem.

The W1 collar means the target is identically zero near the periodic endpoints, so endpoint matching should be exploited.

Pinned Mathlib has no ready Fejer theorem; “standard Fourier approximation” is not a proof plan.

### L-F0B2-01 — direct localized-additive continuity

**Research:** DORMANT / READY FALLBACK  
**Formal:** OPEN

This route remains mathematically legitimate, but PR #86 removes its main prior advantage: avoiding the hard problem of constructing legal global-C² finite vectors. Reactivate if F0-B1 projection/density/WCONT becomes disproportionately large.

### L-E3-01 — minimal finite moment / jet algebra

**Research:** ACTIVE SUPPORT FOR F0-B1B  
**Formal:** LEAD

Use only the codimension-three algebra needed by the projection. Do not resurrect the full historical Prony/reconstruction program without new leverage.

### L-BKILL-01 — fixed trigonometric boundary killer

**Research:** READY FALLBACK  
**Formal:** LEAD / HYPOTHESIS

The proved five-mode vector is the coefficient pattern for `(1-cos theta)^2`. Multiplying a finite trigonometric polynomial by the corresponding fixed factor should enforce endpoint flatness. Compare this construction against the three-mode projection only if projection behaves poorly in the selected W topology.

### L-W0-02 — strengthen witness regularity if demanded

**Research:** DORMANT / READY SUPPORT  
**Formal:** LEAD / HYPOTHESIS

The current C² witness may suffice. Do not spend a PR on C⁶ seed / C⁴ pole-killed plumbing unless WCONT or the selected density theorem genuinely requires it.

## C. New structural clue for the post-F1 stage

### L-KRYLOV-01 — boundary-flat moments versus displacement Krylov chain

**Research:** READY FOR POST-F1 INVESTIGATION  
**Formal:** LEAD / HYPOTHESIS

Boundary flatness gives, in coefficient notation,

~~~text
1^T u = 0
1^T D u = 0
1^T D^2 u = 0,
~~~

where `D=indexMatrix N`. The canonical matrix already obeys

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

If F1 later produces a negative canonical vector inside this three-moment kernel, the displacement defect may simplify along `u,Du,D²u`. No spectral or crossing consequence has yet been proved. Do not use this clue before F1 except as motivation for retaining the moment constraints in the eventual finite obstruction theorem.

## D. Source-faithful parallel route

### L-SGEOM-01 — exact L/lambda aperture geometry

**Research:** ACTIVE PARALLEL  
**Formal:** OPEN

Continue only the exact source geometry required by the ambient form route.

### L-G1B1B-01 — Haar/L²/kappa/q/PsiSharp/QW interface

**Research:** ACTIVE PARALLEL  
**Formal:** OPEN

G1-B1A finite source coordinate transport is already PROVED. Do not rebuild it.

### L-SNEG-01 — source negativity entry

**Research:** ACTIVE PARALLEL  
**Formal:** OPEN

OBS-015 remains binding: a source restriction theorem does not carry the internal W sign automatically. Need either an independent fixed-aperture negative-QW theorem or an exact sign-carrying composition.

### L-G23-01 — negative ambient source form to finite negative sector

**Research:** BLOCKED ON SOURCE INTERFACE + SIGN ENTRY  
**Formal:** OPEN

This remains the source-route alternative to internal F0-B.

## E. Dormant / quarantined warnings

- Old analytic W2-B: DORMANT independent cross-check, not proved by W2-ZS.
- R002 windowed visibility: OPEN and production-validity constrained; do not substitute it for the canonical CCM route.
- Universal odd-sector positivity: RH-strength territory; parity is a decomposition tool, not an assumed sign theorem.
- Fitted-tridiagonal spectral generator route: QUARANTINED where tested gaps collapse.
- Source interface without source sign: prohibited by OBS-015.

## Highest-leverage queue

~~~text
1. F0-B1B exact boundary-flat projection
2. WCONT family-level quantitative continuity
3. approximation theorem matched to WCONT
4. strict finite sign transfer
5. F1 canonical finite obstruction
6. post-F1 review / v2.0 / K0-K3
~~~

Parallel: S-GEOM / S-IFACE / G1-final / S-NEG / G23.

RH remains OPEN.
