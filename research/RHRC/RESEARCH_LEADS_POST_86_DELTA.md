# RHRC research leads — post-PR #86 delta

> **Claim firewall: RH remains OPEN.**
>
> This file supplements the full historical `RESEARCH_LEADS.md` ledger without deleting its accumulated lead inventory. It records only state changes caused by merged PR #86. The full ledger remains the history-bearing inventory; this delta is authoritative for the changed entries until the next full consolidation.

## Validation baseline

~~~text
main = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
RHRC #605 = SUCCESS
Permansson #378 = SUCCESS
RH = OPEN
~~~

## L-F0B1-01 — boundary-flat finite Fourier approximation

**Research status:** PRIMARY / PARTIALLY PROMOTED  
**Formal status:** F0-B1A PROVED; remaining approximation/continuity OPEN

PR #86 closes the carrier-leg uncertainty:

~~~text
centered moments 0,1,2 = 0
  -> hard-window localized vector is global C²
  -> genuine W = canonicalSourceMatrix quadratic form.
~~~

Registered production claim: `R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION`.

The carrier is nontrivial. F0-B1 is now the primary internal path.

## L-F0B1B-01 — exact three-mode boundary-flat projection

**Research status:** ACTIVE / NEXT THEOREM  
**Formal status:** OPEN

For `N>=1`, with `m0,m1,m2` the centered moments of `u`, test the correction on modes `-1,0,+1`:

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

Target: moments 0,1,2 of `u+c` vanish exactly. Also seek fixed-point/idempotent behavior and quantitative correction bounds if cheap.

Falsifier: exact repository `centeredIndex` coordinate bookkeeping; `N=0` is genuinely degenerate.

## L-WCONT-01 — family-level W continuity

**Research status:** ACTIVE / LOAD-BEARING  
**Formal status:** OPEN

New leverage after #86: `zero_sum_inv_sq_gen` and `EF_zero_sum_summable_gen` already supply the inverse-square zero weight and compact-C² transform-decay machinery. Test whether common support plus a family-uniform second-derivative integral bound yields one approximant-independent zero-side majorant.

Permanent warning:

~~~text
per-N Summable != uniform dominated convergence.
~~~

## L-F0B2-01 — direct localized-additive continuity

**Research status:** DORMANT / READY FALLBACK  
**Formal status:** OPEN

PR #86 removes this route's main former advantage: bypassing the construction of legal global-C² finite vectors. Reactivate if projection/density/WCONT grows disproportionately large.

## L-E3-01 — minimal finite moment / jet algebra

**Research status:** ACTIVE SUPPORT FOR F0-B1B  
**Formal status:** LEAD

Use only the exact three-moment projection algebra. Do not resurrect the full historical Prony/reconstruction program without additional leverage.

## L-BKILL-01 — fixed boundary-killer multiplication

**Research status:** READY FALLBACK  
**Formal status:** LEAD / HYPOTHESIS

The proved five-mode vector is the coefficient pattern of `(1-cos theta)^2`. A fixed trigonometric boundary-killer factor may give another legal approximation mechanism if the projection correction behaves badly in the selected W topology.

## L-W0-02 — witness regularity strengthening

**Research status:** DORMANT / READY SUPPORT  
**Formal status:** LEAD / HYPOTHESIS

The current C² witness may suffice. Activate stronger seed/pole-killed regularity only if WCONT or the eventual finite approximation theorem requires it.

## L-KRYLOV-01 — three-moment kernel versus displacement

**Research status:** READY FOR POST-F1 INVESTIGATION  
**Formal status:** LEAD / HYPOTHESIS

Boundary-flat coefficients imply

~~~text
1^T u = 0
1^T D u = 0
1^T D²u = 0,
~~~

while the canonical matrix obeys

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

A future F1 negative vector retaining the three moment constraints may simplify the post-F1 displacement/Krylov rigidity analysis. No spectral or crossing consequence is currently proved.

## Updated priority

~~~text
1. F0-B1B exact projection
2. WCONT quantitative family theorem
3. approximation matched to WCONT
4. strict finite sign transfer
5. F1
6. post-F1 review / v2.0 / K0-K3
~~~

Parallel source route remains `S-GEOM / S-IFACE / G1-final / S-NEG / G23` under OBS-015.

RH remains OPEN.
