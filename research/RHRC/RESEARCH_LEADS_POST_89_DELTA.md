# RHRC research leads — post-PR #89 delta

> **Claim firewall: RH remains OPEN.**
>
> This file supplements the historical research-lead ledger. It records only state changes caused by the exact green WCONT-A theorem head. Earlier delta files remain frozen.

## Validation snapshot

~~~text
merged main = 879eb6d356d8f62bbe0b9241596b15892498ea64
merged through = PR #88

PR #89 head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
PR state at documentation time = OPEN / NOT MERGED

RH = OPEN
~~~

## L-WCONT-01 — common-support genuine-W bound

**Research status:** PROMOTED ON GREEN THEOREM HEAD  
**Formal status:** PROVED on exact #89 head; pending permanent merge

Production theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_norm_le_commonSupport
~~~

For fixed support radius `Λ`,

~~~text
||W(f,g)||
  <= exp(Λ) * zetaInvSqZeroMass
     * (||f||_1 + ||f''||_1)
     * ||g||_1.
~~~

The majorant is family-independent and uses the proved inverse-square zeta-zero mass.

## L-WCONT-XTERM-01 — diagonal continuity by cross terms

**Research status:** PROMOTED ON GREEN THEOREM HEAD  
**Formal status:** PROVED on exact #89 head

Production declarations:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_sub_self_eq_cross
Zeta23.ExceptionalZero.zeta_W_self_sub_self_norm_le_commonSupport
~~~

The previous lead is no longer speculative. The exact cross-term identity and quantitative diagonal perturbation estimate are theorem-backed with summability handled before `tsum` algebra.

## L-F0B1C-01 — WCONT-matched legal finite approximation

**Research status:** ACTIVE / LOAD-BEARING / NEXT  
**Formal status:** OPEN

Target only the exact data now demanded by #88 + #89:

~~~text
strict-collar compact C² h

-> boundary-flat finite p_N
   with one fixed support envelope
   integral ||p_N-h|| -> 0
   integral ||(p_N-h)''|| -> 0.
~~~

A convenient construction may pass through raw periodic finite q_N plus endpoint value/first/second jet control and the #88 projector.

Do not build a generic Sobolev/Fourier density library unless this minimal theorem genuinely requires it.

## L-APPROX-ADDCIRCLE-01 — direct AddCircle Fourier-span approximation

**Research status:** NEW / HIGHEST-PRIORITY LEAD  
**Formal status:** LEAD / HYPOTHESIS

Pinned Mathlib already proves the exact density statement needed on the periodic circle:

~~~text
AddCircle.span_fourier_closure_eq_top
~~~

with characters

~~~text
AddCircle.fourier n (x : AddCircle L)
  = exp(2*pi*i*n*x/L).
~~~

These match the repository `localizedMode L n` phase/sign exactly, up to the fixed `1/sqrt L` normalization.

The same file supplies:

~~~text
AddCircle.fourierCoeff_eq_intervalIntegral
AddCircle.fourierCoeffOn_eq_integral
AddCircle.fourierCoeffOn_of_hasDerivAt
AddCircle.hasDerivAt_fourier
~~~

Preferred experiment:

~~~text
strict-collar C² h
-> periodic h''
-> uniform finite Fourier-span r approx h''
-> subtract mean(r), using mean(h'')=0
-> integrate every nonzero mode twice
-> choose q constant mode to match mean(h)
-> fixed-L integration estimates recover q',q
-> q(0),q'(0),q''(0) -> 0
-> #88 projector
-> WCONT-A.
~~~

This **supersedes the generic Stone-Weierstrass packaging lead**: Mathlib has already performed that density proof for the exact Fourier span.

Fast falsifiers:

- finite-span membership is hard to extract into explicit centered coefficients;
- mean-mode removal/integration-back causes large coercion or normalization friction;
- periodic integration estimates dominate the proof;
- the resulting coefficient map does not align cheaply with `localizedFiniteFunction`.

Important negative result from the implication pass:

~~~text
AddCircle.hasSum_fourier_series_L2
~~~

is not by itself sufficient, because #88 needs q''(0) small and point evaluation is not L²-continuous. L² convergence remains supporting infrastructure, not the primary endpoint argument.

## L-APPROX-SW-01 — generic Stone-Weierstrass packaging

**Research status:** SUPERSEDED / DORMANT  
**Formal status:** LEAD / HYPOTHESIS

Do not rebuild a separating star subalgebra: `AddCircle.span_fourier_closure_eq_top` already gives the theorem required by the primary experiment.

## L-F0B1C-CORR-01 — quantitative three-mode correction bounds

**Research status:** ACTIVE SUPPORT  
**Formal status:** OPEN

The exact coefficients are already theorem-backed:

~~~text
c_-1 = (M1-M2)/2
c_0  = M2-M0
c_1  = -(M1+M2)/2.
~~~

Next prove explicit norm bounds and fixed-L interior function/second-derivative bounds for the correction.

Keep the firewall: the correction by itself is not generally a globally C² hard-window test.

## L-FEJER-01 — direct Fejer construction

**Research status:** DORMANT / READY FALLBACK  
**Formal status:** OPEN

Pinned Mathlib has no need for a Fejer theorem on the preferred route because `AddCircle.span_fourier_closure_eq_top` already supplies uniform finite Fourier-span density. Build Fejer only if extraction/integration-back through that theorem is worse in Lean.

## L-BKILL-01 — boundary-killer multiplication

**Research status:** READY FALLBACK  
**Formal status:** LEAD / HYPOTHESIS

Retain the five-mode boundary-killer architecture if projector stability becomes awkward.

## L-F0B2-01 — direct localized-additive continuity

**Research status:** DORMANT / LOW PRIORITY  
**Formal status:** OPEN

WCONT-A has now removed the main reason to prefer this route.

## L-KRYLOV-01 — moment kernel versus displacement

**Research status:** READY FOR POST-F1  
**Formal status:** LEAD / HYPOTHESIS

Preserve the future F1 witness in the codimension-three kernel

~~~text
1^T u = 1^T D u = 1^T D²u = 0
~~~

for comparison with

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

## Updated priority

~~~text
1. F0-B1C minimal legal finite approximation
2. quantitative three-mode correction bounds
3. strict finite sign transfer
4. strengthened boundary-flat F1
5. full post-F1 review
6. only then K0-K3
~~~

Parallel source work remains separate under OBS-015.

RH remains OPEN.
