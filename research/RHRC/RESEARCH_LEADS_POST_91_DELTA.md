# Research leads delta — post PR #91

**Date:** 2026-09-02  
**Authority:** merged main `bab94aed54298de6fc6676808a0b0e46c2db6046`  
**Claim firewall:** RH remains OPEN.

This is a delta against the accumulated living lead ledger. Historical lead files remain frozen.

## Promotions

### L-F0B1-01 / F0-B1C-A

**Previous:** ACTIVE CANDIDATE / OPEN  
**Now:** PARTIALLY PROMOTED

**PROVED:**

`Zeta23.CCM.exists_localizedFinite_uniform_C2_approx`

Strict-collar (C^2) functions admit centered finite localized Fourier approximants with uniform value/first-jet/second-jet control on one fixed aperture and exact left-endpoint anchoring.

The AddCircle/Finsupp/centered-coordinate construction is no longer a lead.

### L-WCONT-01

**Previous:** ACTIVE / OPEN topology gate  
**Now:** PROMOTED / PROVED by merged PR #89

The genuine zeta Weil form has a fixed-support quantitative bound and a summability-safe diagonal perturbation estimate. Per-approximant summability is no longer the load-bearing route.

## Current primary lead

### L-F0B1C-B-01 — quantitative projection stability

**Research status:** ACTIVE / HIGHEST PRIORITY  
**Formal status:** OPEN

Use #91 raw approximants and #88 exact projection.

Key **DERIVED** simplification:

[
q(0)=0Rightarrow M_0=0.
]

Therefore only (M_1,M_2) need quantitative control.

Derived endpoint formulas:

[
|M_1|=rac{L^{3/2}}{2pi}|q'(0)|,
qquad
|M_2|=rac{L^{5/2}}{4pi^2}|q''(0)|.
]

Derived correction targets:

[
int_0^L |c|
le
rac{L^2}{2pi}|q'(0)|
+
rac{L^3}{2pi^2}|q''(0)|,
]

[
int_0^L |c''|
le
2pi|q'(0)|+L|q''(0)|.
]

For #91 epsilon-approximants this suggests

[
int_0^L |p-h|
le
left(L+rac{L^2}{2pi}+rac{L^3}{2pi^2}ight)arepsilon
]

and

[
int_0^L |p''-h''|
le
(2L+2pi)arepsilon.
]

These inequalities are **DERIVED, not yet Lean theorems**.

## Superseded implementation leads

- Rebuilding generic Stone-Weierstrass for F0-B1C-A: SUPERSEDED.
- Fejer-first raw approximation: DORMANT FALLBACK.
- L2-only Fourier approximation: INSUFFICIENT for endpoint second-jet control.
- Independent family dominated-convergence theorem for W: SUPERSEDED by WCONT-A.

## Retained fallbacks

- boundary-killer multiplication;
- F0-B2 direct localized-additive continuity;
- older analytic W2-B route as an independent cross-check.

Their relative priority decreased because the main path is now theorem-backed through the raw approximation step.

## Parallel source lane

Unchanged.

OBS-015 remains binding: source interface is not source negativity.

S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain OPEN.

## New composition clue

**LEAD / HYPOTHESIS.**

The projected finite witness path preserves the three moment constraints

[
mathbf1^Tu=mathbf1^TDu=mathbf1^TD^2u=0.
]

Combined after F1 with the exact rank-two displacement identity, this may collapse parts of the Krylov/commutator algebra. Do not implement K0-K3 before F1.

## Next decision gate

Attempt F0-B1C-B directly.

If the explicit three-mode correction bounds close with fixed-(L), (N)-independent constants, proceed immediately to strict sign transfer.

If they fail because the global hard-window second derivative cannot be identified cleanly, repair that legal-function seam only; do not reopen Fourier approximation.

**RH remains OPEN.**
