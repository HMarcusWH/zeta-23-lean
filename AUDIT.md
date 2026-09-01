# HMWH Zeta23 fork — current audit entry point

> **Claim firewall: RH remains OPEN.**

## Authority snapshot

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
RH = OPEN
~~~

### Exact #91 validation

~~~text
PR #91 final head = cf1c9b6536264deb8773fa8b0bb3650b07fcff40
head tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merge = bab94aed54298de6fc6676808a0b0e46c2db6046
RHRC #660 = SUCCESS
Permansson #433 = SUCCESS
~~~

Final head tree and merge tree are identical.

RHRC #660 passed:

- Lean action;
- Build CCM formalization;
- Build exceptional-zero foundation;
- reject forbidden placeholders;
- RHRC claim/regression suite;
- cutoff-free normalization lock;
- finite dictionary external-oracle guards;
- source-normalization semantic firewall;
- R004 scalar-shift audit;
- external-reference dependency rejection.

Permansson #433 passed its formal theorem build and placeholder/extra-axiom rejection.

The final ClaimBindings audit prints only

~~~text
[propext, Classical.choice, Quot.sound]
~~~

for exists_localizedFinite_uniform_C2_approx and the load-bearing bridge lemmas. No sorryAx survives.

## Permanent recent merge provenance

### PR #88 — F0-B1B

~~~text
head = fe5fe1c75668e1265482db3119d256997e31f32a
merge = 879eb6d356d8f62bbe0b9241596b15892498ea64
tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
RHRC #617 = SUCCESS
Permansson #390 = SUCCESS
~~~

### PR #89 — WCONT-A

~~~text
head = 8680b379e695278d1688b02f3f01b075620c4b07
merge = f6e79fcf7b4daac7ed29bd90f24321229a9addd1
tree = fd97e0c5704b4071cd0b6388d6281c14310cfa63
RHRC #636 = SUCCESS
Permansson #409 = SUCCESS
~~~

### PR #91 — F0-B1C-A

~~~text
head = cf1c9b6536264deb8773fa8b0bb3650b07fcff40
merge = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
RHRC #660 = SUCCESS
Permansson #433 = SUCCESS
~~~

## Formal theorem state

~~~text
W2-A pair bridge                                  PROVED
W0 compact C² negative W witness                  PROVED
W1 strict-aperture collar                         PROVED
W2-ZS / direct diagonal W bridge                  PROVED
strict negative localized-additive witness        PROVED
G1-A finite additive restriction                  PROVED
F0-B1A legal boundary-flat finite carrier         PROVED
F0-B1B exact boundary-flat projection             PROVED / MERGED
WCONT-A fixed-support genuine-W bound             PROVED / MERGED
F0-B1C-A raw uniform localized C² approximation   PROVED / MERGED

F0-B1C-B quantitative projection stability        OPEN / NOW
strict finite sign transfer                       OPEN
F1 canonical finite negative obstruction          OPEN
K0-K3                                             OPEN
RH                                                OPEN
~~~

## #91 production theorem

Zeta23.CCM.exists_localizedFinite_uniform_C2_approx

For every positive aperture and every strict-collar complex C² target, finite centered localized Fourier functions approximate value, first jet and second jet uniformly on the closed aperture, with left endpoint value anchored exactly to zero.

This closes the raw Fourier approximation bridge.

## Extra post-green consequence

**DERIVED / not separately formalized.**

#91 + #88 gives M0=0 exactly for the raw approximants. Therefore the correction reduces to the M1,M2 residuals.

The exact endpoint identities imply

|M1| = L^(3/2)/(2*pi) * |q'(0)|,

|M2| = L^(5/2)/(4*pi^2) * |q''(0)|.

The expected fixed-L, N-independent correction estimates are

integral_0^L |c|
  <= L^2/(2*pi) * |q'(0)|
   + L^3/(2*pi^2) * |q''(0)|,

and

integral_0^L |c''|
  <= 2*pi*|q'(0)| + L*|q''(0)|.

These are the next formalization target, not yet production claims.

## Current open frontier

F0-B1C-B must convert #91's raw formula-level approximation into a legal boundary-flat hard-window approximation in the exact WCONT topology.

Do not apply W to the raw hard-window approximant.

After F0-B1C-B:

~~~text
W1 strict negative margin
+ WCONT-A
+ legal finite approximation
  -> strict finite negative W
  -> F0-B1A
  -> F1 canonical finite negative obstruction.
~~~

## Permanent firewalls

1. RH remains OPEN.
2. Source interface is not source negativity (OBS-015).
3. Raw periodic finite approximation is not hard-window legality (OBS-016).
4. The correction alone is not an admissible hard-window C² test.
5. Per-member zero-side summability is not family domination; WCONT-A is the accepted replacement.
6. canonicalSourceMatrix is the sign-authoritative finite source object; finiteMatrix is the legacy printed normalization.

## Current post-green settlement

research/RHRC/routes/R003_ccm_bridge/F0_B1C_A_POST_GREEN_PROJECTION_STABILITY_FRONTIER_2026_09_02.md

**RH remains OPEN.**
