# F0-B1A post-green settlement — projection / continuity frontier

> **Claim firewall: RH remains OPEN.**
>
> This is a dated post-green settlement for PR #86. Live GitHub, Lean/compiler/CI and the machine registries override this record if the repository later changes.

## Exact validated state

~~~text
PR #86 theorem head = e44cc5b8539b24fa24066c98c7ff013fb83b1001
PR #86 synthetic merge = a687d8142513b163b9755a18ddf9612901484cac
PR #86 permanent merge = 6d5eb5b5673b6754dda4926c41a60a5b85626a44
merged tree = a633de6504b0e2105d3e3f33b2f1728c1219dad5
RHRC #605 = SUCCESS
Permansson #378 = SUCCESS
RH = OPEN
~~~

The exact #86 head passed the CCM build, ExceptionalZero build, no-placeholder/no-project-axiom gate, RHRC regression/lint suite, R003 normalization/source firewall, R004 scalar-shift audit, external-oracle guard, and independent Permansson verification. The permanent merge tree is the theorem state promoted here.

## What became formally true

**PROVED — boundary-flat finite C² carrier.**

For `L>0`, finite `N`, and arbitrary complex centered coefficients `u`, the condition

~~~text
centeredMoment N 0 u = 0
centeredMoment N 1 u = 0
centeredMoment N 2 u = 0
~~~

implies

~~~text
ContDiff R 2 (localizedFiniteVector L N u).
~~~

Production theorem:

~~~text
Zeta23.CCM.contDiff_localizedFiniteVector_of_boundaryFlat
~~~

**PROVED — the carrier is nontrivial.**

The five-mode coefficients

~~~text
[1/4, -1, 3/2, -1, 1/4]
~~~

on centered modes `-2,-1,0,1,2` satisfy the three moment constraints and are nonzero. These are the coefficients of `(1-cos theta)^2`.

Supporting theorems:

~~~text
Zeta23.CCM.boundaryKillerCoefficients_boundaryFlat
Zeta23.CCM.boundaryKillerCoefficients_ne_zero
~~~

**PROVED — genuine zeta W is the canonical finite quadratic form on this carrier.**

For every boundary-flat finite vector:

~~~text
zetaZeroConfig.W(v,v)
  = localizedWeilAdditiveRHS(v,v)
  = quadraticForm(canonicalSourceMatrix L N) u.
~~~

Production theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm
~~~

Companion cutoff-free theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_boundaryFlatFiniteVector_eq_cutoffFreeQuadraticForm
~~~

Production axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No `sorryAx` or project-specific axiom survived the final validation gates.

## What changed

Before PR #86, F0-B1 and F0-B2 were retained as co-primary bounded candidates because it was not known whether the existing hard-window finite Fourier sector admitted a clean global-C² legal subspace. PR #86 removes that uncertainty.

The shortest internal path is now:

~~~text
off-line zero
  -> W0/W1 strict-collar negative test                 [PROVED]
  -> W2-ZS / direct diagonal W bridge                  [PROVED]
  -> strict negative localized-additive witness        [PROVED]
  -> exact boundary-flat projection                    [F0-B1B OPEN]
  -> approximation in a W-controlling topology         [OPEN]
  -> W continuity / strict-sign transfer               [OPEN]
  -> #86 finite W = canonical finite quadratic form    [PROVED]
  -> F1 canonical finite negative obstruction          [OPEN]
~~~

F0-B1 is therefore the primary internal route. F0-B2 direct localized-additive continuity remains a fallback if projection/density/W-continuity becomes larger than the source or additive alternatives.

## Upstream implications

The next canonical abstraction is an exact projection onto the three-moment kernel, not another special legal vector.

For `N>=1`, write

~~~text
m0 = centeredMoment N 0 u
m1 = centeredMoment N 1 u
m2 = centeredMoment N 2 u.
~~~

A correction supported on the centered modes `-1,0,+1` can be chosen as

~~~text
c_-1 = (m1 - m2)/2
c_0  = m2 - m0
c_+1 = -(m1 + m2)/2.
~~~

Then algebraically

~~~text
M0(c) = -m0
M1(c) = -m1
M2(c) = -m2,
~~~

so `P(u)=u+c` is boundary-flat. This is a **LEAD / next theorem target**, not yet proved in Lean.

The `N=0` sector is genuinely degenerate and must not be hidden; the projection theorem should explicitly require `1 <= N` or an equivalent availability hypothesis for the modes `-1,0,+1`.

## Downstream implications

Once a finite approximant lies in the boundary-flat sector, no further functional-identification theorem is needed: PR #86 already identifies its genuine zeta W self-value with the canonical finite CCM quadratic form.

Therefore the remaining internal burden is approximation plus continuity, not source normalization or finite-matrix identification.

The repository already contains a useful zero-side summability resource:

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
~~~

These theoremize the inverse-square summable zero weight used to dominate compact-C² Fourier transforms. This suggests that a common-support family with one uniform second-derivative control may yield the needed family-level W majorant. That implication remains **OPEN** until stated and proved quantitatively.

## Resurrected routes

**E3 minimal moment/jet algebra — RESURRECTED / ACTIVE SUPPORT.**

Only the codimension-three projection algebra is justified by the new state. The larger historical Prony/reconstruction program remains unnecessary.

**Fixed boundary-killer multiplication — READY FALLBACK / LEAD.**

The explicit `(1-cos(2*pi*x/L))^2` factor automatically supplies high-order endpoint zeros and may be useful if the three-mode correction interacts badly with the eventual topology. Do not prefer it without a theorem-surface comparison.

**Witness-regularity strengthening — LOWER PRIORITY.**

The current C² witness may already suffice. Do not theoremize C⁶/C⁴ plumbing unless WCONT or the selected approximation theorem actually demands it.

## New RH-relevant clues

**LEAD / HYPOTHESIS — boundary-flat negativity lives in a constrained Krylov geometry.**

The three moments correspond to

~~~text
1^T u   = 0
1^T D u = 0
1^T D^2 u = 0
~~~

for the centered index diagonal `D`. The canonical displacement theorem already proves

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

If F0-B/F1 later produces a negative canonical vector inside the three-moment kernel, the rank-two displacement defect is invisible against the all-ones channel along the first few vectors of the `u, D u, D^2 u` chain. This may strengthen the later K0-K3 rigidity analysis. It is not yet a proved spectral consequence.

## Falsification checks

1. Exact projection algebra must be proved with the repository `centeredIndex` convention, not informal integer coordinates.
2. `N=0` must be handled explicitly.
3. Exact correction is not enough: the correction must tend to zero in the topology ultimately used for W continuity.
4. Weak `L²` or uniform convergence alone must not be assumed sufficient for the gamma/log-weighted channel.
5. Per-approximant `Summable` does not imply a uniform family majorant.
6. The existing inverse-square zero weight is useful only if one theorem supplies a family-level constant independent of the approximant index.
7. Do not infer source `QW_lambda` negativity from the internal W/canonical-matrix identity; OBS-015 remains active.

## Highest-leverage next moves

1. **F0-B1B:** theorem-lock the exact three-mode boundary-flat projection, including idempotence/fixed-point behavior and quantitative correction bounds if cheap.
2. **WCONT:** determine and prove the weakest common-support topology that carries W and preserves a fixed negative margin; first test reuse of the existing inverse-square zero majorant.
3. Build finite Fourier approximation in exactly that topology; do not formalize a larger Fejer/Cesaro library unless required.
4. Compose approximation + projection + W continuity with the strict negative W1/#83 witness.
5. Cash out immediately through the #86 canonical finite identity to obtain F1 if the remaining composition is small.
6. Only after green F1 perform the next major post-green review and begin K0-K3.

## Standing questions

**Given everything now formally true, what becomes possible that was not possible before?**

A finite approximation can now be forced into an explicit theorem-backed legal carrier on which genuine zeta W is already the canonical matrix quadratic form.

**If this contains a clue toward RH, where does it propagate?**

It propagates forward into F0-B/F1 and potentially later into the displacement/Krylov rigidity stage through the three annihilated moment channels.

**What experiment or lemma most efficiently tells us whether the clue is real?**

The exact three-mode projection theorem followed by a quantitative W-continuity estimate. If either becomes unexpectedly large or false, F0-B2/source G23 remains available.

RH remains OPEN.
