# WCONT-A post-green settlement — F0-B1C approximation frontier

> **Claim firewall: RH remains OPEN.**
>
> This is the dated Post-Green Research Pass for PR #89. Live GitHub, exact Lean/compiler/CI and machine registries on the checked ref override this record if the repository later changes.

## Exact validated state

~~~text
merged main = 879eb6d356d8f62bbe0b9241596b15892498ea64
merged main tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
merged through = PR #88

PR #89 head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
base = 879eb6d356d8f62bbe0b9241596b15892498ea64
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
PR state at settlement time = OPEN / NOT MERGED
RH = OPEN
~~~

RHRC #619 passed the CCM build, ExceptionalZero build, no-placeholder gate, RHRC claim/regression suite, R003 normalization/source firewall, R004 scalar-shift audit and external-reference/oracle guards. Permansson #392 passed its independent Lean and placeholder/extra-axiom checks.

The promoted WCONT-A declarations print exactly:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No sorryAx survives.

A superseded earlier head failed only because Lean's `positivity` tactic did not automatically discharge two `Complex.normSq >= 0` side goals. The final head replaces those tactic calls by explicit `Complex.normSq_nonneg` proofs; theorem statements and mathematics are unchanged.

## What became formally true

### PROVED — global weighted paper Fourier estimate

For compactly supported C² `f` inside one support radius `Λ`,

~~~text
||paperFT f z|| * (1 + normSq z)
  <= exp(|Im z| Λ) *
     ( integral ||f|| + integral ||f''|| ).
~~~

Production declaration:

~~~text
Zeta23.norm_paperFT_mul_one_add_normSq_le
~~~

This bound is global in `z`. There is no exceptional `z=0` split.

### PROVED — fixed inverse-square zeta-zero mass

The concrete zeta weight

~~~text
mult(ρ) / (1 + normSq(gammaOf ρ))
~~~

is summable, and its tsum is packaged as

~~~text
Zeta23.ExceptionalZero.zetaInvSqZeroMass.
~~~

Production declaration:

~~~text
Zeta23.ExceptionalZero.zeta_invSqZeroWeight_summable
~~~

### PROVED — pointwise family-independent W majorant

For common support radius `Λ`, first leg C² and second leg continuous,

~~~text
||Wsummand(f,g,ρ)||
  <= exp(Λ)
     * (||f||_1 + ||f''||_1)
     * ||g||_1
     * mult(ρ)/(1+normSq(gammaOf ρ)).
~~~

Production declaration:

~~~text
Zeta23.ExceptionalZero.norm_zeta_Wsummand_le_commonSupport
~~~

The same fixed inverse-square zero weight dominates every admissible pair in the support envelope.

### PROVED — WCONT-A quantitative bilinear bound

~~~text
||W(f,g)||
  <= exp(Λ) * zetaInvSqZeroMass
     * (||f||_1 + ||f''||_1)
     * ||g||_1.
~~~

Production declaration:

~~~text
Zeta23.ExceptionalZero.zeta_W_norm_le_commonSupport
~~~

This is a static quantitative theorem. It does not infer a uniform majorant from per-approximant summability; it constructs one directly.

### PROVED — exact summability-safe cross-term identity

For compact C² `p,h`,

~~~text
W(p,p)-W(h,h)
  = W(p-h,p) + W(h,p-h).
~~~

Production declaration:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_sub_self_eq_cross
~~~

The proof obtains all required Summable certificates first and then transports subtraction/addition through `HasSum`.

### PROVED — diagonal perturbation estimate

For one common support radius,

~~~text
||W(p,p)-W(h,h)||
  <= exp(Λ) * zetaInvSqZeroMass *
     [ (||p-h||_1 + ||(p-h)''||_1) * ||p||_1
       + (||h||_1 + ||h''||_1) * ||p-h||_1 ].
~~~

Production declaration:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_sub_self_norm_le_commonSupport
~~~

## What changed

Before #89 the primary internal route still carried an unresolved family-level continuity problem:

~~~text
finite approximants
  -> ? one uniform zero-side majorant
  -> ? W(p_N,p_N) -> W(h,h).
~~~

That seam is now closed.

The exact approximation norm is no longer speculative. It is enough to make

~~~text
integral ||p_N-h|| -> 0
integral ||(p_N-h)''|| -> 0
~~~

inside one fixed support envelope. The second-leg factor only needs L¹ control.

Since

~~~text
||p_N||_1 <= ||h||_1 + ||p_N-h||_1,
~~~

no separate uniform L¹ bound on the approximants should be a load-bearing theorem if the first error already tends to zero.

The next obstruction is therefore **F0-B1C: construct legal boundary-flat finite approximants with exactly these two integral errors tending to zero.**

## Upstream implications

### DERIVED — WCONT topology is essentially W^{2,1}-type for the first leg

The theorem only sees

~~~text
E(f) = integral ||f|| + integral ||f''||.
~~~

No first-derivative integral enters WCONT-A.

Do not promote this to an abstract Sobolev-topology theorem unless useful; the concrete integral form is already sufficient.

### DERIVED — endpoint jets are now projection data, not W-continuity data

Value/first/second endpoint jets remain necessary because #88 converts them into M0/M1/M2 correction coordinates.

They are not independently required by WCONT-A.

This separation matters:

~~~text
W continuity:
  L1 error + second-derivative L1 error

projection legality/stability:
  endpoint value + first jet + second jet.
~~~

### DERIVED — the family dominated-convergence route is obsolete on the primary path

A generic sequence-level dominated-convergence theorem would now duplicate a stronger explicit quantitative estimate.

Keep such a theorem dormant unless a different route needs it.

## Downstream implications

The primary internal ladder can now be sharpened to:

~~~text
strict-collar negative h
  -> raw finite periodic approximation q
     with small interior function/second-derivative error
     and small endpoint jets
  -> #88 moments M0,M1,M2 small
  -> three fixed correction coefficients small
  -> p = boundaryFlatProject q
  -> p is globally C² and compact
  -> ||p-h||_1 + ||(p-h)''||_1 small
  -> W(p,p) close to W(h,h)
  -> strict negative finite p
  -> F0-B1A
  -> canonicalSourceMatrix negative quadratic vector
  -> F1.
~~~

The next theorem package should therefore focus on **approximation + projection stability**, not on any further Weil-form analysis.

## Resurrected routes

### Existing AddCircle Fourier span / second-derivative-first construction

**Status: LEAD / HIGHEST-PRIORITY INVESTIGATION.**

A deeper pinned-Mathlib inventory after WCONT-A found that `Mathlib/Analysis/Fourier/AddCircle.lean` already proves the route-specific density theorem:

~~~text
AddCircle.span_fourier_closure_eq_top
~~~

for the exact characters

~~~text
AddCircle.fourier n (x : AddCircle L)
  = exp(2*pi*i*n*x/L).
~~~

This phase agrees with `localizedMode L n`; the repository adds only `1/sqrt L`.

The same Mathlib file also provides:

~~~text
AddCircle.fourierCoeff_eq_intervalIntegral
AddCircle.fourierCoeffOn_eq_integral
AddCircle.fourierCoeffOn_of_hasDerivAt
AddCircle.hasDerivAt_fourier
~~~

So the project does not need to rebuild Stone-Weierstrass or Fejer merely to obtain uniform finite trigonometric approximation.

Preferred experiment:

1. descend the strict-collar witness to a C² periodic object;
2. uniformly approximate h'' by an element of the finite Fourier span;
3. prove mean(h'')=0 from h'(L)=h'(0), and subtract the approximant's constant mode;
4. integrate nonzero modes twice using frequency `2*pi*i*n/L`;
5. choose the constant mode to match mean(h);
6. use fixed-L periodic integration estimates to control q'-h' and q-h;
7. use uniform h'' approximation to control q''(0), while the lower-jet bounds control q'(0),q(0);
8. feed those residuals through #88.

The theorem `AddCircle.hasSum_fourier_series_L2` was also found, but L² convergence alone is insufficient for the primary projector route because point evaluation q''(0) is not L²-continuous.

The earlier generic Stone-Weierstrass packaging lead is therefore superseded.

### F0-B2 direct localized-additive continuity

**Status: DORMANT / READY FALLBACK.**

#89 removes the principal reason to reopen it. The genuine-W route now has an explicit quantitative modulus.

### Boundary-killer multiplication

**Status: READY FALLBACK.**

Still useful if the three-mode projection correction becomes formally more expensive than expected. Projection remains primary.

### Witness regularity strengthening

**Status: DORMANT.**

WCONT-A accepted the existing C² witness exactly. C⁴/C⁶ strengthening is unnecessary on the current route.

## New RH-relevant clues

### LEAD / HYPOTHESIS — off-line zero now forces an approximation problem with finite codimension only

Combining W0/W1, #86, #88 and #89, the remaining primary obstruction between an off-line zero and F1 is no longer an analytic zero-sum convergence issue. It is a finite-codimension approximation problem: approximate one strict-collar C² function while enforcing three endpoint/moment constraints.

That is materially narrower than the pre-#88/pre-#89 route.

### LEAD / HYPOTHESIS — second-derivative-first approximation may be canonical

Because WCONT-A ignores the first derivative and #88 uses the first derivative only at one endpoint, a construction driven by uniform approximation of `h''` may simultaneously supply:

- the needed second-derivative L¹ control;
- first-jet control by integration;
- function control after fixing the mean;
- endpoint residual control.

If this works, the approximation package may collapse to one density theorem plus elementary periodic integration estimates.

### LEAD / HYPOTHESIS — F1 should retain the codimension-three moment kernel

Any primary-route finite negative vector should still satisfy

~~~text
1^T u = 1^T D u = 1^T D² u = 0.
~~~

That structure should be preserved into the post-F1 displacement/Krylov investigation rather than discarded by a weaker existential theorem.

## Falsification checks

1. **Merge status:** #89 is green but remains open/unmerged at settlement time. Permanent main is still #88.
2. **No RH:** WCONT-A is support infrastructure only.
3. **Support envelope:** the theorem requires one fixed `Λ`; future approximation must not let support radius grow with N.
4. **Raw approximants:** an unprojected hard-window trigonometric polynomial need not be globally C².
5. **Correction alone:** the three-mode correction is not generally boundary-flat and cannot be treated as an independent admissible W test.
6. **Derivative decomposition:** future proofs must justify how interior trigonometric derivatives control the classical derivative of the complete projected hard-window function; endpoint sets are measure-zero but the global C² legal object must be the projected vector.
7. **AddCircle finite-span extraction:** the density theorem is already available, but it still does not by itself produce the exact repository centered coefficient vector, zero-mean second derivative, or twice-integrated coefficient map.
8. **Mean mode:** solving `q''=r` in a periodic finite Fourier sector requires zero mean for `r`; this must be enforced explicitly.
9. **Poincare constants:** any lower-jet recovery must have constants depending only on fixed L, not N.
10. **Strict sign:** convergence must be quantitative enough to beat the actual negative margin of the W1 witness; do not replace this with mere nonpositivity.
11. **Source firewall:** OBS-015 remains binding.
12. **Normalization:** canonicalSourceMatrix remains distinct from legacy finiteMatrix.

## Highest-leverage next moves

1. Finish #89 Stage-B registry/documentation promotion on the exact green head.
2. Merge #89 when desired and verify permanent main SHA/tree.
3. Before coding F0-B1C, prototype the `AddCircle.span_fourier_closure_eq_top` extraction/integration-back bridge against the exact localized finite basis.
4. If that route is formally economical, theorem-lock only the minimal periodic approximation package it requires.
5. Prove explicit three-mode correction coefficient and interior derivative bounds.
6. Combine those bounds with WCONT-A to obtain one strict-negative legal finite vector.
7. Cash out immediately through F0-B1A into strengthened F1.
8. Perform a full Post-Green Research Pass at F1 before K0-K3.

## Standing questions

**Given everything that is now formally true, what becomes possible that was not possible before?**

The project can now replace the vague family-level continuity problem by a concrete finite approximation target measured in two explicit integrals, with all zero-side summability already discharged.

**If this contains a clue toward RH, where does that clue propagate?**

It propagates into a codimension-three finite approximation/sign-transfer problem and then, if F1 closes, into the constrained finite displacement/Krylov sector.

**What experiment, lemma or reformulation most efficiently tests whether that clue is real?**

Test whether uniform approximation of the periodic second derivative, plus mean calibration, can produce centered finite coefficients with the required endpoint jets and W^{2,1}-type error. If yes, the remaining path to F1 may be substantially shorter than the old Fejer/dominated-convergence design.

RH remains OPEN.
