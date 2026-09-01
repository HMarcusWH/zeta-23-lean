# W1 post-green research settlement — zero-side evenization route

Status: **RESEARCH SETTLEMENT / RH OPEN**

This document records the post-green investigation after W1 merged. It is not theorem authority. Lean/compiler/CI, CLAIM_REGISTRY.json and exact declarations remain authoritative.

## Exact validated state

~~~text
repository = HMarcusWH/zeta-23-lean
main = 1a6a286cc4aae76ef6335b85b1022ec3998614df
tree = 1d49b9dc4fbee4054d18ce5059b40c2d7ccbc3cf
merged through = PR #81
PR #81 final validated head = 191e34ece05739122f362d097f9e4393cd5b9ce3
W1 theorem declaration head = 7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
date = 2026-09-01
RH = OPEN
~~~

The final PR #81 head passed the CCM build, ExceptionalZero build, no-placeholder gate, RHRC regression suite, source/normalization firewalls and independent Permansson verification.

Headline axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

## What became formally true

**PROVED**

For every concrete off-line zeta zero, Lean proves

~~~text
exists L > 0, r > 0, h,
  L = 4*r
  and ContDiff R 2 h
  and HasCompactSupport h
  and tsupport h ⊆ Ioo r (3*r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re (zetaZeroConfig.W h h) < 0.
~~~

Production theorem:

~~~text
Zeta23.ExceptionalZero.exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero
~~~

W2-A and W0 were already PROVED and registered.

## What changed

The route-general front end is closed.

**DERIVED**

Because `L=4r`,

~~~text
tsupport h ⊂ (L/4, 3L/4).
~~~

This is stronger geometry than the minimum `tsupport h ⊂ (0,L)`.

Under

~~~text
lambda = exp(L/2)
x = log(lambda*u),
~~~

the midpoint `x=L/2` maps to `u=1`, and the W1 collar maps algebraically to

~~~text
u ∈ (lambda^(-1/2), lambda^(1/2))
~~~

inside the full source aperture `(lambda^-1,lambda)`.

This source-coordinate collar is **DERIVED**, not separately theoremized.

## Upstream implications

### Stronger regularity may already be latent

**LEAD / HYPOTHESIS**

The X1 seed is built from Mathlib's normalized `ContDiffBump`, whose normalized bump supports arbitrary finite differentiability order. The current project interface exposes only C⁴ for the seed and C² after the second-order pole killer because that was the minimum needed.

Therefore the C² W0/W1 endpoint may be an interface truncation rather than an intrinsic limitation.

Do not theoremize extra regularity pre-emptively. Activate only if F0-B or a fallback weighted-integrability proof needs it.

### Do not generalize ZeroConfig prematurely

The shortcut below uses concrete-zeta Schwarz conjugation. Abstract `ZeroConfig` currently carries only the functional-equation reflection

~~~text
rho -> 1-conj(rho).
~~~

Do not add a stronger symmetry field to `ZeroConfig` merely to make one proof prettier unless a second route needs the abstraction.

## Downstream implications

The W1 post-green pass exposed a potentially smaller route through W2.

Current proved input:

~~~text
W2-A:
zetaZeroConfig.W f g
  = EF.literatureRHS (EF.weilTest f g)
~~~

with the necessary Wsummand Summable certificate.

For the diagonal define

~~~text
k = EF.weilTest h h.
~~~

The finite additive target is

~~~text
localizedWeilHalfTest h h
  = 1/2 * (k(y) + k(-y))
~~~

by definition.

If the zero-side symmetry package below closes, the project may prove

~~~text
literatureRHS(localizedWeilHalfTest h h)
  = literatureRHS(k)
~~~

without opening the pole/prime/gamma decomposition of `literatureRHS`.

Then W2-A gives the target

~~~text
zetaZeroConfig.W h h
  = CCM.localizedWeilAdditiveRHS h h.
~~~

If generic in C² compact support, W1 is not logically required for this identity; W1 remains essential for F0-B/source localization.

## New RH-relevant clue — W2-ZS

**LEAD / HYPOTHESIS**

Concrete zeta has unconditional Schwarz conjugation:

~~~text
riemannZeta_conj
analyticOrderAt_zeta_conj
~~~

and the project already has the functional-equation carrier reflection

~~~text
zetaZeroConfig.reflectEquiv :
  rho -> 1-conj(rho).
~~~

Compose conjugation with reflection:

~~~text
rho
  -> conj(rho)
  -> 1-conj(conj(rho))
  = 1-rho.
~~~

The resulting candidate involution should preserve the concrete carrier and multiplicity.

Algebraically:

~~~text
gammaOf(1-rho) = -gammaOf(rho).
~~~

This suggests reindexing the concrete `EF_lit` zero sum directly under `rho -> 1-rho`.

## Proposed next theorem package

Suggested file:

~~~text
Zeta23/ExceptionalZero/WeilZeroSideEvenization.lean
~~~

Suggested bounded sequence:

### ZS0 — conjugation carrier/multiplicity

~~~text
zeta_conj_mem
zeta_mult_conj
~~~

or equivalent exact declarations on `zetaZeroConfig.carrier`.

### ZS1 — one-sub equivalence

~~~text
zetaOneSubEquiv :
  zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier
~~~

with

~~~text
coe (zetaOneSubEquiv rho) = 1-rho
zetaZeroConfig.mult (zetaOneSubEquiv rho)
  = zetaZeroConfig.mult rho.
~~~

The map is self-inverse.

### ZS2 — spectral sign

~~~text
gammaOf (1-rho) = - gammaOf rho.
~~~

### ZS3 — reflected test

Define

~~~text
reflectTest k := fun x => k (-x).
~~~

Prove the exact Fourier convention:

~~~text
paperFT (reflectTest k) z = paperFT k (-z).
~~~

Also preserve C² and compact support.

### ZS4 — zero-sum reindex

Apply concrete `EF_lit` to `k` and `reflectTest k`.

Use

~~~text
Equiv.tsum_eq zetaOneSubEquiv
~~~

only after the relevant Summable certificates exist.

Target:

~~~text
sum zeroSummand(reflectTest k)
  = sum zeroSummand(k).
~~~

### ZS5 — half-evenization

Define

~~~text
halfEven k :=
  fun x => (1/2 : C) * (k x + k (-x)).
~~~

Apply `EF_lit` to `halfEven k`, not an assumed generic linearity theorem for `literatureRHS`.

Target:

~~~text
literatureRHS (halfEven k)
  = literatureRHS k.
~~~

### ZS6 — production diagonal bridge

Preferred target:

~~~text
theorem zeta_W_self_eq_localizedWeilAdditiveRHS
    {h : R -> C}
    (hh : ContDiff R 2 h)
    (hhc : HasCompactSupport h) :
    zetaZeroConfig.W h h
      = Zeta23.CCM.localizedWeilAdditiveRHS h h
~~~

if no extra assumptions are genuinely needed.

## Dumbassery / falsification checks

The shortcut must fail closed.

### Carrier check

Verify `conj(rho)` is an exact concrete nontrivial zero, not merely a zero of a completed function or an abstract symmetry assumption.

### Multiplicity check

Use `analyticOrderAt_zeta_conj`; do not assume multiplicity preservation from set membership.

### Involution check

`rho -> 1-rho` must be packaged as a genuine subtype equivalence with exact inverse law.

### gammaOf orientation check

Direct algebra must prove

~~~text
gammaOf(1-rho) = -gammaOf(rho).
~~~

A conjugated or sign-reversed variant kills the proposed reindex as stated.

### Fourier convention check

The project convention is

~~~text
paperFT f z = integral f(u) * exp(I*z*u) du.
~~~

Under `u -> -u`, reflection should produce `z -> -z`. Confirm there is no extra conjugation.

### Half-factor check

`localizedWeilHalfTest h h` must be exactly the half-evenization of `EF.weilTest h h`, with no argument-order or factor-two drift.

### Totalized tsum check

Never use a totalized `tsum` identity as if divergent sums were algebraic. Every add/smul/reindex step must be backed by the Summable evidence produced by `EF_lit` or a proved consequence.

### Circularity check

Schwarz reflection and the zeta functional equation are unconditional classical zeta facts already formalized in the repository. The route must not import RH, zero-on-line assumptions, or an RH-equivalent positivity statement.

### Scope check

If the proof is concrete-zeta-only, state it that way. Do not silently promote it to arbitrary `ZeroConfig`.

## Resurrected routes

### Gamma/mu route

**READY FALLBACK / OPEN**

The old I0/I1/I2 package remains valid:

~~~text
I0 pole-neutrality transfer
I1 mu/gamma reflection
I2 weighted gamma-channel integrability
~~~

It should be reactivated only if W2-ZS fails or if an independent analytic proof is desired.

### Source route

**ACTIVE PARALLEL / OPEN**

~~~text
S0 L <-> lambda
S1 d*u/L²/kappa/q/PsiSharp/QW
G1-B1B
G1-final
G23
~~~

W1's derived central collar around `u=1` may make source-domain cutoffs cleaner.

## Highest-leverage next moves

1. Implement only ZS0-ZS3 first.
2. If any exact convention fails, stop and classify the shortcut before building sum machinery.
3. If ZS0-ZS3 are clean, implement ZS4-ZS5 with explicit Summable evidence.
4. If ZS5 is green, prove the direct diagonal bridge ZS6.
5. Immediately perform another post-green pass.
6. If ZS6 is green, move the primary internal frontier to F0-B.
7. In parallel, keep the source S0/S1 premise audit alive.
8. Do not spend time on generic C∞ plumbing until F0-B identifies a required regularity order.

## Standing questions

Given everything now formally true, what became possible that was not possible before?

The strict W1 witness made the function-level obstruction compatible with a fixed finite aperture, while the post-green reread exposed enough concrete-zeta symmetry to attempt evenization on the summable zero side rather than the gamma integral.

If this contains a clue toward RH, where does it propagate?

~~~text
W2-ZS
  -> direct W/additive bridge
  -> F0-B
  -> G1-A [PROVED]
  -> F1
  -> K0-K3 finite-wall program.
~~~

What is the fastest test of whether the clue is real?

Prove or falsify ZS0-ZS3. They are small, exact and convention-sensitive. If those survive, the only remaining nontrivial shortcut risk is legal zero-sum reindexing.

RH remains **OPEN**.
