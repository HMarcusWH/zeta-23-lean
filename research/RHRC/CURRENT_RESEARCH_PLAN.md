# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after documentation PR #132 = 38f65ce4abf5eec258d51425e7c9c88b63b21ffb
live main tree = 1cc939300fb269f798d25dc88f8eaff4eccc181a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
theorem-bearing merged through = PR #131
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative over prose. PR #132 changed documentation/control metadata only; it did not add a Lean theorem or expand theorem authority beyond #131.

## One-screen frontier

```text
DONE
  W0/W1/W2-ZS + finite legal approximation
  F1 canonical finite negative obstruction
  constrained algebra / Hermitianity / Euclidean sector
  exact centered N-flow + fixed-L negative tail
  exact reversal symmetry + direct parity decomposition + algebraic D-equivalence
  least/global first bad + predecessor nonnegative
  negative first-bad eigenmode + parity normals + KKT
  rank-at-most-one cubic parity defect
  intrinsic W/S block, dim_C S=1, exact cubic factorization
  canonical V=W⊕S coordinates
  safe shifted predecessor resolvent + exact Schur/secular machinery
  zero-shift kernel/range dichotomy + canonical endpoint
  Re S0<0 at the forced negative root
  canonical zero-shift shell response
  regular Re sigma0<0 + canonical resonant kernel pole
  exact cross-parity secular transfer
  cubic defect = canonical quadratic source moment
  off-line zero -> source-explicit global first-bad certificate
  exact canonical source-moment decomposition / #131

POST-#132 RESEARCH AUDIT — NOT YET LEAN THEOREMS
  denominator-free zero-shift kernel/source transport identified
  direct zero-shift cross-parity transfer identified
  exact rational generic countermodels falsify factorwise sign/nonzero shortcuts
  scalar-shift covariance shows the structural transfer package cannot locate the absolute spectral origin
  high-precision canonical checks show source moment and alpha can change sign
  source-coordinate Taylor algebra suggests boundary-flat cancellations at orders omega^7 / omega^9

NOW — E4-A4b0: KERNEL/SOURCE TRANSPORT
  theoremize, for z in ker A+,
    A-(Dz) = beta(z) d + mu(z) a
    <b-,Dz>/rho- = beta(z) + mu(z)
  derive the full odd-kernel vector compatibility
    (||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0
  derive, under both regular couplings,
    Gamma0 * mu(z) = 0  for every z in ker A+
  theoremize the direct zero-shift transfer without pseudoinverse/Laurent limits
    sigma- = alpha0 sigma+ + Gamma0 * explicitCanonicalSourceMoment(u+0)
  preserve preimage-dependence warnings for alpha0/Gamma0

THEN — E4-A4b1: ABSOLUTE CANONICAL SOURCE ENERGY
  restore the source information deliberately annihilated by the #131 normal moment
  decompose
    Re<Tv,v>
  into pole, reduced arch diagonal/off-diagonal, arch scalar correction, and finite prime-atom energies
  keep the scalar identity normalization term
  identify the regular zero-shift value with S0

THEN — E4-A4b2: CANONICAL ONE-STEP DOMINATION
  for each parity, with predecessor A>=0, shell c and b=P_W T c, prove from the actual canonical source
    q_c = Re<Tc,c> >= 0
    |<w,b>|^2 <= q_c * Re<Aw,w>  for every w in W
  this is the decisive arithmetic/coercive target, not an assumed helper

  if proved:
    w in ker A -> <w,b>=0 -> resonance removed
    Ax0=b -> S0=q_c-<b,x0> >= 0
    existing first-bad theorem gives Re S0<0
    contradiction

OPTIONAL / FALLBACK — E4-A4R: REGULAR-APERTURE SELECTION
  if resonance materially obstructs the domination proof, formalize frozen-cutoff analyticity and the log-lift
    M_Q(L) = -log(L) I + B_Q(L)
    L = exp(z)
    det(Bhat(z)-z I)
  use 2*pi*i periodicity to prove determinant nonidentity
  use real analyticity to obtain dense apertures where all finitely many predecessor parity blocks are injective
  preserve an existing negative witness by continuity and reselect the least-bad size
  result: a first-bad witness with positive-definite predecessors
  WARNING: positive-definite predecessors do not exclude a negative successor; the canonical energy inequality is still required

PARALLEL SOURCE QUANTITATIVE LANE
  theoremize source-atom endpoint expansions only after exact algebraic verification
  candidate leading orders under boundary-flat moment cancellations:
    odd atom energy: omega^7
    even atom energy: omega^9
    even quadratic-normal moment: omega^7
  use these only as possible ingredients for the absolute-energy/domination theorem

PARALLEL — E4-B / E3-C / E3-B3
  parity shifted-nullity, secular monotonicity, and lower-floor deformation remain available
  do not let them displace source-normalization work unless they add genuinely new information
  root uniqueness remains weaker than root absence

TARGET
  canonical one-step domination / equivalent source-energy coercivity
  -> no canonical first-bad negative state
  -> no off-line zero via the existing global-first-bad reduction
  -> explicit terminal bridge to Mathlib RiemannHypothesis
  RH OPEN
```

## What is formally true now

Through #131 the project has theoremized the reduction

```text
hypothetical off-line zero
  -> one finite global-first-bad state
  -> lam<0 is an exact secular/eigenvalue root
  -> both predecessor parity sectors are nonnegative
  -> exact zero-shift regular/resonant classification
  -> exact cross-parity source transfer
  -> exact pole/arch/prime decomposition of the active source moment.
```

The hard remaining step is finite: exclude that actual canonical first-bad state.

## Post-#132 derived kernel targets

These are **DERIVED targets**, not current Lean declarations.

For the even/odd predecessor blocks A+/A-, centered-index transport D, predecessor corrections d/a, source moment mu, and z in ker A+:

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z)
```

where `beta(z)=<b+,z>/rho+`. Projecting to the full odd predecessor kernel gives

```text
(||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0.
```

This is stronger than the scalar cancellation obtainable from a future Laurent expansion and requires no spectral limit.

Under both regular couplings, the same geometry yields

```text
Gamma0 * mu(z) = 0
```

for every even predecessor-kernel vector z. This is a conditional compatibility law, not branch exclusion.

A second derived target is the direct zero-shift transfer, assuming only preimages `A+ x+=b+` and `A- x-=b-`:

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0).
```

Neither whole-block invertibility nor positive definiteness is required. The endpoint response is preimage-independent; `alpha0` and `Gamma0` individually need not be.

## Why the old factorwise source strategy is no longer primary

Exact rational generic countermodels preserve the centered grid, parity/boundary-flat geometry, KKT extraction, rank-one cubic defect, quotient transport, trial reconstruction and the full #129 scalar transfer while exhibiting:

```text
sourceMoment(u+) != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root while the even successor is positive
```

They are not the arithmetic canonical source and do not refute RH. They do refute structural arguments that require generic nonvanishing or sign of `alpha`, `Gamma`, overlap, or source moment.

Canonical high-precision diagnostics also show both signs for the source moment and a negative alpha in legal sampled states. Therefore factorwise sign hunting should not consume the next theorem sequence unless a new canonical normalization theorem explicitly enters.

## Absolute spectral origin is the missing information channel

In the generic structural package, the covariance

```text
M -> M+tI
lambda -> lambda+t
```

leaves the shifted trial vectors, defect/source functional, `alpha`, `Gamma`, and secular transfer data unchanged while moving the absolute spectrum relative to zero.

That is why the cross-parity package by itself cannot decide whether a root is negative. The canonical arithmetic normalization must enter through a quantity that is not scalar-shift invariant.

The natural quantity is the absolute quadratic energy / one-step block extension:

```text
q_c = Re<Tc,c>
A = P_W T|_W
b = P_W T c.
```

The desired domination

```text
|<w,b>|^2 <= q_c Re<Aw,w>
```

is equivalent to positivity of the one-step block extension when `A>=0`. It is unresolved positivity content and must be derived from the exact pole/arch/prime source, including its scalar normalization.

## Why the #131 moment is insufficient by itself

The #131 observable deliberately annihilates scalar identity shifts. That is exactly right for the cubic parity defect, but it erases the normalization information needed to locate the spectral origin.

Therefore the next arithmetic theorem should not merely decompose `explicitCanonicalSourceMoment` again. It should restore the absolute source energy, including the canonical archimedean scalar correction, and use the specific canonical shell/trial geometry.

## Quantitative source clue

Taylor algebra at source coordinate `omega=0` suggests much higher cancellation than the currently formal C2 endpoint package exposes. Under boundary-flat moment constraints (`mu0=mu1=mu2=0`), the first potentially nonzero terms are predicted at high order:

```text
odd atom energy        ~ -2(2pi)^6 |mu3|^2 omega^7 / 7!
even atom energy       ~ +2(2pi)^8 |mu4|^2 omega^9 / 9!
even normal moment     ~ -2(2pi)^6 mu4     omega^7 / 7!
```

High-precision ratios strongly support these coefficients, but this remains **DERIVED / EXPERIMENTAL**, not a Lean theorem. The purpose of formalizing it would be to obtain source-specific quantitative control for the absolute-energy theorem, not to claim a global atom sign.

## Falsification gates

Before promoting any proposed source estimate:

- run it against the exact rational post-#129 countermodels;
- test `Gamma=0`, `alpha=0`, overlap zero, and sourceMoment zero separately;
- test both parities; an even-only exclusion theorem is insufficient;
- test scalar-shift covariance: if the proposed argument survives arbitrary `M+tI` without using canonical normalization, it cannot locate zero;
- test canonical low-dimensional cases numerically before formalization;
- test the elementary atom at `omega=1/2`, where exact legal fixtures have both positive and negative energies;
- preserve the predecessor correction in `D c+`;
- never use D as an isometry;
- never divide by `alpha`, `Gamma`, overlap, or source moment without a theorem;
- no `A^-1` at zero;
- positive-definite predecessor selection is simplification, not negative-root exclusion;
- no finite prefix, fitted tail, or high-precision residual is a theorem.

## Permanent claim boundary

**PROVED:** theorem authority remains exactly through PR #131: finite off-line-zero reduction, global first-bad state, exact negative secular root, zero-shift regular/resonant package, cross-parity transfer, and exact canonical source-moment decomposition.

**DERIVED:** denominator-free kernel/source transport identities; direct zero-shift transfer; scalar-shift origin blindness of the generic transfer package; the implication that a one-step domination theorem would kill both resonance and the regular negative endpoint.

**LEAD / HYPOTHESIS:** canonical absolute source-energy decomposition; canonical one-step domination; high-order source-coordinate endpoint cancellations as an ingredient; log-lift dense regular-aperture selection.

**EXPERIMENTAL SIGNAL:** exact rational generic countermodels; high-precision canonical source checks; numerical confirmation of the #129 transfer and high-order endpoint coefficients.

**OPEN:** canonical one-step domination, finite first-bad exclusion, negative-root exclusion, terminal Mathlib RH bridge, RH.

**RH remains OPEN.**
