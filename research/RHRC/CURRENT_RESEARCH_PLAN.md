# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after theorem PR #134 = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
live main tree = c142efa141036331d139c532d06e7a976c5b50c2

theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
theorem tree = c142efa141036331d139c532d06e7a976c5b50c2
theorem-bearing merged through = PR #134
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
Control v2 / FFBBP v1.6 hardened research-control semantics = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative over prose. PR #134 is theorem-bearing and advances theorem authority. Machine claim promotion remains a separate surface.

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
  exact denominator-free kernel/source transport / #134
  direct zero-shift cross-parity transfer / #134
  Gamma0 * mu(z) = 0 on every even predecessor-kernel vector / #134

POST-#134 RESEARCH CONCLUSION
  zero-shift transport is no longer the bottleneck
  the whole-kernel vector identity is stronger than the old scalar Laurent target
  no zero-shift inverse/pseudoinverse/limit is needed for the current route
  regular-kernel beta(z)=0 follows from the preimage equation + symmetry
  Gamma0*mu(z)=0 is a product law, not factorwise exclusion
  exact generic countermodels still kill structural nonvanishing/sign shortcuts
  scalar-shift covariance still shows transfer data cannot locate spectral zero

NOW — E4-A4b1: ABSOLUTE CANONICAL SOURCE ENERGY
  define the exact real quadratic energy
    E_p(L,N,v) = Re <T_p v, v>
  decompose it through the production source:
    pole energy
    reduced arch diagonal energy
    reduced arch off-diagonal energy
    canonical arch scalar identity correction
    finite von-Mangoldt prime-atom energy sum
  retain the scalar normalization deliberately annihilated by #131's moment
  specialize to the canonical cubic shell and zero-shift trial
  theoremize the exact regular-preimage energy/Schur identity
  do NOT assert positivity in this PR unless separately proved

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
  only if resonance materially obstructs the energy estimate
  formalize frozen-cutoff analyticity and the log-lift
    M_Q(L) = -log(L) I + B_Q(L)
    L = exp(z)
    det(Bhat(z)-z I)
  use periodicity + determinant nonidentity + real analyticity to obtain dense regular apertures
  preserve a negative witness by continuity and reselect the least-bad size
  WARNING: positive-definite predecessors do not exclude a negative successor

PARALLEL SOURCE QUANTITATIVE LANE
  theoremize source-atom endpoint expansions only after exact algebraic verification
  candidate leading orders under boundary-flat moment cancellations:
    odd atom energy: omega^7
    even atom energy: omega^9
    even quadratic-normal moment: omega^7
  use them only if they feed a rigorous absolute-energy/coercivity estimate

PARALLEL — E4-B / E3-C / E3-B3
  parity shifted-nullity, secular monotonicity, and lower-floor deformation remain available
  do not let them displace canonical source-normalization work unless they add independent exclusion information
  root uniqueness remains weaker than root absence

TARGET
  canonical one-step domination / equivalent source-energy coercivity
  -> no canonical first-bad negative state
  -> no off-line zero via the existing global-first-bad reduction
  -> explicit terminal bridge to Mathlib RiemannHypothesis
  RH OPEN
```

## What is formally true now

Through PR #134 the project has theoremized the reduction

```text
hypothetical off-line zero
  -> one finite global-first-bad state
  -> lam<0 is an exact secular/eigenvalue root
  -> both predecessor parity sectors are nonnegative
  -> exact zero-shift regular/resonant classification
  -> exact cross-parity source transfer
  -> exact pole/arch/prime decomposition of the active source moment
  -> exact denominator-free kernel/source transport
  -> exact direct zero-shift cross-parity transfer
  -> exact Gamma0*mu(z)=0 compatibility on the full even predecessor kernel.
```

The hard remaining step is finite and source-specific: prove that the actual canonical first-bad state cannot have the required negative energy/sign.

## PR #134 theorem surface

For `z in ker A+`:

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z)
```

and therefore in the whole odd predecessor kernel

```text
beta(z) K-d + mu(z) K-a = 0.
```

For the actual even cubic coupling-kernel component, `beta` is identified with the canonical self-inner coefficient divided by the shell norm.

If the even cubic coupling has a zero-shift preimage, the odd cubic coupling-kernel component is exactly driven by the even zero-shift response plus the source term. If both parities have preimages:

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
Gamma0 = <u-0,g->/rho-
Gamma0 * mu(z) = 0  for every z in ker A+.
```

No whole-block invertibility, pseudoinverse, Laurent expansion, kernel-dimension assumption, D-isometry, or factor nonzeroness is used.

## Why the next object is energy, not another source moment

The #131 quadratic-normal moment is exactly the correct linear observable for the cubic parity defect, but it annihilates scalar identity shifts. The generic structural package has the covariance

```text
M -> M+tI
lambda -> lambda+t
```

which can preserve the transfer data while moving the spectrum across zero. Therefore a closure theorem must spend canonical information that remembers the absolute spectral origin.

The natural quantity is

```text
E(v) = Re<Tv,v>.
```

The next PR should expose this exact arithmetic expression before attempting a positivity theorem.

## E4-A4b1 implementation target

The next theorem PR should preferably add a narrow module such as

```text
Zeta23/CCM/CanonicalSourceEnergy.lean
```

and wire it into `Zeta23/CCM.lean`.

Desired theorem layers:

1. define production canonical energy on the legal parity carrier;
2. prove matrix-channel decomposition from
   `canonicalSourceMatrix = pole - arch - prime`;
3. retain and isolate the archimedean scalar correction rather than cancelling it;
4. split reduced arch diagonal/off-diagonal energy;
5. split finite prime energy into the exact von-Mangoldt source atoms;
6. specialize to the cubic shell `c` and zero-shift trial `u0`;
7. prove the exact regular-preimage identity connecting `Re<Tu0,u0>` to the zero-shift Schur endpoint.

A green decomposition is not yet positivity. Post-green analysis must inspect which channel can actually supply coercivity.

## Falsification gates for energy/coercivity

Before promoting any proposed inequality:

- run it against the exact rational post-#129 countermodels;
- verify the argument genuinely uses canonical scalar normalization and therefore does not survive arbitrary `M+tI`;
- test both parities;
- test canonical low-dimensional matrices numerically before formalization;
- test the elementary source atom at `omega=1/2`, where legal vectors realize both energy signs;
- preserve the predecessor correction in `D c+`;
- never divide by `alpha`, `Gamma`, overlap or source moment without a theorem;
- never infer `mu(z)=0` from `Gamma0*mu(z)=0` without separately proving `Gamma0!=0`;
- no `A^-1` at zero;
- positive-definite predecessor selection is simplification, not negative-root exclusion;
- no finite prefix, fitted tail or high-precision residual is theorem authority.

## Permanent claim boundary

**PROVED:** theorem authority is through PR #134: finite off-line-zero reduction, global first-bad state, exact negative secular root, zero-shift regular/resonant package, cross-parity source transfer, exact canonical source-moment decomposition, denominator-free whole-kernel transport, direct zero-shift transfer, and `Gamma0*mu(z)=0` on the even predecessor kernel.

**DERIVED:** scalar-shift origin blindness of the generic transfer package; the implication that a canonical one-step domination theorem would kill both resonance and the regular negative endpoint; the source-coordinate high-order cancellation formulas not yet theoremized.

**LEAD / HYPOTHESIS:** canonical absolute source-energy decomposition as the next theorem layer; canonical one-step domination; high-order endpoint cancellations as a possible quantitative ingredient; log-lift dense regular-aperture selection.

**EXPERIMENTAL SIGNAL:** exact rational generic countermodels; high-precision canonical source checks; numerical endpoint-order checks.

**OPEN:** absolute canonical source-energy theorem, canonical one-step domination, finite first-bad exclusion, negative-root exclusion, terminal Mathlib RH bridge, RH.

**RH remains OPEN.**
