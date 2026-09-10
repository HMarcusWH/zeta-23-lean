# Post-#142 research delta — fixed-cell witness persistence, cell-minimal regularization, and analytic frozen predecessors

> **Claim firewall: RH remains OPEN.**

Date: 2026-09-10

This delta supersedes `RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md` as the current-priority research note. Older deltas remain historical evidence and must not be rewritten to look current.

## Exact validated authority

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Compiler/CI evidence is authoritative for the exact theorem state. PR #142 is theorem-bearing and advances theorem authority beyond #140. It does not prove determinant nonidentity, dense regular apertures, successor positivity, negative-root exclusion, the regular Schur-energy sign, or RH.

## What became formally true

### PROVED — fixed-cell continuity of the actual canonical source

`Zeta23/CCM/CanonicalApertureContinuity.lean` theorem-locks the real continuity layer for the production object `canonicalSourceMatrix`.

Headline endpoints:

```text
continuousOn_canonicalSourceMatrix_apply_fixedCell
continuousOn_re_canonicalSourceQuadraticForm_fixedCell
exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
```

For `Q >= 1`, on the physical cutoff cell

```text
I_Q = (log Q, log(Q+1))
```

one has `floor(exp L)=Q`, the prime channel is frozen, each canonical matrix entry is continuous, and for every fixed finite vector `u` the real quadratic energy is continuous.

Therefore, if

```text
Re quadraticForm(canonicalSourceMatrix L1 N,u) < 0
```

at one interior aperture `L1`, then there exists an open `J` with

```text
L1 in J
J subset I_Q
forall L in J,
  Re quadraticForm(canonicalSourceMatrix L N,u) < 0.
```

The same finite size `N` and the same vector `u` remain negative throughout `J`.

### PROVED — off-line zero to locally persistent fixed witness

`Zeta23/ExceptionalZero/FixedCellWitnessPersistence.lean` adds:

```text
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_exists_offLine_zero
```

Combined with #140 aperture freedom, an off-line zero yields a threshold `L0` such that every chosen cell-interior aperture above `L0` receives a finite boundary-flat negative canonical witness that persists locally with its size and vector fixed.

The persistence neighborhood does not itself need to remain above `L0`; after the fixed witness has been selected and proved negative, local persistence follows from continuity.

## What changed mathematically

#140 changed the quantifier from one movable witness to fresh negativity at every sufficiently large aperture.

#142 now freezes the selected finite data locally:

```text
choose interior aperture L1
-> obtain finite witness (N,u)
-> same (N,u) remains negative on an open neighborhood J in the same cell.
```

This closes the continuity/persistence obligation in the finite-cell route.

The countable all-size Baire route is now a fallback rather than the preferred strategy.

## DERIVED — stronger cell-minimal composition

A further simplification is available before any determinant regularization.

For a physical cutoff cell containing at least one bad finite state, define

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then:

```text
K* >= 2;
there exists L* in I_Q where size K* is bad;
for every L in I_Q and every K<K*, both parity sectors at size K are nonnegative;
the predecessor size N*=K*-1 is therefore PSD throughout the whole cell.
```

Choose a negative parity witness at `(L*,K*)`. By #142 the same witness remains negative on an open `J subset I_Q`.

If the relevant predecessor regularity set is dense in the cell, it meets `J`. At such a selected aperture the predecessor is simultaneously:

```text
PSD       from cell-wide minimality
injective from regularity
PD        by finite-dimensional Hermitian linear algebra.
```

This means the preferred route no longer needs regularization of every size through a finite prefix. For the bad parity's Schur reduction, regularizing that parity's predecessor at the single size `N*` is mathematically sufficient. Regularizing both parities at that same size remains a useful symmetric option for cross-parity machinery.

A standalone abstract conditional selection theorem has been locally compiled against the pinned Lean/Mathlib installation. It is **LOCAL LEAN CHECK**, not merged theorem authority. The production specialization remains to be packaged.

## Primary OPEN analytic target

The remaining regularization obstacle is now sharply isolated:

```text
for fixed Q,p,N:
actual frozen intrinsic predecessor determinant
  -> analytic continuation
  -> determinant nonidentity
  -> dense regular apertures in I_Q.
```

The target must be the determinant of the actual `intrinsicPredecessorBlock`, not an unprojected or predecessor-size proxy.

## LEAD — fixed-unit-interval archimedean continuation

#142 removes the apparent origin singularities in the production archimedean primitives using divided slopes and `Real.sinc`.

After the real change of variables `x=L t`, the integration interval becomes fixed. Writing

```text
h(x)=exp(x/2)/(2*sinhc(x))
C=2*pi*n
```

one obtains the derived real identities

```text
alpha_n(L)
  = 2*n * integral_0^1 sinc(C*t) * h(L*t) dt

beta_n(L)
  = integral_0^1 cos(C*t) * h(L*t) dt

gamma_n(L)-wCorrection(L)
  = integral_0^1
      [ C*cSlope(C*t) + (L/2)*eSlope(-L*t/2) ] * h(L*t) dt.
```

Here `gamma_n` is the production `sourceEq44GammaL`; it is not the cross-parity transfer factor `Gamma0`.

These rescaled identities are **DERIVED**, not merged Lean declarations. Numerical comparison against the production real integrals passed 48 selected cases at 70-digit precision. That result is an **EXPERIMENTAL SIGNAL** checking factors and removable values, not a proof of holomorphy.

The fixed interval and fixed oscillatory frequency make direct complexification more concrete than before #142. Aperture dependence is confined to regularized analytic factors.

## LEAD — logarithmic monodromy for determinant nonidentity

The #140 scalar theorem already gives the real-axis decomposition

```text
-2*wCorrection(L) = -log(L) + canonicalApertureScalarRemainder(L).
```

The desired complex architecture is therefore

```text
A(L) = -Log(L) * I + B(L)
```

for a single-valued holomorphic remainder `B` on a connected punctured domain containing the positive real axis and a loop around zero.

With `L=exp(z)`, define

```text
Ahat(z) = -z*I + B(exp z).
```

If `B` is single-valued in `L`, then `B(exp(z+2*pi*i))=B(exp z)`. If `det Ahat` vanished identically, then at a fixed base point the same finite matrix would acquire arbitrarily many distinct shifted eigenvalues `z+2*pi*i*k`, impossible for finite dimension.

Thus the candidate chain is

```text
single-valued holomorphic remainder
+ logarithmic monodromy
+ finite dimension
-> determinant nonidentity
-> isolated determinant zeros
-> dense real regular apertures.
```

This is a **LEAD / HYPOTHESIS** until the full production continuation and domain are theoremized.

A natural candidate domain is a punctured strip around the positive axis bounded by the first nonzero imaginary singularities of the hyperbolic factors, schematically near `|Im L|<pi`. This must be checked channel by channel rather than assumed.

## Falsification — regularity is not the arithmetic contradiction

A stronger generic analytic countermodel shows that the following ingredients can coexist:

```text
exact scalar term -log L;
analytic dependence on L>0;
predecessor positivity throughout the positive axis;
persistent negative finite witnesses at every aperture;
a globally minimal bad size;
a common negative root in both parities.
```

One concrete centered diagonal family is

```text
M_N(L) = diag(q_|n|) + (L-1-log L) I
```

with

```text
q0=0, q1=1, q2=-3, q3=17, qn=-n^8 for n>=4.
```

Because `L-1-log L >= 0`, the predecessor eigenvalues at radius two are positive for every `L>0`, while radius three is bad at `L=1`; sufficiently large radii are bad at every positive aperture.

This is not the canonical zeta source and is not an RH counterexample. Its role is a permanent design firewall:

```text
aperture freedom
+ persistence
+ cell/global minimality
+ regularity
+ parity
+ scalar logarithm
!= arithmetic contradiction.
```

The actual pole/archimedean/von-Mangoldt channels must contribute genuinely new information.

The #134 product law `Gamma0*mu(z)=0` also becomes vacuous on an injective predecessor because the relevant kernel has disappeared. Regularity removes resonance; it does not turn kernel transport into an energy-sign theorem.

## Exact RH reduction after #142

The route now separates cleanly into two distinct OPEN gaps:

```text
off-line zero
  -> persistent cell-minimal bad state                      PROVED + DERIVED
  -> regular state with Ecanonical(c-x0)=Re S0<0            OPEN: analytic regularity + wrapper
  -> False                                                  OPEN: arithmetic contradiction
  -> no off-line zero
  -> terminal Mathlib RiemannHypothesis wrapper             OPEN packaging
```

The first missing arrow has a concrete analytic mechanism. The second does not yet have a legitimate proof mechanism.

At a regular first-bad predecessor:

```text
A>=0
A injective
unique x0 with A x0=b
u0=c-x0
Ecanonical(u0)=Re S0<0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0) >= 0
```

or equivalently, once inverse notation is legal,

```text
<b,A^-1 b> <= q_c.
```

A proof that simply repackages successor positivity or universal one-step domination does not count as a reduced argument.

## New arithmetic clue from cell-wide minimality

**LEAD.** Cell-minimality supplies predecessor nonnegativity throughout an interval, not merely at one aperture. Once differentiability is available, an interior kernel vector would satisfy first- and second-order necessary conditions involving aperture derivatives of the actual predecessor family.

These derivative constraints may expose weighted prime/archimedean identities absent from the pointwise certificate. The generic countermodel shows such identities cannot yield a contradiction from geometry alone; their value depends on actual arithmetic coefficients.

## Highest-leverage next work

```text
1. production cell-minimal bad-state theorem;
2. complex continuation primitives for the #142 regularized archimedean forms;
3. frozen intrinsic predecessor holomorphy and scalar-log decomposition;
4. finite-dimensional monodromy/nonidentity theorem;
5. dense fixed-cell regularity;
6. compose with cell minimum + #142 persistence + existing Schur/energy machinery;
7. expose the exact regular scalar energy deficit;
8. attack that deficit using source-specific arithmetic.
```

The all-size Baire route remains a fallback. Additional generic parity, kernel, or determinant geometry should not displace the source-specific arithmetic work unless it introduces genuinely new information.

## Evidence labels after #142

**PROVED**

- theorem authority through PR #142;
- #140 aperture freedom and regularity/frozen-source scaffold;
- fixed-cell `floor(exp L)=Q`;
- entrywise continuity of the actual canonical source matrix on a physical cutoff cell;
- fixed-vector canonical quadratic-energy continuity on that cell;
- persistence of the same finite negative witness on an open in-cell neighborhood;
- off-line-zero wrapper supplying such local persistence beyond the #140 threshold.

**DERIVED**

- cell-minimal bad size makes every smaller size good in both parities throughout the cell;
- only the predecessor determinant(s) at the single cell-minimal size need regularizing in the preferred route;
- rescaled fixed-unit-interval archimedean identities;
- first-bad PSD + injective Hermitian predecessor -> positive definite predecessor.

**LOCAL LEAN CHECK**

- abstract conditional cell-minimal regular selection theorem; not merged and not canonical determinant density.

**LEAD / HYPOTHESIS**

- single-valued holomorphic continuation of the actual frozen predecessor remainder;
- punctured-strip continuation around zero;
- determinant nonidentity by logarithmic monodromy/eigenvalue counting;
- dense fixed-cell regularity;
- derivative-weighted arithmetic constraints from interval-wide predecessor PSD;
- regular canonical Schur-energy nonnegativity.

**EXPERIMENTAL SIGNAL**

- 48 high-precision checks of the rescaled real integral identities;
- prior prime-weight sensitivity and cancellation diagnostics.

**OPEN**

- production cell-minimal wrapper;
- full analytic frozen predecessor theorem;
- determinant nonidentity and dense regularity;
- regular first-bad source countercertificate wrapper;
- arithmetic nonnegativity of the regular zero-shift trial energy;
- negative-root exclusion;
- terminal Mathlib RH bridge;
- RH.

## Permanent firewalls

```text
fixed-cell continuity != analyticity
analyticity != determinant nonidentity
regular predecessor != positive successor
cell-minimality + regularity != arithmetic contradiction
Gamma0*mu(z)=0 with trivial kernel != source sign
universal domination restatement != research reduction
high-precision agreement != theorem
synthetic analytic countermodel != zeta counterexample
```

**RH remains OPEN.**
