# Post-#142 regularization countermodel — geometry, persistence and regularity still do not force the arithmetic sign

> **Claim firewall: this is a generic analytic countermodel, not the canonical zeta source and not a counterexample to RH. RH remains OPEN.**

Date: 2026-09-10

## Purpose

PR #142 proves that one strict finite canonical negative witness persists with the same finite size and the same vector on an open neighborhood inside one physical cutoff cell.

The post-#142 route then proposes to combine persistence with a cell-minimal bad size and dense predecessor regularity.

This note records a generic analytic negative control showing that those geometric ingredients, even strengthened substantially, do not by themselves imply a contradiction.

## Family

On centered coordinates `-N,...,N`, define a reversal-symmetric real diagonal family

```text
M_N(L) = diag(q_|n|) + (L - 1 - log L) I,    L>0,
```

where

```text
q0 = 0
q1 = 1
q2 = -3
q3 = 17
qn = -n^8,  n>=4.
```

The aperture correction satisfies

```text
L - 1 - log L >= 0
```

for every `L>0`, with equality at `L=1`.

The family is real analytic on the positive aperture axis and has the explicit scalar form

```text
-log L * I + entire/elementary remainder.
```

## Positive predecessors at the globally minimal bad size

At radius two, the relevant boundary-flat parity predecessor eigenvalues reduce to

```text
13/35 + (L - 1 - log L)
1/5   + (L - 1 - log L),
```

so both are strictly positive for every `L>0`.

At `L=1`, radius three has a common negative eigenvalue `-1/7` in both parities.

Therefore radius three is a globally minimal bad size while both predecessor parity sectors remain positive throughout the whole positive aperture axis.

This is stronger than the regularity state required by the proposed canonical route.

## Persistent badness at every aperture

Let

```text
s = L - 1 - log L.
```

For any `N>=4`, choose the even boundary-flat vector

```text
v_{+N}=v_{-N}=1
v_{+1}=v_{-1}=-N^2
v_0=2(N^2-1)
```

with all other coordinates zero.

Its squared norm is

```text
||v||^2 = 6N^4 - 8N^2 + 6.
```

Its quadratic energy is

```text
-2N^8 + 2N^4 + s(6N^4 - 8N^2 + 6).
```

Hence the energy is negative whenever

```text
N^4 > 1 + 3s.
```

For every fixed `L>0`, the right-hand side is finite, so sufficiently large `N` gives a strict negative finite witness.

Thus this generic family has finite negative witnesses at every positive aperture, not merely locally.

## What the fixture falsifies

The following package is compatible with persistent finite badness:

```text
analytic aperture dependence
exact scalar -log L contribution
reversal parity
centered finite nesting
boundary-flat constraints
persistent negative finite witnesses
cell/global minimal bad size
both predecessors positive and therefore regular
common negative state in both parities.
```

Therefore no contradiction may be inferred from this package alone.

In particular:

```text
aperture freedom
+ #142-style witness persistence
+ cell-minimality
+ predecessor PSD/PD
+ determinant nonvanishing
+ parity structure
+ scalar logarithmic normalization
!= negative-root exclusion.
```

A successful canonical proof must use information absent from this fixture: the exact pole, archimedean and von-Mangoldt source channels and their production normalization.

## Interaction with #134/#136/#137

When a predecessor is regular, its kernel is zero. Consequently the #134 product law involving `Gamma0*mu(z)=0` on kernel/preimage configurations cannot by itself generate a sign contradiction in the regular state; the kernel obstruction has been removed.

#136 still supplies the exact scalar-sensitive canonical energy target, and #137 supplies the one-step determinant/countercertificate interface. This generic fixture shows why an independent arithmetic sign theorem is still required after regularization.

## Regression rule

Any proposed post-#142 contradiction should be tested against this fixture before formal investment.

If the argument proves impossibility using only the generic ingredients listed above, it is overstrong and cannot be the missing canonical arithmetic step.

The fixture may be strengthened or translated into executable exact-rational checks, but such checks remain regression evidence rather than Lean theorem authority unless separately formalized.

**RH remains OPEN.**
