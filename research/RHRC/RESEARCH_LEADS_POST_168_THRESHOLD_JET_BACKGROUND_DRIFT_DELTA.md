# Post-#168 FB-05 threshold-jet / background-drift research delta

> **Claim firewall: RH remains OPEN.**
>
> This document is a research synthesis, not theorem authority. Live GitHub, Lean/compiler results and exact CI evidence outrank this prose.

## Authority split

The formal theorem surface did **not** move after PR #163.

```text
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
```

The latest merged research-evidence anchor is PR #168:

```text
research PR = #168
validated research head = 9657dad6f1e262b1fa7e08e6944aaa935feeaf33
merged research commit = 4e2c111a836f3fc95f8209485f726dc886c918e7
research tree = 881e1f05302041f56ae4b6a14f14e45d7bbc096b
RHRC #1055 = SUCCESS
Permansson #828 = SUCCESS
```

Control-v2 semantic authority remains PR #117. The selected formal break remains `E4A4-SCHUR-FB-05`. Machine claim promotion is unchanged.

## What is formally true before this research delta

The theorem package through #163 gives one retained even-selected shifted negative state carrying all of:

```text
R8(u_lambda) < 0
F_odd(lambda) = Gamma(lambda) * explicitCanonicalSourceMoment(u_lambda)
odd successor bad OR explicitCanonicalSourceMoment(u_lambda) != 0
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
2*(2*pi)^4*(R8(u_lambda)-R9(u_lambda)) = S8(L)*|h^(7)(0)|^2
```

and, on the retained even-selected branch,

```text
2*(2*pi)^4*R9(u_lambda) < -S8(L)*|h^(7)(0)|^2.
```

No current Lean theorem proves a sign or nonvanishing theorem for `S8`, a sourceMoment-to-`M4` implication, simultaneous parity exclusion, odd-selected closure, negative-root exclusion, or RH.

## Research sequence #165 -> #168

### #165 — endpoint scalar audit

PR #165 exposed the exact executable finite arithmetic form of

```text
canonicalPolePrimeRieszEndpointScalar L 8
```

with the project normalization `Riesz order 8 -> ninth left-anchored primitive -> L^-9`. Prime powers are included through von Mangoldt weights.

The broad finite search and checked-in Arb fixtures found no sampled negative value. This is evidence only; there is no global sign theorem.

More importantly, the #163 recurrence already shows why endpoint positivity alone is not the contradiction:

```text
S8(L) >= 0
and R8(u_lambda) < 0
  -> R9(u_lambda) <= R8(u_lambda) < 0.
```

So a future sign theorem for `S8` would propagate transformed negativity unless composed with a genuinely independent terminal restriction.

Near zero the exact fixed-cell expression has `S8(L) -> 0` at least linearly; therefore no uniform positive lower bound should be assumed.

**Research consequence:** endpoint-scalar sign/nonvanishing remains mathematically open but is no longer the default standalone FB-05 closure mechanism.

### #166 — theorem-aligned shifted-state discriminator

PR #166 corrected an important state mismatch. The retained state is not the old zero-shift Schur trial. In the exact integer predecessor basis `W`, with Gram matrix `G`, production restriction `H`, shell generator `c`, coupling `r`, and negative secular root `lambda`, the theorem-aligned ray is

```text
u_lambda = c - W (H - lambda G)^(-1) r.
```

The Gram matrix is essential because the checked-in basis is not orthonormal.

The broadened finite scout covered 672 sampled canonical states and found zero reconstructible negative successors. That is not a positivity theorem. It did, however, isolate an odd near-critical family at

```text
Q = 16
N = 3
K* = 4
parity = odd
```

with a floating successor eigenvalue on the order of `10^-12`. Arb/Sylvester replay certified the exact sampled point positive definite.

**Research consequence:** the first-bad numerical route was not instantiated, but the strongest finite signal became a sharply localized near-boundary problem rather than a uniform scan problem.

### #167 — Q16 full-cell barrier and interval-method falsification

PR #167 compressed the selected odd `K=4` restriction to its three Sylvester determinants and attacked the complete fixed `Q=16` cutoff cell.

Floating optimization found no negative point and pushed the apparent minimum toward the upper threshold `L = log 17`.

The direct whole-cell Arb strategy was then attacked adversarially. Even after depth-8 dyadic subdivision:

```text
leaf_count = 256
POSITIVE_CERTIFIED = 0
BAD_INTERVAL_CERTIFIED = 0
UNRESOLVED = 256
```

This is a certification-method result, not evidence of either sign.

**Research consequence:** brute-force subdivision of the current dependency-heavy full matrix representation is not a productive certification route. A dependency-reduced scalar barrier, derivative bound, or analytic decomposition is required.

### #168 — boundary-flat prime-entry threshold jet

PR #168 attacked the arithmetic seam at `L = log 17`. A sanity check corrected the unconstrained parity expansion: the actual successor carrier is boundary-flat, so centered moments `M0=M1=M2=0` vanish before parity reduction.

Exact executable SymPy identities on the project's integer parity/boundary-flat bases for `K=2..8` give:

```text
odd carrier:
  orders 1,3,5 vanish
  first surviving order 7 = -(2/7!) M3^T M3

even carrier:
  orders 1,3,5,7 vanish
  first surviving order 9 = +(2/9!) M4^T M4
```

with the common `(2*pi)^(2k)` factor removed. The canonical prime contribution carries the opposite sign because the production source subtracts the prime channel.

Thus the isolated entering-prime contribution is seventh-order stabilizing on the odd boundary-flat carrier and ninth-order destabilizing on the even carrier, in source coordinate

```text
omega_q(L) = 1 - log(q)/L.
```

This is exact executable algebra and high-precision research evidence, not Lean theorem authority.

The physical Q16/Q17 microscope produced:

```text
L = log 17 threshold: POSITIVE_CERTIFIED
Q16/Q17 fixed-cutoff continuations overlap at threshold: true
18 / 18 two-sided Arb microscope points: POSITIVE_CERTIFIED
floating Q17 classification: CONTINUES_DOWN_BUT_POSITIVE
```

The isolated odd entering-prime stabilizer therefore does **not** reverse the full canonical background trend in the tested Q17 state.

**Research consequence:** formalizing the isolated threshold jet alone would be mathematically interesting but currently low leverage for FB-05. The missing object is the full scalar barrier/background variation.

## New active lead — full scalar pivot / background variation

The post-#168 research object should be a scalar final Sylvester/Schur pivot rather than the full interval matrix.

Near a prime-power threshold, schematically:

```text
P(L) = P_background(L) + P_entering_q(L).
```

For the odd boundary-flat carrier, the entering term begins at order seven in `omega_q`; for the even carrier it begins at order nine.

The background consists of the continuously varying pole, archimedean, scalar-repair and already-active prime-power channels. It can therefore dominate the local derivative even while the new prime atom has a favorable high-order sign.

The next research PR should determine:

1. the full scalar pivot and its channel reconstruction;
2. one-sided/background derivative data at the relevant prime-power threshold;
3. the exact leading rank-one threshold-kick coefficient projected into the pivot;
4. the predicted catch-up scale between smooth drift and the high-order arithmetic kick;
5. whether the same mechanism persists through later actual prime-power thresholds and other near-critical sizes/parities;
6. whether a true scalar barrier, parity incompatibility, or finite bad successor emerges.

A useful heuristic scale in the odd case is

```text
omega_catch ~ (-P_background'(0) / (7*kappa))^(1/6)
```

when the background derivative is negative and the seventh-order coefficient `kappa` is positive. This is a research diagnostic, not a theorem statement.

## Why this is not the old global Schur-monotonicity route

The project has already quarantined global aperture/Schur monotonicity. The new target does **not** assume a fixed sign for the global derivative.

It is local and arithmetic:

```text
smooth canonical background near an actual prime-power seam
+
known high-order boundary-flat prime-entry response.
```

The objective is a cancellation-preserving local decomposition, not a universal monotonicity theorem.

## Reclassified FB-05 subroutes

### Endpoint scalar

**Formal status:** OPEN.

**Research priority:** lower as a standalone mechanism. Positive finite evidence survives, but positivity alone does not contradict the retained negative state.

### Prime-sample / local-jet rigidity

**Formal status:** OPEN.

#163 still provides an exact shared observable. #166-#168 do not prove `explicitCanonicalSourceMoment != 0 -> M4 != 0` or the converse.

### Simultaneous parity badness

**Formal status:** OPEN.

This remains a genuine alternative branch in #161 and may become more informative when combined with the parity-asymmetric threshold jets.

### Odd-selected coverage

**Formal status:** OPEN.

No WLOG-even theorem exists; `D` remains algebraic rather than unitary/isometric.

### Threshold prime-entry jet

**Formal status:** not separately theoremized in Lean.

**Research status:** exact executable identities + high-precision/Arb finite evidence. Valuable as a component of a stronger mechanism, not currently sufficient alone.

### Full scalar pivot/background dynamics

**Formal status:** OPEN.

**Research status:** NEXT / highest information gain.

## Falsification requirements for the next slice

Before Lean investment:

- reconstruct the scalar pivot independently from the full restricted matrix;
- verify channel reconstruction at the pivot level;
- compare finite differences, analytic/high-precision derivatives and Arb pointwise replay;
- test both sides of prime-power thresholds;
- preserve von Mangoldt prime powers, not primes only;
- test both parity sectors and several sizes;
- deliberately search for thresholds where the favorable high-order kick is too weak;
- test whether pivot sensitivity to the rank-one atom degenerates;
- do not interpret Arb `UNRESOLVED` as a sign;
- do not revive global monotonicity under a new name;
- if an actual negative successor is found, feed that exact state into the #166 shifted-state discriminator.

## Highest-leverage next move

Create a research PR that decomposes and falsifies the full threshold pivot/background dynamics. Only if that produces a genuinely independent inequality or barrier should the project formalize the weakest useful theorem in Lean.

The expected path is therefore:

```text
#163 theorem authority
  -> #165 endpoint-scalar falsification
  -> #166 theorem-aligned shifted-state discriminator
  -> #167 near-critical scalar barrier + interval-method falsification
  -> #168 boundary-flat threshold jet + Q17 microscope
  -> NEXT: full scalar pivot/background variation
  -> surviving arithmetic barrier, if any
  -> Lean theoremization
  -> compose with exact retained state
  -> FB-06 negative-root exclusion
  -> FB-07 terminal zeta/Mathlib seam
```

## Permanent claim firewall

- exact executable algebra is not Lean theorem authority;
- finite Arb certification is not a whole-cell or global theorem;
- no sampled negative state is not positivity;
- endpoint-scalar positivity is not by itself root exclusion;
- threshold prime-entry stabilization is not full-source stabilization;
- sourceMoment and `M4` remain logically distinct without another theorem;
- simultaneous parity badness remains allowed;
- selected parity is not even WLOG;
- negative-root exclusion remains open;
- **RH remains OPEN.**