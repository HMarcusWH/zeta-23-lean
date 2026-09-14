# Post-#172 q13 even scalar-barrier research delta

> **Claim firewall: RH remains OPEN.**
>
> This document records the post-green research state after PR #172. It is a research-state synthesis, not Lean theorem authority. Exact compiler/CI evidence outranks this prose.

## Authority split

### Theorem authority

```text
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
```

### Latest research-evidence anchor

```text
latest merged research PR = #172
validated research head = 4c857cd031497d895232a18a4bfb9a094d9facae
merged research commit = a31bb0bb7f025d7727dd3f224c705af797f64a19
research tree = c64b098c3159d739fa15eeaa96e35693615873d7
RHRC #1063 = SUCCESS
Permansson #836 = SUCCESS
```

### Control authority

```text
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

Research PRs #165-#172 do not promote theorem authority beyond #163.

## What #172 actually tested

PR #172 moved the post-#170 local Schur-visibility picture into threshold-to-threshold production dynamics. The executable layer:

- locks exact finite-dimensional envelope/integration accounting on synthetic fixtures;
- identifies genuine nonzero von-Mangoldt seams;
- reconstructs production threshold/barrier budgets;
- scouts multiple q/N/parity arithmetic intervals;
- Arb-replays threshold and selected near-minimum points;
- preserves theorem-aligned `[W|c]` one-step geometry and H1 scope.

The tested genuine arithmetic intervals include

```text
9  -> 11
11 -> 13
13 -> 16
16 -> 17
17 -> 19
```

where the interval endpoints are consecutive nonzero von-Mangoldt seams, not merely consecutive integers.

## Main post-green discovery: q13/N2/K3/even

The most dangerous sampled production state is

```text
q = 13
q_next = 16
predecessor N = 2
successor K* = 3
parity = even
```

The floating scout records

```text
minimum sampled unit-shell pivot ~= 5.8032031e-12
headroom ratio                  ~= 9.821465e-4
sampled bad successor count     = 0
```

The 256-bit Arb replay at the quantized near-minimum candidate certifies

```text
full unit-shell pivot       ~= +5.8401616e-12
q-removed background pivot  ~= +1.2217611e-11
current-q entry lift         ~= -6.3774491e-12
```

with the predecessor H1 condition certified at that point.

So the q13 atom does not replenish the barrier at this finite target. It consumes about half of the positive background margin while the complete physical state remains positive.

## Arithmetic entry lift is sign-indefinite

The post-#170 intuition "entering arithmetic atom replenishes the barrier" does not survive #172 as a universal research heuristic.

The finite Arb replay includes:

```text
q9 / even   -> current-q entry lift NEGATIVE_CERTIFIED
q13 / even  -> current-q entry lift NEGATIVE_CERTIFIED
q16 / odd   -> current-q entry lift POSITIVE_CERTIFIED
```

At the q17 near-end candidate, the full physical state remains H1 but the q-removed background is not H1-certified, so the first-bad comparative lift is deliberately left unresolved there.

**Research conclusion:** current-q arithmetic lift is sign-indefinite in the tested canonical states. Any closing argument must control the complete physical scalar or prove a stronger state-dependent arithmetic restriction. A universal favorable-kick theorem is not supported by #172.

## Exact low-dimensional reduction at the q13 target

The executable theorem-aligned geometry has dimension

```text
dim V_N^parity = max(N-1, 0).
```

Therefore for the q13 target

```text
N = 2      -> predecessor dimension = 1
K* = 3     -> successor dimension   = 2.
```

In the exact one-step basis `[W|c]`, the complete successor restriction is literally

```text
H(L) = [[a(L), b(L)],
        [b(L), d(L)]].
```

The H1 condition is simply

```text
a(L) > 0.
```

The Schur pivot is

```text
P(L) = d(L) - b(L)^2 / a(L)
     = Delta_2(L) / a(L),

Delta_2(L) = a(L)d(L) - b(L)^2.
```

Hence on H1 scope

```text
sign P(L) = sign Delta_2(L).
```

This is the highest-information representation after #172: the full finite first-bad question on this target reduces to one predecessor scalar and one 2x2 determinant.

This is a research reduction in the executable coordinate. It is not itself a new Lean theorem.

## Physical cutoff seams inside the arithmetic 13 -> 16 interval

Mathematically, 13 -> 16 is one interval between consecutive nonzero von-Mangoldt seams because

```text
Lambda(14) = 0
Lambda(15) = 0.
```

But the production backend still tracks the physical integer cutoff

```text
Q = floor(exp L).
```

The #172 Arb replay therefore evaluates q13 candidates with physical cutoffs Q=14 and Q=15 as L moves across the interval.

A rigorous whole-interval #174 attack must not silently treat `[log 13, log 16]` as one fixed-Q interval. It should either:

1. certify the scalar piecewise on

```text
[log 13, log 14]
[log 14, log 15]
[log 15, log 16],
```

with threshold continuity/equality checks at 14 and 15; or

2. separately prove in the executable/Arb representation that the zero-von-Mangoldt additions at Q=14 and Q=15 are exactly inert for the reduced scalar.

The first approach is the preferred fail-closed implementation.

## Cancellation severity

The #172 threshold-barrier diagnostics expose very large channel cancellation ratios, including values on the order of

```text
~2e9  at q9/q13 examples
~1e10 at q16 example.
```

Therefore ordinary floating sums of separately large pole/arch/prime/scalar derivative contributions are not trustworthy at a `1e-12` barrier scale.

This strengthens the existing cancellation firewall: use the complete matrix/scalar object or rigorously controlled cancellation-preserving formulations. Do not infer the sign of the final pivot from coarse channel signs.

## What changed versus #170

### Before #172

The best finite picture was the q17/odd local decomposition:

```text
entering q17 atom     -> positive finite pivot effect
q-removed background -> negative finite difference
full sampled state    -> positive through q19.
```

### After #172

The broader threshold-to-threshold scout shows:

```text
arithmetic entry lift is not universally favorable;
the q13/even complete scalar comes within ~5.84e-12 of zero;
the q13 target is exactly 2-dimensional in [W|c] coordinates;
H1 + successor sign therefore reduce to a(L)>0 and Delta_2(L)>0;
physical cutoff seams 14/15 must still be handled rigorously.
```

The next question is no longer "does arithmetic replenishment beat background loss?" in general. It is:

> Can the complete q13/N2/K3/even scalar determinant cross zero while the 1D predecessor remains positive, or can that exact low-dimensional barrier be certified positive throughout the full physical 13 -> 16 interval?

## New reusable obstructions

### OBS-045 — current-q arithmetic entry is not universal barrier replenishment

Finite Arb evidence now contains both negative and positive current-q entry lifts. A proof route requiring a universally favorable entering arithmetic atom is unsupported and must provide additional hypotheses.

### OBS-046 — physical H1 does not imply q-removed-background H1

At q17, the complete physical state can remain H1 while the q-removed background leaves certified H1 scope. Therefore `P_full - P_background` has first-bad comparative meaning only after background H1 is separately established.

## Highest-leverage next research PR

Target:

```text
R003: resolve the q13 -> 16 even 2x2 Schur determinant barrier
```

Primary rigorous question:

```text
exists L in (log 13, log 16):
  a(L) > 0 and Delta_2(L) < 0
```

versus a full interval certificate

```text
a(L) > 0 and Delta_2(L) > 0
for all L in [log 13, log 16].
```

The rigorous implementation should respect the physical Q=13/14/15 subcells.

If a certified negative H1 point is found, feed that state immediately into the #166 shifted-state machinery.

If the whole q13 interval is certified positive, treat that as a **method/structure result**, not FB-05 closure. The retained first-bad state forced by an off-line zero has arbitrary canonical L/N/parity; positivity of this one finite q13 cell does not exclude all retained states. The next step would be to extract whatever arithmetic/scalar inequality made the 2x2 proof succeed and test whether it generalizes.

## Falsification checks

The next pass should deliberately test:

- whether `a(L)` approaches or crosses zero before `Delta_2(L)`;
- whether `Delta_2(L)` crosses zero in any of the Q=13/14/15 physical subcells;
- whether the q13 sampled minimum moves under higher-precision optimization;
- whether the opposite parity at the same q/N behaves qualitatively differently;
- whether negative entry lift is parity-driven or a q/N-specific effect;
- whether the reduced scalar representation actually resolves the dependency inflation that defeated the #167 full-matrix interval route;
- whether any apparently favorable inequality merely restates successor positivity.

## Claim firewall

- theorem authority remains #163;
- #172 is research evidence only;
- finite Arb point certification is not whole-cell positivity;
- a q13 whole-cell certificate would not by itself close FB-05;
- arithmetic entry lift is not known to have a universal sign;
- physical H1 does not imply background H1;
- channel pivot values are not additive;
- large cancellation makes coarse channel-sign reasoning unsafe;
- simultaneous parity badness remains open;
- odd-selected coverage remains open;
- negative-root exclusion remains open;
- RH remains OPEN.

**RH remains OPEN.**
