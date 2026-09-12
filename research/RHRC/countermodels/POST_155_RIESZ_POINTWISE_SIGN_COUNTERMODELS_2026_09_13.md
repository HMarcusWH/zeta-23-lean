# Post-#155 exact Riesz pointwise-sign countermodels

Date: 2026-09-13

> **Scope firewall:** these are exact finite countermodels to a proposed proof mechanism, not counterexamples to RH and not counterexamples to the #155 Riesz identity. **RH remains OPEN.**

## Mechanism being tested

The falsified implication is

```text
positive left-anchored Riesz primitive
+ boundary-flat endpoint cancellation
-> pointwise fixed-sign smoothed source-energy integrand.
```

A failure of this implication means smoothing cannot manufacture pointwise positivity merely from primitive positivity and endpoint flatness.

## Auditable production formula and checker

The regression evaluates derivatives directly from the production real source-entry formula in `Zeta23/CCM/DictionaryAnalysis.lean`:

```text
n != m:
  sourceEntryReal(omega,n,m)
    = [sin(2*pi*n*omega)-sin(2*pi*m*omega)] / [pi*(n-m)]

n = m:
  sourceEntryReal(omega,n,n)
    = 2*omega*cos(2*pi*n*omega).
```

For real fixture vectors the quadratic source contraction agrees exactly with the theorem-authoritative complex contraction by `sourceContract_eq_ofReal`.

The deterministic checker is:

```text
research/RHRC/countermodels/check_post155_riesz_pointwise_sign.py
```

It uses only integer and `Fraction` arithmetic. At `omega=0` and `omega=1/4`, the required trigonometric values lie in `{0,+/-1}`. The checker evaluates the exact normalized odd derivatives as rational pairs `a+b*pi`; it uses no floating approximation. `research/RHRC/tools/run_suite.py` executes this checker in CI.

## Exact K=2 fixtures

Use centered coordinates `n=-2,-1,0,1,2`.

### Even reversal fixture

```text
u_even = (1,-4,6,-4,1)
```

This vector is reversal-even and satisfies the three boundary-flat centered-moment constraints

```text
M0=0
M1=0
M2=0.
```

Even parity also gives `M3=0`.

For the production source energy `g_even`, the checker obtains the exact values

```text
g_even^(9)(0)   / [2*(2*pi)^8] = 576 > 0

g_even^(9)(1/4) / [2*(2*pi)^8]
  = -1024/3 - 16*pi < 0.
```

Therefore the ninth derivative changes sign between `omega=0` and `omega=1/4`.

### Odd reversal fixture

```text
u_odd = (1,-2,0,2,-1)
```

This vector is reversal-odd and satisfies

```text
M0=0
M1=0
M2=0.
```

For the production source energy `g_odd`, the exact checker gives

```text
g_odd^(7)(0)   / [2*(2*pi)^6] = -144 < 0

g_odd^(7)(1/4) / [2*(2*pi)^6]
  = 256/3 + 4*pi > 0.
```

Equivalently, under the historical normalization by the negative factor `-2*(2*pi)^6`, these are

```text
144 > 0
and
-256/3 - 4*pi < 0.
```

Therefore the seventh derivative also changes sign between `omega=0` and `omega=1/4`.

## What these fixtures establish

They falsify the proposed universal step

```text
D^[r](t) >= 0
and endpoint jets vanish
-> D^[r](t) * g^(r+1)(1-t/L) has a fixed sign pointwise.
```

Even when the Riesz primitive is positive in a prime-free aperture, the source-energy derivative factor can change sign.

The regression is exact at the finite source-entry level. It does not rely on the still-unproved complex `D`-transport theorem proposed for FB-03E.

## What they do not establish

They do **not** show that:

- the full integrated Riesz pairing has no useful sign;
- the complete discrepancy minus archimedean/scalar residual can be negative under the exact retained first-bad ancestry;
- the D-transport recursion is false;
- the #155 Riesz identity is false;
- RH is false.

## Research consequence

Classify the universal pointwise-sign route as dead. Future FB-04 work must instead preserve the complete integrated arithmetic structure or identify a different global invariant.

Potential surviving mechanisms include:

```text
stationarity A x0=b
whole-cell first-bad minimality
transfer to smaller-size good states
exact discrepancy/archimedean cancellation
combined-parity invariants.
```

Each remains OPEN until separately theoremized.

## Regression use

Before reviving a proposed pointwise positivity argument, run

```text
python research/RHRC/countermodels/check_post155_riesz_pointwise_sign.py
```

and test the proposed new hypothesis against both fixtures. A valid revival must name a new hypothesis that excludes these fixtures and prove that the exact retained first-bad production state satisfies that hypothesis.

**RH remains OPEN.**
